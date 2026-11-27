/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.DigitSumDirichletConvolution
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Partial sums of the second digit-sum convolution

This module proves the asymptotic formula for the partial sums of the Dirichlet
square of the base-$q$ digit-sum function: they equal
$\frac{(q-1)^2}{24 \log^2 q} \, x \log^3 x + O(x \log^2 x)$ as $x \to \infty$.
The proof goes through an elementary block decomposition for the digit-sum
partial sums, summation by parts, and integral comparisons for the sums
$\sum \log d / d$ and $\sum \log^2 d / d$.
-/

namespace MetaMathlibExt

@[expose] public section

namespace digitSumArith_sq_partialSum_isBigO

/-- The sum of the base-$q$ digits is additive when a multiple of a power of
$q$ is added to a smaller number: the low digits come from the smaller number
and the high digits from the multiple. -/
private theorem digitSum_add_pow (q b : ℕ) (hq : 1 < q) :
    ∀ k m : ℕ, m < q ^ k →
      (Nat.digits q (b * q ^ k + m)).sum = (Nat.digits q b).sum + (Nat.digits q m).sum := by
  intro k
  induction k with
  | zero =>
      intro m hm
      have hm0 : m = 0 := by simp only [pow_zero] at hm; omega
      subst hm0
      simp
  | succ k ih =>
      intro m hm
      have hq0 : 0 < q := by omega
      have hm' : m / q < q ^ k := by
        rw [Nat.div_lt_iff_lt_mul hq0]
        calc m < q ^ (k + 1) := hm
          _ = q ^ k * q := by rw [pow_succ]
      have hsum : ∀ n : ℕ, n ≠ 0 →
          (Nat.digits q n).sum = n % q + (Nat.digits q (n / q)).sum := by
        intro n hn
        rw [Nat.digits_def' hq (Nat.pos_of_ne_zero hn)]
        simp [List.sum_cons]
      by_cases h0 : b * q ^ (k + 1) + m = 0
      · obtain ⟨hb0, hm0⟩ := Nat.add_eq_zero_iff.mp h0
        have hb : b = 0 := by
          rcases Nat.mul_eq_zero.mp hb0 with h | h
          · exact h
          · omega
        simp [hb, hm0]
      · rw [hsum _ h0]
        have hmod : (b * q ^ (k + 1) + m) % q = m % q := by
          have heq : b * q ^ (k + 1) + m = m + (b * q ^ k) * q := by rw [pow_succ']; ring
          rw [heq, Nat.add_mul_mod_self_right]
        have hdiv : (b * q ^ (k + 1) + m) / q = b * q ^ k + m / q := by
          have heq : b * q ^ (k + 1) + m = m + q * (b * q ^ k) := by rw [pow_succ']; ring
          rw [heq, Nat.add_mul_div_left _ _ hq0, add_comm]
        rw [hmod, hdiv, ih (m / q) hm']
        by_cases hm0 : m = 0
        · simp [hm0]
        · rw [hsum m hm0]
          omega

/-- A number below the base has a one-digit expansion, so its digit sum is
itself. -/
private theorem digitSum_lt_base (q b : ℕ) (hb : b < q) :
    ((Nat.digits q b).sum : ℝ) = b := by
  rcases eq_or_ne b 0 with rfl | hb0
  · simp
  · have h : Nat.digits q b = [b] := Nat.digits_of_lt q b hb0 hb
    rw [h]
    simp

/-- The partial sum of the base-$q$ digit sums over the integers below $N$. -/
private noncomputable def partialSum (q N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, ((Nat.digits q n).sum : ℝ)

/-- Block decomposition of the digit-sum partial sums. Writing $N = aM + r$
with $M = q^k$, the sum over $[0, N)$ splits into $a$ full blocks of length
$M$ and one partial block. -/
private theorem partialSum_block (q : ℕ) (hq : 2 ≤ q) (k N : ℕ)
    (hlo : q ^ k ≤ N) (hhi : N < q * q ^ k) :
    partialSum q N =
      ((N / q ^ k : ℕ) : ℝ) * partialSum q (q ^ k) +
        (q ^ k : ℝ) * ((N / q ^ k : ℕ) : ℝ) * (((N / q ^ k : ℕ) : ℝ) - 1) / 2 +
        ((N % q ^ k : ℕ) : ℝ) * ((N / q ^ k : ℕ) : ℝ) +
        partialSum q (N % q ^ k) := by
  classical
  set M := q ^ k with hM
  have hq1 : 1 < q := by omega
  have hMpos : 0 < M := by positivity
  have ha : N / M < q := by
    rw [Nat.div_lt_iff_lt_mul hMpos]
    calc N < q * q ^ k := hhi
      _ = q * M := rfl
  set a := N / M with ha_def
  set r := N % M with hr_def
  have hNM : N = M * a + r := (Nat.div_add_mod N M).symm
  have hdouble : ∀ a : ℕ,
      ∑ n ∈ Finset.range (a * M), ((Nat.digits q n).sum : ℝ) =
        ∑ b ∈ Finset.range a, ∑ m ∈ Finset.range M, ((Nat.digits q (b * M + m)).sum : ℝ) := by
    intro a
    induction a with
    | zero => simp
    | succ a ih =>
        have h1 : (a + 1) * M = a * M + M := by ring
        rw [h1, Finset.sum_range_add, ih, Finset.sum_range_succ]
  have hinner : ∀ b : ℕ, b < q →
      ∑ m ∈ Finset.range M, ((Nat.digits q (b * M + m)).sum : ℝ) =
        (M : ℝ) * b + partialSum q M := by
    intro b hb
    have hstep : ∑ m ∈ Finset.range M, ((Nat.digits q (b * M + m)).sum : ℝ) =
        ∑ m ∈ Finset.range M, ((b : ℝ) + ((Nat.digits q m).sum : ℝ)) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmM : m < M := Finset.mem_range.mp hm
      have hm' : m < q ^ k := by rwa [hM] at hmM
      have h := digitSum_add_pow q b hq1 k m hm'
      rw [← hM] at h
      rw [h, Nat.cast_add, digitSum_lt_base q b hb]
    rw [hstep, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    rfl
  have hpart : ∑ m ∈ Finset.range r, ((Nat.digits q (M * a + m)).sum : ℝ) =
      ((r : ℕ) : ℝ) * ((a : ℕ) : ℝ) + partialSum q r := by
    have hstep : ∑ m ∈ Finset.range r, ((Nat.digits q (M * a + m)).sum : ℝ) =
        ∑ m ∈ Finset.range r, (((a : ℕ) : ℝ) + ((Nat.digits q m).sum : ℝ)) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmM : m < r := Finset.mem_range.mp hm
      have hm' : m < M := lt_of_lt_of_le hmM (Nat.mod_lt _ hMpos).le
      have hm'' : m < q ^ k := by rwa [hM] at hm'
      have h := digitSum_add_pow q a hq1 k m hm''
      rw [← hM] at h
      rw [mul_comm M a, h, Nat.cast_add, digitSum_lt_base q a ha]
    rw [hstep, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    rfl
  have hsumid : ∑ b ∈ Finset.range a, (b : ℝ) =
      ((a : ℕ) : ℝ) * (((a : ℕ) : ℝ) - 1) / 2 := by
    have hmul := Finset.sum_range_id_mul_two a
    have hcast : ((∑ i ∈ Finset.range a, i : ℕ) : ℝ) * 2 =
        ((a : ℕ) : ℝ) * (((a : ℕ) : ℝ) - 1) := by
      have h2 : ((∑ i ∈ Finset.range a, i : ℕ) : ℝ) * 2 =
          ((∑ i ∈ Finset.range a, i) * 2 : ℕ) := by push_cast; ring
      have ha1 : 1 ≤ a := by rw [ha_def]; exact Nat.div_pos hlo hMpos
      have hsub : ((a - 1 : ℕ) : ℝ) = ((a : ℕ) : ℝ) - 1 := by
        rw [Nat.cast_sub ha1]
        simp
      rw [h2, hmul, Nat.cast_mul, hsub]
    have hsumcast : ∑ b ∈ Finset.range a, (b : ℝ) =
        ((∑ i ∈ Finset.range a, i : ℕ) : ℝ) := by
      rw [Nat.cast_sum]
    rw [hsumcast]
    linarith
  have hblocks : ∑ b ∈ Finset.range a,
      ∑ m ∈ Finset.range M, ((Nat.digits q (b * M + m)).sum : ℝ) =
        ((a : ℕ) : ℝ) * partialSum q M +
          (M : ℝ) * (((a : ℕ) : ℝ) * (((a : ℕ) : ℝ) - 1) / 2) := by
    rw [Finset.sum_congr rfl (fun b hb => hinner b (lt_of_lt_of_le (Finset.mem_range.mp hb)
      (le_of_lt ha)))]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsumid, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    ring
  unfold partialSum
  rw [hNM, Finset.sum_range_add]
  have hfirst : ∑ n ∈ Finset.range (M * a), ((Nat.digits q n).sum : ℝ) =
      ∑ b ∈ Finset.range a, ∑ m ∈ Finset.range M, ((Nat.digits q (b * M + m)).sum : ℝ) := by
    rw [mul_comm M a]
    exact hdouble a
  rw [hfirst, hblocks, hpart]
  unfold partialSum
  have hMcast : (M : ℝ) = (q : ℝ) ^ k := by rw [hM, Nat.cast_pow]
  rw [hMcast]
  ring

/-- The exact value of the digit-sum partial sum over a full block of length
$q^k$: it is $\frac{q-1}{2} k q^k$. -/
private theorem partialSum_pow (q : ℕ) (hq : 2 ≤ q) (k : ℕ) :
    partialSum q (q ^ k) = ((q : ℝ) - 1) / 2 * k * (q : ℝ) ^ k := by
  have hq1 : 1 < q := by omega
  have hchoose : ((q.choose 2 : ℕ) : ℝ) = (q : ℝ) * ((q : ℝ) - 1) / 2 := by
    have hdvd : 2 ∣ q * (q - 1) := by
      obtain ⟨m, hm⟩ := show ∃ m, q = m + 1 from ⟨q - 1, by omega⟩
      rw [hm]
      have heq : (m + 1) * (m + 1 - 1) = m * (m + 1) := by
        rw [Nat.add_sub_cancel]
        ring
      rw [heq]
      exact (Nat.even_mul_succ_self m).two_dvd
    rw [Nat.choose_two_right, Nat.cast_div hdvd (by norm_num)]
    push_cast
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    ring
  have hcast : ((k * q ^ (k - 1) * q.choose 2 : ℕ) : ℝ) =
      (k : ℝ) * (q : ℝ) ^ (k - 1) * ((q : ℝ) * ((q : ℝ) - 1) / 2) := by
    simp only [Nat.cast_mul, Nat.cast_pow, hchoose]
  unfold partialSum
  rw [← Nat.cast_sum, Nat.sum_sum_digits_eq hq1, hcast]
  cases k with
  | zero => simp
  | succ k =>
      simp only [Nat.succ_sub_one, Nat.cast_succ]
      rw [pow_succ]
      ring

/-- The digit-sum partial sums satisfy the main term
$\frac{q-1}{2 \log q} N \log N$ with an error of order $N$, proved by strong
induction using the block decomposition and the exact value over full blocks. -/
private theorem partialSum_bound (q : ℕ) (hq : 2 ≤ q) :
    ∀ N : ℕ, 1 ≤ N →
      |partialSum q N - ((q : ℝ) - 1) / (2 * Real.log q) * N * Real.log N| ≤
        4 * (q : ℝ) ^ 2 * N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
    intro hN
    have hq1 : 1 < q := by omega
    have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
    have hq0R : (0 : ℝ) < q := by linarith
    have hlogqpos : 0 < Real.log q := Real.log_pos (by linarith)
    have hlogq2 : (1 : ℝ) / 2 ≤ Real.log q := by
      have h1 : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) (by linarith)
      linarith [Real.log_two_gt_d9]
    set A : ℝ := ((q : ℝ) - 1) / (2 * Real.log q) with hAdef
    have hA_nonneg : 0 ≤ A := by
      rw [hAdef]
      exact div_nonneg (by linarith) (by linarith [hlogqpos])
    have hA_le : A ≤ (q : ℝ) - 1 := by
      rw [hAdef, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.log q)]
      nlinarith [hlogq2, hqR]
    have hAlogq : A * Real.log q = ((q : ℝ) - 1) / 2 := by
      rw [hAdef]
      field_simp
    rcases eq_or_lt_of_le hN with hN1 | hN2
    · subst hN1
      simp [partialSum]
    · have hNpos : 0 < N := by omega
      set k := Nat.log q N with hkdef
      set M := q ^ k with hMdef
      have hMpos : 0 < M := by positivity
      have hMle : M ≤ N := Nat.pow_log_le_self q (by omega : N ≠ 0)
      have hNlt : N < q * M := by
        have h := Nat.lt_pow_succ_log_self hq1 N
        rw [pow_succ, mul_comm (q ^ k) q] at h
        exact h
      set a := N / M with hadef
      set r := N % M with hrdef
      have ha_lt : a < q := by
        rw [hadef, Nat.div_lt_iff_lt_mul hMpos]
        calc N < q * M := hNlt
          _ = q * M := rfl
      have ha1 : 1 ≤ a := by rw [hadef]; exact Nat.div_pos hMle hMpos
      have hr_lt : r < M := by rw [hrdef]; exact Nat.mod_lt _ hMpos
      have hNM : N = M * a + r := (Nat.div_add_mod N M).symm
      have hrN : r < N := by
        have h1 : M ≤ M * a := Nat.le_mul_of_pos_right M ha1
        omega
      have h2r : 2 * r < N := by
        have hlt : r * a < M * a := Nat.mul_lt_mul_of_pos_right hr_lt (by omega : 0 < a)
        have hle : r ≤ r * a := by
          calc r = r * 1 := (mul_one r).symm
            _ ≤ r * a := Nat.mul_le_mul_left r ha1
        omega
      have hMcast : (M : ℝ) = (q : ℝ) ^ k := by rw [hMdef, Nat.cast_pow]
      have hlogM : Real.log M = (k : ℝ) * Real.log q := by
        rw [hMcast, Real.log_pow]
      have hSM : partialSum q M = A * M * Real.log M := by
        rw [partialSum_pow q hq k, hlogM, hMcast]
        rw [hAdef]
        field_simp
      have hL1_nonneg : 0 ≤ Real.log N - (k : ℝ) * Real.log q := by
        have h := Real.log_le_log (by positivity : (0 : ℝ) < M)
          (by exact_mod_cast hMle : (M : ℝ) ≤ N)
        rw [hlogM] at h
        linarith
      have hL1_le : Real.log N - (k : ℝ) * Real.log q ≤ Real.log q := by
        have hlt : Real.log N < Real.log (q * M) := by
          apply Real.log_lt_log (by positivity : (0 : ℝ) < N)
          exact_mod_cast hNlt
        have hmul : Real.log ((q : ℝ) * M) = Real.log q + Real.log M := by
          rw [Real.log_mul (by positivity : (q : ℝ) ≠ 0) (by positivity : (M : ℝ) ≠ 0)]
        rw [hmul, hlogM] at hlt
        linarith
      have hEr : |partialSum q r - A * r * Real.log r| ≤ 4 * (q : ℝ) ^ 2 * r := by
        rcases eq_or_ne r 0 with hr0 | hr0
        · simp [hr0, partialSum]
        · exact IH r hrN (by omega)
      have hT5 : |A * (r : ℝ) * (Real.log N - Real.log r)| ≤ A * (N : ℝ) := by
        rcases eq_or_ne r 0 with hr0 | hr0
        · rw [hr0]
          simp only [Nat.cast_zero, mul_zero, zero_mul, abs_zero]
          exact mul_nonneg hA_nonneg (by positivity)
        · have hrpos : (0 : ℝ) < r := by exact_mod_cast (Nat.pos_of_ne_zero hr0)
          have hlogdiff : Real.log N - Real.log r = Real.log ((N : ℝ) / r) := by
            rw [Real.log_div (by positivity : (N : ℝ) ≠ 0) (by positivity : (r : ℝ) ≠ 0)]
          have hge : (1 : ℝ) ≤ (N : ℝ) / r := by
            rw [le_div_iff₀ hrpos]
            simp only [one_mul]
            exact_mod_cast (le_of_lt hrN)
          have hΔ : 0 ≤ Real.log N - Real.log r := by
            rw [hlogdiff]
            exact Real.log_nonneg hge
          have hle1 : (r : ℝ) * (Real.log N - Real.log r) ≤ (N : ℝ) := by
            rw [hlogdiff]
            have h1 : Real.log ((N : ℝ) / r) ≤ (N : ℝ) / r :=
              Real.log_le_self (by positivity)
            have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hrpos)
            rwa [mul_div_cancel₀ _ (ne_of_gt hrpos)] at h2
          rw [abs_of_nonneg (mul_nonneg (mul_nonneg hA_nonneg (Nat.cast_nonneg r)) hΔ)]
          calc A * (r : ℝ) * (Real.log N - Real.log r)
              = A * ((r : ℝ) * (Real.log N - Real.log r)) := by ring
            _ ≤ A * (N : ℝ) := mul_le_mul_of_nonneg_left hle1 hA_nonneg
      have hId : partialSum q N - A * (N : ℝ) * Real.log N =
          -(A * (a : ℝ) * (M : ℝ) * (Real.log N - (k : ℝ) * Real.log q)) +
            (M : ℝ) * (a : ℝ) * ((a : ℝ) - 1) / 2 + (a : ℝ) * (r : ℝ) +
            (partialSum q r - A * (r : ℝ) * Real.log r) +
            -(A * (r : ℝ) * (Real.log N - Real.log r)) := by
        have hNcast : (N : ℝ) = (M : ℝ) * (a : ℝ) + (r : ℝ) := by
          have h := hNM
          exact_mod_cast h
        rw [partialSum_block q hq k N hMle hNlt, ← hMdef, ← hadef, ← hrdef,
          hSM, hlogM, hNcast, hMcast]
        ring
      have hT1 : |-(A * (a : ℝ) * (M : ℝ) * (Real.log N - (k : ℝ) * Real.log q))| ≤
          ((q : ℝ) - 1) / 2 * (N : ℝ) := by
        rw [abs_neg]
        have h1 : A * (Real.log N - (k : ℝ) * Real.log q) ≤ ((q : ℝ) - 1) / 2 := by
          have h2 : A * (Real.log N - (k : ℝ) * Real.log q) ≤ A * Real.log q :=
            mul_le_mul_of_nonneg_left hL1_le hA_nonneg
          rwa [hAlogq] at h2
        have h1' : 0 ≤ A * (Real.log N - (k : ℝ) * Real.log q) :=
          mul_nonneg hA_nonneg hL1_nonneg
        have h3 : (a : ℝ) * (M : ℝ) ≤ (N : ℝ) := by
          have h := hNM
          have h' : (N : ℝ) = (M : ℝ) * (a : ℝ) + (r : ℝ) := by exact_mod_cast h
          nlinarith [h', (by positivity : (0 : ℝ) ≤ (r : ℝ))]
        calc |A * (a : ℝ) * (M : ℝ) * (Real.log N - (k : ℝ) * Real.log q)|
            = ((a : ℝ) * (M : ℝ)) * (A * (Real.log N - (k : ℝ) * Real.log q)) := by
              rw [abs_of_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hA_nonneg
                (Nat.cast_nonneg a)) (Nat.cast_nonneg M)) hL1_nonneg)]
              ring
          _ ≤ (N : ℝ) * (((q : ℝ) - 1) / 2) :=
              mul_le_mul h3 h1 h1' (Nat.cast_nonneg N)
          _ = ((q : ℝ) - 1) / 2 * (N : ℝ) := by ring
      have hT2 : |(M : ℝ) * (a : ℝ) * ((a : ℝ) - 1) / 2| ≤ (q : ℝ) ^ 2 / 2 * (N : ℝ) := by
        have ha1R : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
        rw [abs_of_nonneg (div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg M)
          (Nat.cast_nonneg a)) (by linarith)) (by norm_num))]
        have haR : (a : ℝ) ≤ q := by exact_mod_cast (le_of_lt ha_lt)
        have h1 : (M : ℝ) * (a : ℝ) * ((a : ℝ) - 1) ≤ (N : ℝ) * (q : ℝ) * (q : ℝ) := by
          have hMleR : (M : ℝ) ≤ N := by exact_mod_cast hMle
          have h2 : (M : ℝ) * (a : ℝ) * ((a : ℝ) - 1) ≤
              (N : ℝ) * (q : ℝ) * ((q : ℝ) - 1) := by
            apply mul_le_mul _ (by linarith : (a : ℝ) - 1 ≤ (q : ℝ) - 1)
              (by linarith) (by positivity)
            apply mul_le_mul hMleR haR (by positivity) (by positivity)
          nlinarith [h2, hqR]
        nlinarith [h1, hq0R]
      have hT3 : |(a : ℝ) * (r : ℝ)| ≤ (q : ℝ) / 2 * (N : ℝ) := by
        rw [abs_of_nonneg (by positivity)]
        have haR : (a : ℝ) ≤ q := by exact_mod_cast (le_of_lt ha_lt)
        have hrR : (r : ℝ) ≤ (N : ℝ) / 2 := by
          have h : (2 * r : ℕ) < N := h2r
          have h' : ((2 * r : ℕ) : ℝ) < (N : ℝ) := by exact_mod_cast h
          push_cast at h'
          linarith
        calc (a : ℝ) * (r : ℝ) ≤ (q : ℝ) * ((N : ℝ) / 2) :=
              mul_le_mul haR hrR (by positivity) (by positivity)
          _ = (q : ℝ) / 2 * (N : ℝ) := by ring
      have hT4 : |partialSum q r - A * (r : ℝ) * Real.log r| ≤
          (4 * (q : ℝ) ^ 2 / 2) * (N : ℝ) := by
        have hrR : (r : ℝ) ≤ (N : ℝ) / 2 := by
          have h : (2 * r : ℕ) < N := h2r
          have h' : ((2 * r : ℕ) : ℝ) < (N : ℝ) := by exact_mod_cast h
          push_cast at h'
          linarith
        calc |partialSum q r - A * (r : ℝ) * Real.log r|
            ≤ 4 * (q : ℝ) ^ 2 * (r : ℝ) := hEr
          _ ≤ 4 * (q : ℝ) ^ 2 * ((N : ℝ) / 2) :=
              mul_le_mul_of_nonneg_left hrR (by positivity)
          _ = (4 * (q : ℝ) ^ 2 / 2) * (N : ℝ) := by ring
      have hT5' : |-(A * (r : ℝ) * (Real.log N - Real.log r))| ≤
          ((q : ℝ) - 1) * (N : ℝ) := by
        rw [abs_neg]
        exact (hT5.trans (mul_le_mul_of_nonneg_right hA_le (by positivity)))
      set T1 : ℝ := -(A * (a : ℝ) * (M : ℝ) * (Real.log N - (k : ℝ) * Real.log q)) with hT1d
      set T2 : ℝ := (M : ℝ) * (a : ℝ) * ((a : ℝ) - 1) / 2 with hT2d
      set T3 : ℝ := (a : ℝ) * (r : ℝ) with hT3d
      set T4 : ℝ := partialSum q r - A * (r : ℝ) * Real.log r with hT4d
      set T5 : ℝ := -(A * (r : ℝ) * (Real.log N - Real.log r)) with hT5d
      have hcoeff : ((q : ℝ) - 1) / 2 + (q : ℝ) ^ 2 / 2 + (q : ℝ) / 2 +
          (4 * (q : ℝ) ^ 2 / 2) + ((q : ℝ) - 1) ≤ 4 * (q : ℝ) ^ 2 := by
        have hsq := sq_nonneg ((q : ℝ) - 2)
        nlinarith only [hqR, hsq]
      have hsum : ((q : ℝ) - 1) / 2 * (N : ℝ) + (q : ℝ) ^ 2 / 2 * (N : ℝ) +
          (q : ℝ) / 2 * (N : ℝ) + (4 * (q : ℝ) ^ 2 / 2) * (N : ℝ) +
          ((q : ℝ) - 1) * (N : ℝ) =
          (((q : ℝ) - 1) / 2 + (q : ℝ) ^ 2 / 2 + (q : ℝ) / 2 +
            (4 * (q : ℝ) ^ 2 / 2) + ((q : ℝ) - 1)) * (N : ℝ) := by ring
      refine abs_le.mpr ⟨?_, ?_⟩
      · have h1 : -(4 * (q : ℝ) ^ 2 * (N : ℝ)) ≤
            -(((q : ℝ) - 1) / 2 * (N : ℝ) + (q : ℝ) ^ 2 / 2 * (N : ℝ) +
              (q : ℝ) / 2 * (N : ℝ) + (4 * (q : ℝ) ^ 2 / 2) * (N : ℝ) +
              ((q : ℝ) - 1) * (N : ℝ)) := by
          rw [hsum]
          have hNn : (0 : ℝ) ≤ N := by positivity
          exact neg_le_neg (mul_le_mul_of_nonneg_right hcoeff hNn)
        have h2 : -(((q : ℝ) - 1) / 2 * (N : ℝ) + (q : ℝ) ^ 2 / 2 * (N : ℝ) +
              (q : ℝ) / 2 * (N : ℝ) + (4 * (q : ℝ) ^ 2 / 2) * (N : ℝ) +
              ((q : ℝ) - 1) * (N : ℝ)) ≤
            partialSum q N - A * (N : ℝ) * Real.log N := by
          have b1 := abs_le.mp hT1
          have b2 := abs_le.mp hT2
          have b3 := abs_le.mp hT3
          have b4 := abs_le.mp hT4
          have b5 := abs_le.mp hT5'
          linarith [hId, b1.1, b2.1, b3.1, b4.1, b5.1]
        exact h1.trans h2
      · have h1 : partialSum q N - A * (N : ℝ) * Real.log N ≤
            ((q : ℝ) - 1) / 2 * (N : ℝ) + (q : ℝ) ^ 2 / 2 * (N : ℝ) +
              (q : ℝ) / 2 * (N : ℝ) + (4 * (q : ℝ) ^ 2 / 2) * (N : ℝ) +
              ((q : ℝ) - 1) * (N : ℝ) := by
          have b1 := abs_le.mp hT1
          have b2 := abs_le.mp hT2
          have b3 := abs_le.mp hT3
          have b4 := abs_le.mp hT4
          have b5 := abs_le.mp hT5'
          linarith [hId, b1.2, b2.2, b3.2, b4.2, b5.2]
        have h2 : ((q : ℝ) - 1) / 2 * (N : ℝ) + (q : ℝ) ^ 2 / 2 * (N : ℝ) +
              (q : ℝ) / 2 * (N : ℝ) + (4 * (q : ℝ) ^ 2 / 2) * (N : ℝ) +
              ((q : ℝ) - 1) * (N : ℝ) ≤ 4 * (q : ℝ) ^ 2 * (N : ℝ) := by
          rw [hsum]
          exact mul_le_mul_of_nonneg_right hcoeff (by positivity)
        exact h1.trans h2

/-- The derivative of $\log t / t$ is $(1 - \log t) / t^2$. -/
private theorem logDiv_hasDerivAt (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => Real.log s / s) ((1 - Real.log t) / t ^ 2) t := by
  have h := (Real.hasDerivAt_log (ne_of_gt ht)).div (hasDerivAt_id t) (ne_of_gt ht)
  have hfun : (Real.log / id) = fun s : ℝ => Real.log s / s := by
    funext s
    simp
  rw [hfun] at h
  convert h using 1
  simp only [id_eq]
  field_simp

/-- The derivative of $\log^2 t / t$ is $(2 \log t - \log^2 t) / t^2$. -/
private theorem logSqDiv_hasDerivAt (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => Real.log s ^ 2 / s)
      ((2 * Real.log t - Real.log t ^ 2) / t ^ 2) t := by
  have h := ((Real.hasDerivAt_log (ne_of_gt ht)).pow 2).div (hasDerivAt_id t)
    (ne_of_gt ht)
  have hfun : (Real.log ^ 2 / id) = fun s : ℝ => Real.log s ^ 2 / s := by
    funext s
    simp [Pi.pow_def]
  rw [hfun] at h
  convert h using 1
  simp only [id_eq]
  field_simp
  ring_nf
  simp only [Pi.pow_def]

/-- $\log t / t$ is antitone on $[8, \infty)$. -/
private theorem logDiv_antitone : AntitoneOn (fun t : ℝ => Real.log t / t) (Set.Ici 8) := by
  have hlog8 : (2 : ℝ) < Real.log 8 := by
    have h1 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    rw [h1]
    linarith [Real.log_two_gt_d9]
  have hcont : ContinuousOn (fun t : ℝ => Real.log t / t) (Set.Ici 8) := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have hx8 : (8 : ℝ) ≤ x := hx
    exact ((logDiv_hasDerivAt x (by linarith)).differentiableAt).continuousAt
  refine antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := fun t : ℝ => (1 - Real.log t) / t ^ 2) (convex_Ici 8) hcont ?_ ?_
  · intro x hx
    rw [interior_Ici] at hx
    have hx8 : (8 : ℝ) < x := hx
    exact (logDiv_hasDerivAt x (by linarith)).hasDerivWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx8 : (8 : ℝ) < x := hx
    have hlogx : (1 : ℝ) ≤ Real.log x := by
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 8) (le_of_lt hx8)
      linarith [hlog8]
    have hpos : (0 : ℝ) < x ^ 2 := by positivity
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hpos)

/-- $\log^2 t / t$ is antitone on $[8, \infty)$. -/
private theorem logSqDiv_antitone :
    AntitoneOn (fun t : ℝ => Real.log t ^ 2 / t) (Set.Ici 8) := by
  have hlog8 : (2 : ℝ) < Real.log 8 := by
    have h1 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    rw [h1]
    linarith [Real.log_two_gt_d9]
  have hcont : ContinuousOn (fun t : ℝ => Real.log t ^ 2 / t) (Set.Ici 8) := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have hx8 : (8 : ℝ) ≤ x := hx
    exact ((logSqDiv_hasDerivAt x (by linarith)).differentiableAt).continuousAt
  refine antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := fun t : ℝ => (2 * Real.log t - Real.log t ^ 2) / t ^ 2) (convex_Ici 8) hcont ?_ ?_
  · intro x hx
    rw [interior_Ici] at hx
    have hx8 : (8 : ℝ) < x := hx
    exact (logSqDiv_hasDerivAt x (by linarith)).hasDerivWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx8 : (8 : ℝ) < x := hx
    have hlogx : (2 : ℝ) ≤ Real.log x := by
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 8) (le_of_lt hx8)
      linarith [hlog8]
    have hpos : (0 : ℝ) < x ^ 2 := by positivity
    apply div_nonpos_of_nonpos_of_nonneg _ (le_of_lt hpos)
    nlinarith [hlogx, Real.log_nonneg (by linarith : (1 : ℝ) ≤ x)]

/-- Integral comparison for an antitone function with an antiderivative:
the sum over $[1, N]$ of $f$ differs from $F(N)$ by a constant plus $\log N$,
where $F' = f$. -/
private theorem sum_bound_aux {f F : ℝ → ℝ} (hanti : AntitoneOn f (Set.Ici 8))
    (hFderiv : ∀ t : ℝ, 0 < t → HasDerivAt F (f t) t)
    (hFcont : ContinuousOn F (Set.Ioi 0))
    (hfnonneg : ∀ t : ℝ, 8 ≤ t → 0 ≤ f t)
    (hf8 : f 8 ≤ 1)
    (hhead : ∀ (d : ℕ), d ∈ Finset.Icc (1 : ℕ) 7 → 0 ≤ f (d : ℝ) ∧ f (d : ℝ) ≤ 2.1)
    (hfN : ∀ N : ℕ, 8 ≤ N → f (N : ℝ) ≤ Real.log N) :
    ∀ N : ℕ, 8 ≤ N →
      |∑ d ∈ Finset.Icc 1 N, f (d : ℝ) - F (N : ℝ)| ≤
        16 + |F 8| + Real.log N := by
  intro N hN
  have haR : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hantiIcc : AntitoneOn f (Set.Icc (8 : ℝ) ((N : ℝ) + 1)) := by
    apply hanti.mono
    intro x hx
    simp only [Set.mem_Icc] at hx
    simp only [Set.mem_Ici]
    linarith [hx.1]
  have hfint : ∀ a b : ℝ, 8 ≤ a → a ≤ b →
      IntervalIntegrable f MeasureTheory.volume a b := by
    intro a b ha hab
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    have hsub : Set.Icc a b ⊆ Set.Ici 8 := by
      intro x hx
      simp only [Set.mem_Icc] at hx
      simp only [Set.mem_Ici]
      linarith [hx.1, ha]
    exact ((hanti.mono hsub).integrableOn_isCompact isCompact_Icc).mono_set
      Set.Ioc_subset_Icc_self
  have hFTC : ∀ a b : ℝ, 8 ≤ a → a ≤ b → ∫ t in a..b, f t = F b - F a := by
    intro a b ha hab
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    · apply hFcont.mono
      intro x hx
      simp only [Set.mem_Icc] at hx
      simp only [Set.mem_Ioi]
      linarith [hx.1, ha]
    · intro x hx
      simp only [Set.mem_Ioo] at hx
      exact hFderiv x (by linarith [hx.1, ha])
    · exact hfint a b ha hab
  have hmid : ∑ d ∈ Finset.Icc 8 N, f (d : ℝ) =
      ∑ i ∈ Finset.range (N - 7), f ((8 : ℝ) + (i : ℝ)) := by
    rw [← Finset.Ico_add_one_right_eq_Icc 8 N, Finset.sum_Ico_eq_sum_range]
    have hNM : N + 1 - 8 = N - 7 := by omega
    rw [hNM]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    push_cast
    ring
  have hshift : ∑ i ∈ Finset.range (N - 7), f ((8 : ℝ) + ((i + 1 : ℕ) : ℝ)) =
      ∑ i ∈ Finset.range (N - 7), f ((8 : ℝ) + (i : ℝ)) - f 8 + f ((N : ℝ) + 1) := by
    have h1 : ∀ g : ℕ → ℝ, ∀ M : ℕ,
        ∑ i ∈ Finset.range M, g (i + 1) = ∑ i ∈ Finset.range M, g i - g 0 + g M := by
      intro g M
      have hA := Finset.sum_range_succ' g M
      have hB := Finset.sum_range_succ g M
      linarith
    have h2 := h1 (fun i => f ((8 : ℝ) + (i : ℝ))) (N - 7)
    have h3 : f ((8 : ℝ) + ((N - 7 : ℕ) : ℝ)) = f ((N : ℝ) + 1) := by
      have hN7 : ((N - 7 : ℕ) : ℝ) = (N : ℝ) - 7 := by
        rw [Nat.cast_sub (by omega : 7 ≤ N)]
        norm_num
      simp only [hN7]
      congr 1
      ring
    have h4 : f ((8 : ℝ) + ((0 : ℕ) : ℝ)) = f 8 := by simp
    rw [h2, h4, h3]
  have hcast0 : (8 : ℝ) + ((N - 7 : ℕ) : ℝ) = (N : ℝ) + 1 := by
    rw [Nat.cast_sub (by omega : 7 ≤ N)]
    push_cast
    ring
  have hantiIcc' : AntitoneOn f (Set.Icc (8 : ℝ) ((8 : ℝ) + ((N - 7 : ℕ) : ℝ))) := by
    rw [hcast0]
    exact hantiIcc
  have hle1 : ∫ x in (8 : ℝ)..((N : ℝ) + 1), f x ≤ ∑ d ∈ Finset.Icc 8 N, f (d : ℝ) := by
    have h := AntitoneOn.integral_le_sum (f := f) (x₀ := (8 : ℝ)) (a := N - 7) hantiIcc'
    rw [hcast0] at h
    rw [hmid]
    exact h
  have hle2 : ∑ d ∈ Finset.Icc 8 N, f (d : ℝ) - f 8 + f ((N : ℝ) + 1) ≤
      ∫ x in (8 : ℝ)..((N : ℝ) + 1), f x := by
    have h := AntitoneOn.sum_le_integral (f := f) (x₀ := (8 : ℝ)) (a := N - 7) hantiIcc'
    rw [hcast0] at h
    rw [hshift, ← hmid] at h
    exact h
  have hI : ∫ x in (8 : ℝ)..((N : ℝ) + 1), f x = F ((N : ℝ) + 1) - F 8 :=
    hFTC 8 ((N : ℝ) + 1) (le_refl 8) (by linarith)
  have hmidI : |∑ d ∈ Finset.Icc 8 N, f (d : ℝ) - ∫ x in (8 : ℝ)..((N : ℝ) + 1), f x| ≤ 1 := by
    rw [abs_le]
    constructor
    · linarith [hle1]
    · have hnn : 0 ≤ f ((N : ℝ) + 1) := hfnonneg _ (by linarith)
      linarith [hle2, hf8, hnn]
  have hFdiff : |F ((N : ℝ) + 1) - F (N : ℝ)| ≤ Real.log N := by
    have hI2 : ∫ x in (N : ℝ)..((N : ℝ) + 1), f x = F ((N : ℝ) + 1) - F (N : ℝ) :=
      hFTC (N : ℝ) ((N : ℝ) + 1) (by linarith) (by linarith)
    have hnonnegI : 0 ≤ ∫ x in (N : ℝ)..((N : ℝ) + 1), f x :=
      intervalIntegral.integral_nonneg (by linarith)
        (fun u hu => hfnonneg u (by simp only [Set.mem_Icc] at hu; linarith [hu.1, haR]))
    have hleI : ∫ x in (N : ℝ)..((N : ℝ) + 1), f x ≤ f (N : ℝ) := by
      have hantiN : AntitoneOn f (Set.Icc (N : ℝ) ((N : ℝ) + ((1 : ℕ) : ℝ))) := by
        apply hanti.mono
        intro x hx
        simp only [Set.mem_Icc] at hx
        simp only [Set.mem_Ici]
        linarith [hx.1, haR]
      have h := AntitoneOn.integral_le_sum (f := f) (x₀ := (N : ℝ)) (a := 1) hantiN
      simpa using h
    rw [← hI2]
    rw [abs_le]
    constructor <;> linarith [hnonnegI, hleI, hfN N hN]
  have hsplit : ∑ d ∈ Finset.Icc 1 N, f (d : ℝ) =
      ∑ d ∈ Finset.Icc (1 : ℕ) 7, f (d : ℝ) + ∑ d ∈ Finset.Icc 8 N, f (d : ℝ) := by
    rw [← Finset.Ico_add_one_right_eq_Icc (1 : ℕ) N,
      ← Finset.Ico_add_one_right_eq_Icc (1 : ℕ) (7 : ℕ),
      ← Finset.Ico_add_one_right_eq_Icc (8 : ℕ) N]
    rw [show ((7 : ℕ) + 1) = 8 by norm_num]
    exact (Finset.sum_Ico_consecutive (fun d => f (d : ℝ)) (by norm_num) (by omega)).symm
  have hheadbound : |∑ d ∈ Finset.Icc (1 : ℕ) 7, f (d : ℝ)| ≤ 15 := by
    rw [abs_le]
    constructor
    · have h0 : 0 ≤ ∑ d ∈ Finset.Icc (1 : ℕ) 7, f (d : ℝ) :=
        Finset.sum_nonneg (fun d hd => (hhead d hd).1)
      linarith
    · calc ∑ d ∈ Finset.Icc (1 : ℕ) 7, f (d : ℝ)
          ≤ ∑ _d ∈ Finset.Icc (1 : ℕ) 7, (2.1 : ℝ) :=
          Finset.sum_le_sum (fun d hd => (hhead d hd).2)
        _ ≤ 15 := by rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; norm_num
  rw [hsplit]
  rw [hI] at hmidI
  have hdecomp : ∑ d ∈ Finset.Icc (1 : ℕ) 7, f (d : ℝ) + ∑ d ∈ Finset.Icc 8 N, f (d : ℝ) -
      F (N : ℝ) =
      ∑ d ∈ Finset.Icc (1 : ℕ) 7, f (d : ℝ) +
        (∑ d ∈ Finset.Icc 8 N, f (d : ℝ) - (F ((N : ℝ) + 1) - F 8)) +
        (F ((N : ℝ) + 1) - F (N : ℝ)) - F 8 := by ring
  rw [hdecomp]
  calc |∑ d ∈ Finset.Icc (1 : ℕ) 7, f (d : ℝ) +
        (∑ d ∈ Finset.Icc 8 N, f (d : ℝ) - (F ((N : ℝ) + 1) - F 8)) +
        (F ((N : ℝ) + 1) - F (N : ℝ)) - F 8|
      ≤ |∑ d ∈ Finset.Icc (1 : ℕ) 7, f (d : ℝ)| +
        |∑ d ∈ Finset.Icc 8 N, f (d : ℝ) - (F ((N : ℝ) + 1) - F 8)| +
        |F ((N : ℝ) + 1) - F (N : ℝ)| + |F 8| := by
        calc |∑ d ∈ Finset.Icc (1 : ℕ) 7, f (d : ℝ) +
              (∑ d ∈ Finset.Icc 8 N, f (d : ℝ) - (F ((N : ℝ) + 1) - F 8)) +
              (F ((N : ℝ) + 1) - F (N : ℝ)) - F 8|
            ≤ |∑ d ∈ Finset.Icc (1 : ℕ) 7, f (d : ℝ) +
              (∑ d ∈ Finset.Icc 8 N, f (d : ℝ) - (F ((N : ℝ) + 1) - F 8)) +
              (F ((N : ℝ) + 1) - F (N : ℝ))| + |-F 8| := abs_add_le _ _
          _ ≤ (|∑ d ∈ Finset.Icc (1 : ℕ) 7, f (d : ℝ) +
              (∑ d ∈ Finset.Icc 8 N, f (d : ℝ) - (F ((N : ℝ) + 1) - F 8))| +
              |F ((N : ℝ) + 1) - F (N : ℝ)|) + |F 8| := by
              rw [abs_neg]
              gcongr
              exact abs_add_le _ _
          _ ≤ ((|∑ d ∈ Finset.Icc (1 : ℕ) 7, f (d : ℝ)| +
              |∑ d ∈ Finset.Icc 8 N, f (d : ℝ) - (F ((N : ℝ) + 1) - F 8)|) +
              |F ((N : ℝ) + 1) - F (N : ℝ)|) + |F 8| := by
              gcongr
              exact abs_add_le _ _
          _ = |∑ d ∈ Finset.Icc (1 : ℕ) 7, f (d : ℝ)| +
              |∑ d ∈ Finset.Icc 8 N, f (d : ℝ) - (F ((N : ℝ) + 1) - F 8)| +
              |F ((N : ℝ) + 1) - F (N : ℝ)| + |F 8| := by ring
    _ ≤ 15 + 1 + Real.log N + |F 8| := by
        have h1 : |∑ d ∈ Finset.Icc 8 N, f (d : ℝ) - (F ((N : ℝ) + 1) - F 8)| ≤ 1 := hmidI
        linarith [hheadbound, h1, hFdiff]
    _ = 16 + |F 8| + Real.log N := by ring

/-- The derivative of $\log^2 t / 2$ is $\log t / t$. -/
private theorem logSq_hasDerivAt (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => (Real.log s) ^ 2 / 2) (Real.log t / t) t := by
  have ht' : t ≠ 0 := ne_of_gt ht
  have h := ((Real.hasDerivAt_log ht').pow 2).div_const (2 : ℝ)
  convert h using 1
  rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  field_simp
  ring

/-- The derivative of $\log^3 t / 3$ is $\log^2 t / t$. -/
private theorem logCube_hasDerivAt (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => (Real.log s) ^ 3 / 3) (Real.log t ^ 2 / t) t := by
  have ht' : t ≠ 0 := ne_of_gt ht
  have h := ((Real.hasDerivAt_log ht').pow 3).div_const (3 : ℝ)
  convert h using 1
  rw [show (3 : ℕ) - 1 = 2 from rfl]
  field_simp
  ring

/-- $2 < \log 8$, from the bound $0.6931471803 < \log 2$. -/
private theorem log_eight_gt : (2 : ℝ) < Real.log 8 := by
  have h1 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  rw [h1]
  linarith [Real.log_two_gt_d9]

/-- $\log 8 < 2.1$, from the bound $\log 2 < 0.6931471808$. -/
private theorem log_eight_lt : Real.log 8 < 2.1 := by
  have h1 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  rw [h1]
  linarith [Real.log_two_lt_d9]

/-- For $d \le 7$, $\log d \le 2.1$. -/
private theorem log_le_of_le_seven {d : ℕ} (hd : d ≤ 7) : Real.log (d : ℝ) ≤ 2.1 := by
  rcases eq_or_ne d 0 with rfl | hd0
  · rw [Nat.cast_zero, Real.log_zero]
    norm_num
  · have h1 : Real.log (d : ℝ) ≤ Real.log 8 := by
      apply Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero hd0))
      exact_mod_cast (le_trans hd (by norm_num))
    linarith [log_eight_lt]

/-- The head of the $\sum \log d / d$ sum is at most $14$. -/
private theorem logDiv_head_bound :
    ∑ d ∈ Finset.Icc (1 : ℕ) 7, Real.log (d : ℝ) / (d : ℝ) ≤ 15 := by
  calc ∑ d ∈ Finset.Icc (1 : ℕ) 7, Real.log (d : ℝ) / (d : ℝ)
      ≤ ∑ _d ∈ Finset.Icc (1 : ℕ) 7, (2.1 : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have hd7 : d ≤ 7 := (Finset.mem_Icc.mp hd).2
        have hlog : Real.log (d : ℝ) ≤ 2.1 := log_le_of_le_seven hd7
        have hle : Real.log (d : ℝ) / (d : ℝ) ≤ 1 := by
          rw [div_le_one (by exact_mod_cast (Nat.pos_of_ne_zero (by omega : d ≠ 0)))]
          exact Real.log_le_self (Nat.cast_nonneg d)
        linarith
    _ ≤ 15 := by rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; norm_num

/-- The head of the $\sum \log^2 d / d$ sum is at most $14$. -/
private theorem logSqDiv_head_bound :
    ∑ d ∈ Finset.Icc (1 : ℕ) 7, Real.log (d : ℝ) ^ 2 / (d : ℝ) ≤ 15 := by
  calc ∑ d ∈ Finset.Icc (1 : ℕ) 7, Real.log (d : ℝ) ^ 2 / (d : ℝ)
      ≤ ∑ _d ∈ Finset.Icc (1 : ℕ) 7, (2.1 : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have hd7 : d ≤ 7 := (Finset.mem_Icc.mp hd).2
        have hlog : Real.log (d : ℝ) ≤ 2.1 := log_le_of_le_seven hd7
        have hnonneg : 0 ≤ Real.log (d : ℝ) :=
          Real.log_nonneg (by exact_mod_cast hd1)
        have hle : Real.log (d : ℝ) / (d : ℝ) ≤ 1 := by
          rw [div_le_one (by exact_mod_cast (Nat.pos_of_ne_zero (by omega : d ≠ 0)))]
          exact Real.log_le_self (Nat.cast_nonneg d)
        have heq : Real.log (d : ℝ) ^ 2 / (d : ℝ) =
            Real.log (d : ℝ) * (Real.log (d : ℝ) / (d : ℝ)) := by ring
        rw [heq]
        calc Real.log (d : ℝ) * (Real.log (d : ℝ) / (d : ℝ))
            ≤ 2.1 * 1 := mul_le_mul hlog hle (div_nonneg hnonneg (Nat.cast_nonneg d)) (by norm_num)
          _ ≤ 2.1 := by norm_num
    _ ≤ 15 := by rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; norm_num

/-- $\sum_{d=1}^N \log d / d = \frac{\log^2 N}{2} + O(\log N)$. -/
private theorem logDiv_sum_bound (N : ℕ) (hN : 1 ≤ N) :
    |∑ d ∈ Finset.Icc 1 N, Real.log (d : ℝ) / (d : ℝ) - (Real.log N) ^ 2 / 2| ≤
      22 + |(Real.log 8) ^ 2 / 2| + Real.log N := by
  by_cases hN8 : 8 ≤ N
  · have hFderiv : ∀ t : ℝ, 0 < t → HasDerivAt (fun s : ℝ => (Real.log s) ^ 2 / 2)
        ((fun t : ℝ => Real.log t / t) t) t := fun t ht => logSq_hasDerivAt t ht
    have hFcont : ContinuousOn (fun s : ℝ => (Real.log s) ^ 2 / 2) (Set.Ioi 0) := by
      apply continuousOn_of_forall_continuousAt
      intro x hx
      exact ((logSq_hasDerivAt x hx).differentiableAt).continuousAt
    have hf8 : Real.log 8 / 8 ≤ 1 := by
      rw [div_le_one (by norm_num : (0 : ℝ) < 8)]
      exact Real.log_le_self (by norm_num)
    have h := sum_bound_aux logDiv_antitone hFderiv hFcont
      (fun t ht => div_nonneg (Real.log_nonneg (by linarith)) (by linarith))
      hf8
      (fun d hd => ⟨div_nonneg (Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp hd).1))
        (Nat.cast_nonneg d), by
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have hd7 : d ≤ 7 := (Finset.mem_Icc.mp hd).2
        have hle : Real.log (d : ℝ) / (d : ℝ) ≤ 1 := by
          rw [div_le_one (by exact_mod_cast (Nat.pos_of_ne_zero
            (by omega : d ≠ 0)))]
          exact Real.log_le_self (Nat.cast_nonneg d)
        linarith⟩)
      (fun M hM => by
        have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (show 1 ≤ M by omega)
        exact div_le_self (Real.log_nonneg hM1) hM1) N hN8
    refine h.trans ?_
    linarith
  · have hN7 : N ≤ 7 := by omega
    have hsum_nonneg : 0 ≤ ∑ d ∈ Finset.Icc 1 N, Real.log (d : ℝ) / (d : ℝ) :=
      Finset.sum_nonneg (fun d hd => div_nonneg
        (Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp hd).1)) (Nat.cast_nonneg d))
    have hsum_le : ∑ d ∈ Finset.Icc 1 N, Real.log (d : ℝ) / (d : ℝ) ≤ 15 := by
      calc ∑ d ∈ Finset.Icc 1 N, Real.log (d : ℝ) / (d : ℝ)
          ≤ ∑ d ∈ Finset.Icc (1 : ℕ) 7, Real.log (d : ℝ) / (d : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.Icc_subset_Icc (le_refl 1) hN7)
              (fun d hd _ => div_nonneg
                (Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp hd).1))
                (Nat.cast_nonneg d))
        _ ≤ 15 := logDiv_head_bound
    have hmain_le : (Real.log N) ^ 2 / 2 ≤ 3 := by
      have hlog : Real.log (N : ℝ) ≤ 2.1 := log_le_of_le_seven hN7
      have hnonneg : 0 ≤ Real.log (N : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hN)
      have h3 : (Real.log (N : ℝ)) ^ 2 ≤ (2.1 : ℝ) ^ 2 := pow_le_pow_left₀ hnonneg hlog 2
      linarith [h3]
    have hlognonneg : 0 ≤ Real.log (N : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hN)
    have hmain_nonneg : 0 ≤ (Real.log N) ^ 2 / 2 := by positivity
    rw [abs_le]
    constructor <;> nlinarith [hsum_nonneg, hsum_le, hmain_le, hlognonneg, hmain_nonneg,
      abs_nonneg ((Real.log 8) ^ 2 / 2 : ℝ)]

/-- $\sum_{d=1}^N \log^2 d / d = \frac{\log^3 N}{3} + O(\log N)$. -/
private theorem logSqDiv_sum_bound (N : ℕ) (hN : 1 ≤ N) :
    |∑ d ∈ Finset.Icc 1 N, Real.log (d : ℝ) ^ 2 / (d : ℝ) - (Real.log N) ^ 3 / 3| ≤
      22 + |(Real.log 8) ^ 3 / 3| + Real.log N := by
  by_cases hN8 : 8 ≤ N
  · have hFderiv : ∀ t : ℝ, 0 < t → HasDerivAt (fun s : ℝ => (Real.log s) ^ 3 / 3)
        ((fun t : ℝ => Real.log t ^ 2 / t) t) t := fun t ht => logCube_hasDerivAt t ht
    have hFcont : ContinuousOn (fun s : ℝ => (Real.log s) ^ 3 / 3) (Set.Ioi 0) := by
      apply continuousOn_of_forall_continuousAt
      intro x hx
      exact ((logCube_hasDerivAt x hx).differentiableAt).continuousAt
    have hf8 : Real.log 8 ^ 2 / 8 ≤ 1 := by
      rw [div_le_one (by norm_num : (0 : ℝ) < 8)]
      have hlog : Real.log 8 ≤ 2.1 := log_eight_lt.le
      have hnonneg : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
      nlinarith [hlog, hnonneg]
    have h := sum_bound_aux logSqDiv_antitone hFderiv hFcont
      (fun t ht => div_nonneg (sq_nonneg _) (by linarith))
      hf8
      (fun d hd => ⟨div_nonneg (sq_nonneg _) (Nat.cast_nonneg d), by
        have hd7 : d ≤ 7 := (Finset.mem_Icc.mp hd).2
        have hlog : Real.log (d : ℝ) ≤ 2.1 := log_le_of_le_seven hd7
        have hnonneg : 0 ≤ Real.log (d : ℝ) :=
          Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp hd).1)
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have hle : Real.log (d : ℝ) / (d : ℝ) ≤ 1 := by
          rw [div_le_one (by exact_mod_cast (Nat.pos_of_ne_zero
            (by omega : d ≠ 0)))]
          exact Real.log_le_self (Nat.cast_nonneg d)
        have heq : Real.log (d : ℝ) ^ 2 / (d : ℝ) =
            Real.log (d : ℝ) * (Real.log (d : ℝ) / (d : ℝ)) := by ring
        rw [heq]
        calc Real.log (d : ℝ) * (Real.log (d : ℝ) / (d : ℝ))
            ≤ 2.1 * 1 := mul_le_mul hlog hle (div_nonneg hnonneg (Nat.cast_nonneg d)) (by norm_num)
          _ ≤ 2.1 := by norm_num⟩)
      (fun M hM => by
        have hnonneg : 0 ≤ Real.log (M : ℝ) :=
          Real.log_nonneg (by exact_mod_cast (show 1 ≤ M by omega))
        have hle : Real.log (M : ℝ) / (M : ℝ) ≤ 1 := by
          rw [div_le_one (by exact_mod_cast (Nat.pos_of_ne_zero (by omega : M ≠ 0)))]
          exact Real.log_le_self (Nat.cast_nonneg M)
        have heq : Real.log (M : ℝ) ^ 2 / (M : ℝ) =
            Real.log (M : ℝ) * (Real.log (M : ℝ) / (M : ℝ)) := by ring
        rw [heq]
        calc Real.log (M : ℝ) * (Real.log (M : ℝ) / (M : ℝ))
            ≤ Real.log (M : ℝ) * 1 := mul_le_mul_of_nonneg_left hle hnonneg
          _ = Real.log (M : ℝ) := mul_one _)
      N hN8
    refine h.trans ?_
    linarith
  · have hN7 : N ≤ 7 := by omega
    have hsum_nonneg : 0 ≤ ∑ d ∈ Finset.Icc 1 N, Real.log (d : ℝ) ^ 2 / (d : ℝ) :=
      Finset.sum_nonneg (fun d hd => div_nonneg (sq_nonneg _) (Nat.cast_nonneg d))
    have hsum_le : ∑ d ∈ Finset.Icc 1 N, Real.log (d : ℝ) ^ 2 / (d : ℝ) ≤ 15 := by
      calc ∑ d ∈ Finset.Icc 1 N, Real.log (d : ℝ) ^ 2 / (d : ℝ)
          ≤ ∑ d ∈ Finset.Icc (1 : ℕ) 7, Real.log (d : ℝ) ^ 2 / (d : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.Icc_subset_Icc (le_refl 1) hN7)
              (fun d hd _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg d))
        _ ≤ 15 := logSqDiv_head_bound
    have hmain_le : (Real.log N) ^ 3 / 3 ≤ 4 := by
      have hlog : Real.log (N : ℝ) ≤ 2.1 := log_le_of_le_seven hN7
      have hnonneg : 0 ≤ Real.log (N : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hN)
      have h3 : (Real.log (N : ℝ)) ^ 3 ≤ (2.1 : ℝ) ^ 3 := pow_le_pow_left₀ hnonneg hlog 3
      linarith [h3]
    have hlognonneg : 0 ≤ Real.log (N : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hN)
    have hmain_nonneg : 0 ≤ (Real.log N) ^ 3 / 3 := by positivity
    rw [abs_le]
    constructor <;> nlinarith [hsum_nonneg, hsum_le, hmain_le, hlognonneg, hmain_nonneg,
      abs_nonneg ((Real.log 8) ^ 3 / 3 : ℝ)]

/-- For $N \ge 1$, the harmonic number bound $H_N \le 1 + \log N$ and $H_N \ge 0$ give
$|H_N - \log N| \le 20 + \log N$. -/
private theorem harmonic_sum_bound (N : ℕ) (hN : 1 ≤ N) :
    |∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / (d : ℝ) - Real.log N| ≤ 20 + Real.log N := by
  have hsum : ∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / (d : ℝ) = (harmonic N : ℝ) := by
    simp [harmonic_eq_sum_Icc, one_div]
  have hup := harmonic_le_one_add_log N
  have hnonneg : 0 ≤ ∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / (d : ℝ) :=
    Finset.sum_nonneg fun d _ => by positivity
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  rw [abs_le]
  constructor <;> linarith

/-- The base-$q$ digit sum of $d$, as a real number. -/
private noncomputable def digitSumVal (q d : ℕ) : ℝ := ((Nat.digits q d).sum : ℝ)

/-- The partial sum of the base-$q$ digit sums over $1 \le d \le N$. -/
private noncomputable def partialSumIcc (q N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, digitSumVal q d

/-- The two forms of the digit-sum partial sum agree. -/
private theorem partialSumIcc_eq (q N : ℕ) :
    partialSum q (N + 1) = partialSumIcc q N := by
  unfold partialSum partialSumIcc digitSumVal
  rw [← Finset.Ico_add_one_right_eq_Icc 1 N, Finset.sum_Ico_eq_sum_range,
    Nat.add_sub_cancel, Finset.sum_range_succ']
  simp only [Nat.digits_zero, List.sum_nil, Nat.cast_zero, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  rw [add_comm 1 i]

/-- The error in the main term for the digit-sum partial sums over
$1 \le d \le N$. -/
private theorem partialSumIcc_bound (q : ℕ) (hq : 2 ≤ q) (d : ℕ) (hd : 1 ≤ d) :
    |partialSumIcc q d - ((q : ℝ) - 1) / (2 * Real.log q) * (d : ℝ) * Real.log d| ≤
      4 * (q : ℝ) ^ 2 * (d : ℝ) +
        (4 * (q : ℝ) ^ 2 + 2 * (((q : ℝ) - 1) / (2 * Real.log q))) * (1 + Real.log d) := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogqpos : 0 < Real.log q := Real.log_pos (by linarith)
  set A : ℝ := ((q : ℝ) - 1) / (2 * Real.log q) with hAdef
  have hA_nonneg : 0 ≤ A := by
    rw [hAdef]
    exact div_nonneg (by linarith) (by linarith [hlogqpos])
  have hK_nonneg : 0 ≤ 4 * (q : ℝ) ^ 2 := by positivity
  have hlognonneg : 0 ≤ Real.log (d : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hd)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (Nat.pos_of_ne_zero (by omega))
  have h1 := partialSum_bound q hq (d + 1) (by omega)
  rw [partialSumIcc_eq] at h1
  have hdiff : |A * ((d : ℝ) + 1) * Real.log ((d : ℝ) + 1) - A * (d : ℝ) * Real.log d| ≤
      A * (2 + Real.log d) := by
    have hlogdiff : Real.log ((d : ℝ) + 1) - Real.log d = Real.log (1 + 1 / (d : ℝ)) := by
      have h1' : (1 : ℝ) + 1 / (d : ℝ) = ((d : ℝ) + 1) / (d : ℝ) := by
        field_simp
      rw [h1', Real.log_div (by positivity) (ne_of_gt hdpos)]
    have hle1 : Real.log (1 + 1 / (d : ℝ)) ≤ 1 / (d : ℝ) := by
      have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 1 / (d : ℝ))
      linarith
    have hle2 : Real.log ((d : ℝ) + 1) ≤ Real.log d + 1 := by
      have h2 : Real.log ((d : ℝ) + 1) = Real.log d + Real.log (1 + 1 / (d : ℝ)) := by
        rw [← hlogdiff]; ring
      rw [h2]
      have h3 : (1 : ℝ) / (d : ℝ) ≤ 1 := by
        rw [div_le_one hdpos]
        exact_mod_cast hd
      linarith
    have hnonneg : 0 ≤ A * ((d : ℝ) + 1) * Real.log ((d : ℝ) + 1) -
        A * (d : ℝ) * Real.log d := by
      have hmono : (d : ℝ) * Real.log d ≤ ((d : ℝ) + 1) * Real.log ((d : ℝ) + 1) :=
        mul_le_mul (by linarith) (Real.log_le_log hdpos (by linarith))
          (Real.log_nonneg (by exact_mod_cast hd)) (by linarith)
      nlinarith [hA_nonneg, hmono]
    rw [abs_of_nonneg hnonneg]
    have hdecomp : A * ((d : ℝ) + 1) * Real.log ((d : ℝ) + 1) - A * (d : ℝ) * Real.log d =
        A * ((d : ℝ) * Real.log (1 + 1 / (d : ℝ)) + Real.log ((d : ℝ) + 1)) := by
      linear_combination A * (d : ℝ) * hlogdiff
    rw [hdecomp]
    have h4 : (d : ℝ) * Real.log (1 + 1 / (d : ℝ)) ≤ 1 := by
      have h5 := mul_le_mul_of_nonneg_left hle1 (le_of_lt hdpos)
      rwa [mul_div_cancel₀ _ (ne_of_gt hdpos)] at h5
    calc A * ((d : ℝ) * Real.log (1 + 1 / (d : ℝ)) + Real.log ((d : ℝ) + 1))
        ≤ A * (1 + (Real.log d + 1)) :=
          mul_le_mul_of_nonneg_left (by linarith) hA_nonneg
      _ = A * (2 + Real.log d) := by ring
  have hcast : ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 := by push_cast; ring
  have h1' : |partialSumIcc q d - A * ((d : ℝ) + 1) * Real.log ((d : ℝ) + 1)| ≤
      4 * (q : ℝ) ^ 2 * ((d : ℝ) + 1) := by
    have h2 : (4 : ℝ) * (q : ℝ) ^ 2 * ((d + 1 : ℕ) : ℝ) = 4 * (q : ℝ) ^ 2 * ((d : ℝ) + 1) := by
      rw [hcast]
    rw [← h2]
    convert h1 using 1
    rw [hAdef]
    congr 1
    rw [hcast]
  have hfin : 4 * (q : ℝ) ^ 2 * ((d : ℝ) + 1) + A * (2 + Real.log d) ≤
      4 * (q : ℝ) ^ 2 * (d : ℝ) +
        (4 * (q : ℝ) ^ 2 + 2 * A) * (1 + Real.log d) := by
    have hAL : A * Real.log d ≤ (4 * (q : ℝ) ^ 2 + 2 * A) * Real.log d :=
      mul_le_mul_of_nonneg_right (by linarith [hK_nonneg]) hlognonneg
    nlinarith [hAL, hA_nonneg, hlognonneg, hK_nonneg]
  calc |partialSumIcc q d - A * (d : ℝ) * Real.log d|
      ≤ |partialSumIcc q d - A * ((d : ℝ) + 1) * Real.log ((d : ℝ) + 1)| +
        |A * ((d : ℝ) + 1) * Real.log ((d : ℝ) + 1) - A * (d : ℝ) * Real.log d| := by
        have h := abs_add_le (partialSumIcc q d - A * ((d : ℝ) + 1) * Real.log ((d : ℝ) + 1))
          (A * ((d : ℝ) + 1) * Real.log ((d : ℝ) + 1) - A * (d : ℝ) * Real.log d)
        have heq : (partialSumIcc q d - A * ((d : ℝ) + 1) * Real.log ((d : ℝ) + 1)) +
            (A * ((d : ℝ) + 1) * Real.log ((d : ℝ) + 1) - A * (d : ℝ) * Real.log d) =
          partialSumIcc q d - A * (d : ℝ) * Real.log d := by ring
        rwa [heq] at h
    _ ≤ 4 * (q : ℝ) ^ 2 * ((d : ℝ) + 1) + A * (2 + Real.log d) :=
        add_le_add h1' hdiff
    _ ≤ 4 * (q : ℝ) ^ 2 * (d : ℝ) +
        (4 * (q : ℝ) ^ 2 + 2 * A) * (1 + Real.log d) := hfin

/-- The telescoping sum $\sum_{d=1}^M 1/(d(d+1))$ is at most $1$. -/
private theorem sum_inv_mul_succ_le_one (M : ℕ) :
    ∑ d ∈ Finset.Icc 1 M, (1 : ℝ) / ((d : ℝ) * ((d : ℝ) + 1)) ≤ 1 := by
  have heq : ∀ M : ℕ, ∑ d ∈ Finset.Icc 1 M, (1 : ℝ) / ((d : ℝ) * ((d : ℝ) + 1)) =
      1 - 1 / ((M : ℝ) + 1) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
        rw [Finset.sum_Icc_succ_top (by norm_num : 1 ≤ M + 1), ih]
        have hM : ((M : ℝ) + 1) ≠ 0 := by positivity
        have hM2 : ((M : ℝ) + 2) ≠ 0 := by positivity
        have hcast : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        field_simp
        ring
  rw [heq]
  have h : (0 : ℝ) ≤ 1 / ((M : ℝ) + 1) := by positivity
  linarith

/-- Summation by parts for the digit sum with real weights. -/
private theorem weighted_abel_identity (q N : ℕ) (hN : 1 ≤ N) (w : ℕ → ℝ) :
    ∑ d ∈ Finset.Icc 1 N, digitSumVal q d * w d =
      partialSumIcc q N * w N +
        ∑ d ∈ Finset.Icc 1 (N - 1), partialSumIcc q d * (w d - w (d + 1)) := by
  have hrange (d : ℕ) : ∑ i ∈ Finset.range (d + 1), digitSumVal q i = partialSumIcc q d :=
    partialSumIcc_eq q d
  have hzero : partialSumIcc q 0 = 0 := by simp [partialSumIcc]
  rw [← sub_neg_eq_add, ← Finset.sum_neg_distrib]
  simp_rw [← mul_neg, neg_sub]
  simpa only [← Finset.Icc_add_one_left_eq_Ioc, hrange, hzero, smul_eq_mul, mul_zero,
    sub_zero, Nat.zero_add, mul_comm] using
    Finset.sum_Ioc_by_parts w (digitSumVal q) (m := 0) (n := N) hN

/-- Summation by parts for the reciprocal digit sums. -/
private theorem reciprocal_abel_identity (q : ℕ) :
    ∀ N : ℕ, 1 ≤ N →
      ∑ d ∈ Finset.Icc 1 N, digitSumVal q d / (d : ℝ) =
        partialSumIcc q N / (N : ℝ) +
          ∑ d ∈ Finset.Icc 1 (N - 1), partialSumIcc q d / ((d : ℝ) * ((d : ℝ) + 1)) := by
  intro N hN
  have h := weighted_abel_identity q N hN (fun d => 1 / (d : ℝ))
  simp only [← mul_div_assoc, mul_one, Nat.cast_add_one] at h
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
  field_simp
  ring

/-- Reindexing the shifted harmonic sum. -/
private theorem sum_inv_succ_le_harmonic (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 (N - 1), (1 : ℝ) / ((d : ℝ) + 1) ≤
      ∑ e ∈ Finset.Icc 1 N, (1 : ℝ) / (e : ℝ) := by
  have h1 : ∑ d ∈ Finset.Icc 1 (N - 1), (1 : ℝ) / ((d : ℝ) + 1) =
      ∑ e ∈ Finset.Icc 2 N, (1 : ℝ) / (e : ℝ) := by
    rw [← Finset.Ico_add_one_right_eq_Icc 2 N, ← Finset.Ico_add_one_right_eq_Icc 1 (N - 1),
      Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    have hNM : N + 1 - 2 = N - 1 := by omega
    have hNM2 : N - 1 + 1 - 1 = N - 1 := by omega
    rw [hNM, hNM2]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    push_cast
    ring
  rw [h1]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc (by norm_num) (le_refl N))
    (fun e he _ => by positivity)

/-- The reciprocal digit sums satisfy
$\sum_{d=1}^N s_q(d)/d = \frac{(q-1)\log^2 N}{4 \log q} + O(\log N)$. -/
private theorem reciprocal_sum_bound (q : ℕ) (hq : 2 ≤ q) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ d ∈ Finset.Icc 1 N, digitSumVal q d / (d : ℝ) -
        ((q : ℝ) - 1) / (4 * Real.log q) * (Real.log N) ^ 2| ≤ C * (1 + Real.log N) := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogqpos : 0 < Real.log q := Real.log_pos (by linarith)
  have hlogqne : Real.log q ≠ 0 := ne_of_gt hlogqpos
  set A : ℝ := ((q : ℝ) - 1) / (2 * Real.log q) with hAdef
  set K : ℝ := 4 * (q : ℝ) ^ 2 with hKdef
  set C1 : ℝ := K + 2 * A with hC1def
  have hA_nonneg : 0 ≤ A := by
    rw [hAdef]
    exact div_nonneg (by linarith) (by linarith [hlogqpos])
  have hK_nonneg : 0 ≤ K := by rw [hKdef]; positivity
  have hC1_nonneg : 0 ≤ C1 := by rw [hC1def]; linarith
  set e : ℕ → ℝ := fun d => partialSumIcc q d - A * (d : ℝ) * Real.log d with hedef
  have herr : ∀ d : ℕ, 1 ≤ d → |e d| ≤ K * (d : ℝ) + C1 * (1 + Real.log d) := by
    intro d hd
    have h := partialSumIcc_bound q hq d hd
    rw [← hAdef, ← hKdef, ← hC1def] at h
    have he : e d = partialSumIcc q d - A * (d : ℝ) * Real.log d := by simp [hedef]
    rw [he]
    exact h
  set H8 : ℝ := |(Real.log 8) ^ 2 / 2| with hH8def
  have hH8_nonneg : 0 ≤ H8 := abs_nonneg _
  refine ⟨(K + C1) + A * (25 + H8) + 22 * K + C1 + A, fun N hN => ?_⟩
  have hlognonneg : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have hNpos : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hId := reciprocal_abel_identity q N hN
  -- The substitution of the main term in the Abel sum.
  have hSub : ∑ d ∈ Finset.Icc 1 (N - 1),
        partialSumIcc q d / ((d : ℝ) * ((d : ℝ) + 1)) =
      A * (∑ d ∈ Finset.Icc 1 (N - 1), Real.log d / ((d : ℝ) + 1)) +
        ∑ d ∈ Finset.Icc 1 (N - 1), e d / ((d : ℝ) * ((d : ℝ) + 1)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdpos : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hd1pos : ((d : ℝ) + 1) ≠ 0 := by positivity
    have hSd : partialSumIcc q d = A * (d : ℝ) * Real.log d + e d := by
      simp only [hedef]
      ring
    rw [hSd]
    field_simp
  -- The main logarithmic sum.
  have hMbound : |∑ d ∈ Finset.Icc 1 (N - 1), Real.log d / ((d : ℝ) + 1) -
      (Real.log N) ^ 2 / 2| ≤ 23 + H8 + 2 * Real.log N := by
    have hM1 : ∑ d ∈ Finset.Icc 1 (N - 1), Real.log d / ((d : ℝ) + 1) =
        ∑ d ∈ Finset.Icc 1 (N - 1), Real.log d / (d : ℝ) -
          ∑ d ∈ Finset.Icc 1 (N - 1), Real.log d / ((d : ℝ) * ((d : ℝ) + 1)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hdpos : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hd1pos : ((d : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    have hH1split : ∑ d ∈ Finset.Icc 1 N, Real.log d / (d : ℝ) =
        ∑ d ∈ Finset.Icc 1 (N - 1), Real.log d / (d : ℝ) + Real.log N / (N : ℝ) := by
      conv_lhs => rw [show N = N - 1 + 1 from (Nat.sub_add_cancel hN).symm]
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N - 1 + 1) _, Nat.sub_add_cancel hN]
    have hlogNN : Real.log (N : ℝ) / (N : ℝ) ≤ 1 := by
      rw [div_le_one (by exact_mod_cast (Nat.pos_of_ne_zero (by omega : N ≠ 0)))]
      exact Real.log_le_self (Nat.cast_nonneg N)
    have hTbound : ∑ d ∈ Finset.Icc 1 (N - 1), Real.log d / ((d : ℝ) * ((d : ℝ) + 1)) ≤
        Real.log N := by
      have hterm : ∀ d ∈ Finset.Icc 1 (N - 1),
          Real.log d / ((d : ℝ) * ((d : ℝ) + 1)) ≤
            Real.log N * ((1 : ℝ) / ((d : ℝ) * ((d : ℝ) + 1))) := by
        intro d hd
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have hdle : d ≤ N := le_trans (Finset.mem_Icc.mp hd).2 (by omega)
        have hlogle : Real.log (d : ℝ) ≤ Real.log (N : ℝ) :=
          Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero (by omega : d ≠ 0)))
            (by exact_mod_cast hdle)
        rw [one_div, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hlogle (inv_nonneg.mpr (by positivity))
      calc ∑ d ∈ Finset.Icc 1 (N - 1), Real.log d / ((d : ℝ) * ((d : ℝ) + 1))
          ≤ ∑ d ∈ Finset.Icc 1 (N - 1), Real.log N * ((1 : ℝ) / ((d : ℝ) * ((d : ℝ) + 1))) :=
            Finset.sum_le_sum hterm
        _ = Real.log N * ∑ d ∈ Finset.Icc 1 (N - 1), (1 : ℝ) / ((d : ℝ) * ((d : ℝ) + 1)) := by
            rw [Finset.mul_sum]
        _ ≤ Real.log N * 1 := mul_le_mul_of_nonneg_left (sum_inv_mul_succ_le_one (N - 1))
            hlognonneg
        _ = Real.log N := mul_one _
    have hTnonneg : 0 ≤ ∑ d ∈ Finset.Icc 1 (N - 1),
        Real.log d / ((d : ℝ) * ((d : ℝ) + 1)) :=
      Finset.sum_nonneg (fun d hd => by
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        exact div_nonneg (Real.log_nonneg (by exact_mod_cast hd1)) (by positivity))
    have hH1 := logDiv_sum_bound N hN
    rw [← hH8def] at hH1
    rw [abs_le] at hH1 ⊢
    have hWnonneg : 0 ≤ Real.log (N : ℝ) / (N : ℝ) :=
      div_nonneg hlognonneg (Nat.cast_nonneg N)
    constructor
    · have h1 := hH1.1
      linarith [hM1, hTbound, hTnonneg, hlogNN, hH1split]
    · have h2 := hH1.2
      linarith [hM1, hTbound, hTnonneg, hlogNN, hH1split, hWnonneg]
  -- The error sum.
  have hEbound : |∑ d ∈ Finset.Icc 1 (N - 1), e d / ((d : ℝ) * ((d : ℝ) + 1))| ≤
      K * (20 + 2 * Real.log N) + C1 * (1 + Real.log N) := by
    have hsumabs : |∑ d ∈ Finset.Icc 1 (N - 1), e d / ((d : ℝ) * ((d : ℝ) + 1))| ≤
        ∑ d ∈ Finset.Icc 1 (N - 1), |e d| / ((d : ℝ) * ((d : ℝ) + 1)) := by
      calc |∑ d ∈ Finset.Icc 1 (N - 1), e d / ((d : ℝ) * ((d : ℝ) + 1))|
          ≤ ∑ d ∈ Finset.Icc 1 (N - 1), |e d / ((d : ℝ) * ((d : ℝ) + 1))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ d ∈ Finset.Icc 1 (N - 1), |e d| / ((d : ℝ) * ((d : ℝ) + 1)) := by
            apply Finset.sum_congr rfl
            intro d hd
            have hD : (0 : ℝ) ≤ (d : ℝ) * ((d : ℝ) + 1) :=
              mul_nonneg (Nat.cast_nonneg d) (add_nonneg (Nat.cast_nonneg d) zero_le_one)
            rw [abs_div, abs_of_nonneg hD]
    have hterm : ∀ d ∈ Finset.Icc 1 (N - 1),
        |e d| / ((d : ℝ) * ((d : ℝ) + 1)) ≤
          K / ((d : ℝ) + 1) + C1 * (1 + Real.log N) * ((1 : ℝ) / ((d : ℝ) * ((d : ℝ) + 1))) := by
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hdpos : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hd1pos : ((d : ℝ) + 1) ≠ 0 := by positivity
      have hlogle : Real.log (d : ℝ) ≤ Real.log (N : ℝ) :=
        Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero (by omega : d ≠ 0)))
          (by exact_mod_cast (le_trans (Finset.mem_Icc.mp hd).2 (by omega)))
      have h1 := herr d hd1
      have h2 : |e d| / ((d : ℝ) * ((d : ℝ) + 1)) ≤
          (K * (d : ℝ) + C1 * (1 + Real.log d)) / ((d : ℝ) * ((d : ℝ) + 1)) :=
        div_le_div_of_nonneg_right h1 (by positivity)
      have h3 : (K * (d : ℝ) + C1 * (1 + Real.log d)) / ((d : ℝ) * ((d : ℝ) + 1)) =
          K / ((d : ℝ) + 1) + C1 * (1 + Real.log d) * ((1 : ℝ) / ((d : ℝ) * ((d : ℝ) + 1))) := by
        field_simp
      have h4 : C1 * (1 + Real.log d) * ((1 : ℝ) / ((d : ℝ) * ((d : ℝ) + 1))) ≤
          C1 * (1 + Real.log N) * ((1 : ℝ) / ((d : ℝ) * ((d : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC1_nonneg)
          (by positivity)
      linarith [h2, h3, h4]
    have hreidx := sum_inv_succ_le_harmonic N
    have hHarm := harmonic_sum_bound N hN
    have hHarmle : ∑ e ∈ Finset.Icc 1 N, (1 : ℝ) / (e : ℝ) ≤ 20 + 2 * Real.log N := by
      have h := (abs_le.mp hHarm).2
      linarith
    calc |∑ d ∈ Finset.Icc 1 (N - 1), e d / ((d : ℝ) * ((d : ℝ) + 1))|
        ≤ ∑ d ∈ Finset.Icc 1 (N - 1),
            (K / ((d : ℝ) + 1) + C1 * (1 + Real.log N) * ((1 : ℝ) / ((d : ℝ) * ((d : ℝ) + 1)))) :=
          le_trans hsumabs (Finset.sum_le_sum hterm)
      _ = K * (∑ d ∈ Finset.Icc 1 (N - 1), (1 : ℝ) / ((d : ℝ) + 1)) +
          C1 * (1 + Real.log N) * (∑ d ∈ Finset.Icc 1 (N - 1),
            (1 : ℝ) / ((d : ℝ) * ((d : ℝ) + 1))) := by
          rw [Finset.sum_add_distrib]
          congr 1
          · rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro d _
            rw [div_eq_mul_one_div, one_div]
          · rw [Finset.mul_sum]
      _ ≤ K * (20 + 2 * Real.log N) + C1 * (1 + Real.log N) * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left (hreidx.trans hHarmle) hK_nonneg)
            (mul_le_mul_of_nonneg_left (sum_inv_mul_succ_le_one (N - 1))
              (mul_nonneg hC1_nonneg (by linarith)))
      _ = K * (20 + 2 * Real.log N) + C1 * (1 + Real.log N) := by ring
  -- The boundary term.
  have hSbound : |partialSumIcc q N / (N : ℝ) - A * Real.log N| ≤ K + C1 * (1 + Real.log N) := by
    have hSd : partialSumIcc q N = A * (N : ℝ) * Real.log N + e N := by
      simp only [hedef]
      ring
    have hEq : partialSumIcc q N / (N : ℝ) - A * Real.log N = e N / (N : ℝ) := by
      rw [hSd]
      field_simp
      ring
    rw [hEq, abs_div, abs_of_nonneg (le_of_lt (by positivity : (0 : ℝ) < (N : ℝ)))]
    have h1 := herr N hN
    have h2 : |e N| / (N : ℝ) ≤ (K * (N : ℝ) + C1 * (1 + Real.log N)) / (N : ℝ) :=
      div_le_div_of_nonneg_right h1 (by positivity)
    have h3 : (K * (N : ℝ) + C1 * (1 + Real.log N)) / (N : ℝ) =
        K + C1 * (1 + Real.log N) / (N : ℝ) := by
      field_simp
    have h4 : C1 * (1 + Real.log N) / (N : ℝ) ≤ C1 * (1 + Real.log N) :=
      div_le_self (mul_nonneg hC1_nonneg (by linarith)) (by exact_mod_cast hN)
    linarith [h2, h3, h4]
  -- Assembly.
  have hB : ((q : ℝ) - 1) / (4 * Real.log q) * (Real.log N) ^ 2 = A * ((Real.log N) ^ 2 / 2) := by
    rw [hAdef]
    field_simp
    ring
  have hEq : ∑ d ∈ Finset.Icc 1 N, digitSumVal q d / (d : ℝ) -
        ((q : ℝ) - 1) / (4 * Real.log q) * (Real.log N) ^ 2 =
      (partialSumIcc q N / (N : ℝ) - A * Real.log N) + A * Real.log N +
        A * (∑ d ∈ Finset.Icc 1 (N - 1), Real.log d / ((d : ℝ) + 1) - (Real.log N) ^ 2 / 2) +
        ∑ d ∈ Finset.Icc 1 (N - 1), e d / ((d : ℝ) * ((d : ℝ) + 1)) := by
    rw [hId, hSub, hB]
    ring
  have hTri : |∑ d ∈ Finset.Icc 1 N, digitSumVal q d / (d : ℝ) -
        ((q : ℝ) - 1) / (4 * Real.log q) * (Real.log N) ^ 2| ≤
      |partialSumIcc q N / (N : ℝ) - A * Real.log N| + |A * Real.log N| +
        |A * (∑ d ∈ Finset.Icc 1 (N - 1), Real.log d / ((d : ℝ) + 1) - (Real.log N) ^ 2 / 2)| +
        |∑ d ∈ Finset.Icc 1 (N - 1), e d / ((d : ℝ) * ((d : ℝ) + 1))| := by
    rw [hEq]
    calc |(partialSumIcc q N / (N : ℝ) - A * Real.log N) + A * Real.log N +
          A * (∑ d ∈ Finset.Icc 1 (N - 1), Real.log d / ((d : ℝ) + 1) - (Real.log N) ^ 2 / 2) +
          ∑ d ∈ Finset.Icc 1 (N - 1), e d / ((d : ℝ) * ((d : ℝ) + 1))|
        ≤ |(partialSumIcc q N / (N : ℝ) - A * Real.log N) + A * Real.log N +
          A * (∑ d ∈ Finset.Icc 1 (N - 1), Real.log d / ((d : ℝ) + 1) - (Real.log N) ^ 2 / 2)| +
          |∑ d ∈ Finset.Icc 1 (N - 1), e d / ((d : ℝ) * ((d : ℝ) + 1))| :=
          abs_add_le _ _
      _ ≤ ((|partialSumIcc q N / (N : ℝ) - A * Real.log N| + |A * Real.log N|) +
          |A * (∑ d ∈ Finset.Icc 1 (N - 1), Real.log d / ((d : ℝ) + 1) - (Real.log N) ^ 2 / 2)|) +
          |∑ d ∈ Finset.Icc 1 (N - 1), e d / ((d : ℝ) * ((d : ℝ) + 1))| := by
        have hstep1 : |(partialSumIcc q N / (N : ℝ) - A * Real.log N) + A * Real.log N +
            A * (∑ d ∈ Finset.Icc 1 (N - 1), Real.log d / ((d : ℝ) + 1) - (Real.log N) ^ 2 / 2)| +
            |∑ d ∈ Finset.Icc 1 (N - 1), e d / ((d : ℝ) * ((d : ℝ) + 1))| ≤
            (|(partialSumIcc q N / (N : ℝ) - A * Real.log N) + A * Real.log N| +
            |A * (∑ d ∈ Finset.Icc 1 (N - 1), Real.log d / ((d : ℝ) + 1) - (Real.log N) ^ 2 / 2)|) +
            |∑ d ∈ Finset.Icc 1 (N - 1), e d / ((d : ℝ) * ((d : ℝ) + 1))| := by
          gcongr
          exact abs_add_le _ _
        have hstep2 : (|(partialSumIcc q N / (N : ℝ) - A * Real.log N) + A * Real.log N| +
            |A * (∑ d ∈ Finset.Icc 1 (N - 1), Real.log d / ((d : ℝ) + 1) - (Real.log N) ^ 2 / 2)|) +
            |∑ d ∈ Finset.Icc 1 (N - 1), e d / ((d : ℝ) * ((d : ℝ) + 1))| ≤
            ((|partialSumIcc q N / (N : ℝ) - A * Real.log N| + |A * Real.log N|) +
            |A * (∑ d ∈ Finset.Icc 1 (N - 1), Real.log d / ((d : ℝ) + 1) - (Real.log N) ^ 2 / 2)|) +
            |∑ d ∈ Finset.Icc 1 (N - 1), e d / ((d : ℝ) * ((d : ℝ) + 1))| := by
          gcongr
          exact abs_add_le _ _
        exact le_trans hstep1 hstep2
      _ = |partialSumIcc q N / (N : ℝ) - A * Real.log N| + |A * Real.log N| +
          |A * (∑ d ∈ Finset.Icc 1 (N - 1), Real.log d / ((d : ℝ) + 1) - (Real.log N) ^ 2 / 2)| +
          |∑ d ∈ Finset.Icc 1 (N - 1), e d / ((d : ℝ) * ((d : ℝ) + 1))| := by ring
  have hAmid : |A * (∑ d ∈ Finset.Icc 1 (N - 1), Real.log d / ((d : ℝ) + 1) -
      (Real.log N) ^ 2 / 2)| ≤ A * (23 + H8 + 2 * Real.log N) := by
    rw [abs_mul, abs_of_nonneg hA_nonneg]
    exact mul_le_mul_of_nonneg_left hMbound hA_nonneg
  have h1 : K + C1 * (1 + Real.log N) ≤ (K + C1) * (1 + Real.log N) := by
    have h : K * (Real.log N) ≥ 0 := mul_nonneg hK_nonneg hlognonneg
    nlinarith [h, hK_nonneg, hC1_nonneg]
  have h2 : A * (23 + H8 + 2 * Real.log N) ≤ A * (25 + H8) * (1 + Real.log N) := by
    calc A * (23 + H8 + 2 * Real.log N)
        ≤ A * ((25 + H8) * (1 + Real.log N)) :=
          mul_le_mul_of_nonneg_left (by nlinarith [hH8_nonneg, hlognonneg]) hA_nonneg
      _ = A * (25 + H8) * (1 + Real.log N) := by ring
  have h3 : K * (20 + 2 * Real.log N) ≤ 22 * K * (1 + Real.log N) := by
    calc K * (20 + 2 * Real.log N)
        ≤ K * (22 * (1 + Real.log N)) :=
          mul_le_mul_of_nonneg_left (by linarith) hK_nonneg
      _ = 22 * K * (1 + Real.log N) := by ring
  have hAL : |A * Real.log N| ≤ A * (1 + Real.log N) := by
    rw [abs_of_nonneg (mul_nonneg hA_nonneg hlognonneg)]
    exact mul_le_mul_of_nonneg_left (by linarith) hA_nonneg
  have hY : (K + C1) * (1 + Real.log N) + A * (1 + Real.log N) +
      A * (25 + H8) * (1 + Real.log N) +
      22 * K * (1 + Real.log N) + C1 * (1 + Real.log N) =
      ((K + C1) + A * (25 + H8) + 22 * K + C1 + A) * (1 + Real.log N) := by ring
  linarith [hTri, hSbound, hAmid, hEbound, h1, h2, h3, hY, hAL]

/-- Summation by parts for the log-weighted reciprocal digit sums. -/
private theorem logWeighted_abel_identity (q : ℕ) :
    ∀ N : ℕ, 1 ≤ N →
      ∑ d ∈ Finset.Icc 1 N, digitSumVal q d * Real.log d / (d : ℝ) =
        partialSumIcc q N * Real.log N / (N : ℝ) +
          ∑ d ∈ Finset.Icc 1 (N - 1), partialSumIcc q d *
            (Real.log d / (d : ℝ) - Real.log ((d : ℝ) + 1) / ((d : ℝ) + 1)) := by
  intro N hN
  simpa only [← mul_div_assoc, Nat.cast_add_one] using
    weighted_abel_identity q N hN (fun d => Real.log d / (d : ℝ))

/-- Bounds for $\log(d+1) - \log d$. -/
private theorem log_succ_sub_log_bounds (d : ℕ) (hd : 1 ≤ d) :
    1 / ((d : ℝ) + 1) ≤ Real.log ((d : ℝ) + 1) - Real.log (d : ℝ) ∧
      Real.log ((d : ℝ) + 1) - Real.log (d : ℝ) ≤ 1 / (d : ℝ) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (Nat.pos_of_ne_zero (by omega))
  have hident : Real.log ((d : ℝ) + 1) - Real.log (d : ℝ) =
      Real.log (1 + 1 / (d : ℝ)) := by
    have h1 : (1 : ℝ) + 1 / (d : ℝ) = ((d : ℝ) + 1) / (d : ℝ) := by field_simp
    rw [h1, Real.log_div (by positivity) (ne_of_gt hdpos)]
  rw [hident]
  constructor
  · have h : Real.log (1 + 1 / (d : ℝ)) = -Real.log (1 + 1 / (d : ℝ))⁻¹ := by
      rw [← Real.log_inv]
      congr 1
      field_simp
    rw [h]
    have hle : Real.log (1 + 1 / (d : ℝ))⁻¹ ≤ (1 + 1 / (d : ℝ))⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have heq : (1 : ℝ) - (1 + 1 / (d : ℝ))⁻¹ = 1 / ((d : ℝ) + 1) := by
      field_simp
      ring
    linarith [hle, heq]
  · have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 1 / (d : ℝ))
    linarith

/-- Triangle inequality for four summands. -/
private theorem abs_le_add_four (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  calc |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
    _ ≤ (|a + b| + |c|) + |d| := by
      gcongr
      exact abs_add_le _ _
    _ ≤ ((|a| + |b|) + |c|) + |d| := by
      gcongr
      exact abs_add_le _ _
    _ = |a| + |b| + |c| + |d| := by ring

/-- The per-term comparison between the weighted summand and $\log d / d$. -/
private theorem logWeight_term_bound (d N : ℕ) (hd : 1 ≤ d) (hdN : d ≤ N) :
    |(d : ℝ) * Real.log d * (Real.log ((d : ℝ) + 1) - Real.log d) / ((d : ℝ) + 1) -
      Real.log d / (d : ℝ)| ≤
      3 * Real.log N / ((d : ℝ) * ((d : ℝ) + 1)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (Nat.pos_of_ne_zero (by omega))
  have hd1pos : (0 : ℝ) < (d : ℝ) + 1 := by linarith
  have hlognonneg : 0 ≤ Real.log (d : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hd)
  have hlogle : Real.log (d : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hdpos (by exact_mod_cast hdN)
  set Δ : ℝ := Real.log ((d : ℝ) + 1) - Real.log d with hΔdef
  have hΔbounds := log_succ_sub_log_bounds d hd
  have hu_lo : (d : ℝ) / ((d : ℝ) + 1) ≤ (d : ℝ) * Δ := by
    rw [hΔdef]
    have h1 : ((d : ℝ) + 1)⁻¹ ≤ Real.log ((d : ℝ) + 1) - Real.log (d : ℝ) := by
      rw [← one_div]
      exact hΔbounds.1
    exact mul_le_mul_of_nonneg_left h1 (le_of_lt hdpos)
  have hu_hi : (d : ℝ) * Δ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hΔbounds.2 (le_of_lt hdpos)
    rwa [mul_div_cancel₀ _ (ne_of_gt hdpos)] at h
  set u : ℝ := (d : ℝ) * Δ with hudef
  have hId : (d : ℝ) * Real.log d * Δ / ((d : ℝ) + 1) - Real.log d / (d : ℝ) =
      Real.log d * (u * (d : ℝ) - ((d : ℝ) + 1)) / ((d : ℝ) * ((d : ℝ) + 1)) := by
    rw [hudef]
    field_simp
  have hnum : |u * (d : ℝ) - ((d : ℝ) + 1)| ≤ 3 := by
    rw [abs_le]
    constructor
    · have h1 : (d : ℝ) ^ 2 / ((d : ℝ) + 1) ≤ u * (d : ℝ) := by
        have h := mul_le_mul_of_nonneg_right hu_lo (le_of_lt hdpos)
        have heq : (d : ℝ) / ((d : ℝ) + 1) * (d : ℝ) = (d : ℝ) ^ 2 / ((d : ℝ) + 1) := by
          field_simp
        rwa [heq] at h
      have h2 : (2 : ℝ) * (d : ℝ) + 1 ≤ 3 * ((d : ℝ) + 1) := by
        linarith [(Nat.cast_nonneg (d : ℕ) : (0 : ℝ) ≤ (d : ℝ))]
      have h3 : ((d : ℝ) ^ 2 / ((d : ℝ) + 1)) - ((d : ℝ) + 1) ≥ -3 := by
        have h4 : ((d : ℝ) ^ 2 / ((d : ℝ) + 1)) - ((d : ℝ) + 1) =
            -(((2 : ℝ) * (d : ℝ) + 1) / ((d : ℝ) + 1)) := by
          field_simp
          ring
        rw [h4]
        have h5 : ((2 : ℝ) * (d : ℝ) + 1) / ((d : ℝ) + 1) ≤ 3 := by
          rw [div_le_iff₀ hd1pos]
          linarith [(Nat.cast_nonneg (d : ℕ) : (0 : ℝ) ≤ (d : ℝ))]
        linarith
      linarith
    · have h1 : u * (d : ℝ) ≤ (d : ℝ) := by
        calc u * (d : ℝ) ≤ 1 * (d : ℝ) := mul_le_mul_of_nonneg_right hu_hi (le_of_lt hdpos)
          _ = (d : ℝ) := one_mul _
      linarith
  rw [hId, abs_div, abs_mul, abs_of_nonneg hlognonneg,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (d : ℝ) * ((d : ℝ) + 1))]
  calc Real.log d * |u * (d : ℝ) - ((d : ℝ) + 1)| / ((d : ℝ) * ((d : ℝ) + 1))
      ≤ Real.log N * 3 / ((d : ℝ) * ((d : ℝ) + 1)) :=
        div_le_div_of_nonneg_right
          (mul_le_mul hlogle hnum (abs_nonneg _)
            (Real.log_nonneg (by exact_mod_cast (le_trans hd hdN)))) (by positivity)
    _ = 3 * Real.log N / ((d : ℝ) * ((d : ℝ) + 1)) := by ring

/-- The log-weighted reciprocal digit sums satisfy
$\sum_{d=1}^N s_q(d) \log d / d = \frac{(q-1)\log^3 N}{6 \log q} + O(\log^2 N)$. -/
private theorem logWeighted_sum_bound (q : ℕ) (hq : 2 ≤ q) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ d ∈ Finset.Icc 1 N, digitSumVal q d * Real.log d / (d : ℝ) -
        ((q : ℝ) - 1) / (6 * Real.log q) * (Real.log N) ^ 3| ≤ C * (1 + (Real.log N) ^ 2) := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogqpos : 0 < Real.log q := Real.log_pos (by linarith)
  set A : ℝ := ((q : ℝ) - 1) / (2 * Real.log q) with hAdef
  set K : ℝ := 4 * (q : ℝ) ^ 2 with hKdef
  set C1 : ℝ := K + 2 * A with hC1def
  have hA_nonneg : 0 ≤ A := by
    rw [hAdef]
    exact div_nonneg (by linarith) (by linarith [hlogqpos])
  have hK_nonneg : 0 ≤ K := by rw [hKdef]; positivity
  have hC1_nonneg : 0 ≤ C1 := by rw [hC1def]; linarith
  set e : ℕ → ℝ := fun d => partialSumIcc q d - A * (d : ℝ) * Real.log d with hedef
  have herr : ∀ d : ℕ, 1 ≤ d → |e d| ≤ K * (d : ℝ) + C1 * (1 + Real.log d) := by
    intro d hd
    have h := partialSumIcc_bound q hq d hd
    rw [← hAdef, ← hKdef, ← hC1def] at h
    have he : e d = partialSumIcc q d - A * (d : ℝ) * Real.log d := by simp [hedef]
    rw [he]
    exact h
  set H8 : ℝ := |(Real.log 8) ^ 2 / 2| with hH8def
  set H8b : ℝ := |(Real.log 8) ^ 3 / 3| with hH8bdef
  have hH8_nonneg : 0 ≤ H8 := abs_nonneg _
  have hH8b_nonneg : 0 ≤ H8b := abs_nonneg _
  refine ⟨(K + 2 * C1) + A / 2 + A * (26 + H8b) + A * (28 + H8) + 44 * K + 2 * C1,
    fun N hN => ?_⟩
  have hlognonneg : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have hNpos : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hId := logWeighted_abel_identity q N hN
  -- The substitution of the main term in the Abel sum.
  have hSub : ∑ d ∈ Finset.Icc 1 (N - 1), partialSumIcc q d *
        (Real.log d / (d : ℝ) - Real.log ((d : ℝ) + 1) / ((d : ℝ) + 1)) =
      A * ((∑ d ∈ Finset.Icc 1 (N - 1), Real.log d ^ 2 / ((d : ℝ) + 1)) -
        ∑ d ∈ Finset.Icc 1 (N - 1), (d : ℝ) * Real.log d *
          (Real.log ((d : ℝ) + 1) - Real.log d) / ((d : ℝ) + 1)) +
        ∑ d ∈ Finset.Icc 1 (N - 1), e d *
          (Real.log d / (d : ℝ) - Real.log ((d : ℝ) + 1) / ((d : ℝ) + 1)) := by
    have hterm : ∀ d ∈ Finset.Icc 1 (N - 1), partialSumIcc q d *
          (Real.log d / (d : ℝ) - Real.log ((d : ℝ) + 1) / ((d : ℝ) + 1)) =
        A * (Real.log d ^ 2 / ((d : ℝ) + 1) - (d : ℝ) * Real.log d *
          (Real.log ((d : ℝ) + 1) - Real.log d) / ((d : ℝ) + 1)) +
          e d * (Real.log d / (d : ℝ) - Real.log ((d : ℝ) + 1) / ((d : ℝ) + 1)) := by
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hdpos : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hd1pos : ((d : ℝ) + 1) ≠ 0 := by positivity
      have hSd : partialSumIcc q d = A * (d : ℝ) * Real.log d + e d := by
        simp only [hedef]
        ring
      rw [hSd]
      field_simp
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_sub_distrib]
  -- The first main sum.
  have hP1bound : |∑ d ∈ Finset.Icc 1 (N - 1), Real.log d ^ 2 / ((d : ℝ) + 1) -
      (Real.log N) ^ 3 / 3| ≤ 22 + H8b + 2 * Real.log N + (Real.log N) ^ 2 := by
    have hP1eq : ∑ d ∈ Finset.Icc 1 (N - 1), Real.log d ^ 2 / ((d : ℝ) + 1) =
        ∑ d ∈ Finset.Icc 1 (N - 1), Real.log d ^ 2 / (d : ℝ) -
          ∑ d ∈ Finset.Icc 1 (N - 1), Real.log d ^ 2 / ((d : ℝ) * ((d : ℝ) + 1)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hdpos : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hd1pos : ((d : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    have hH2split : ∑ d ∈ Finset.Icc 1 N, Real.log d ^ 2 / (d : ℝ) =
        ∑ d ∈ Finset.Icc 1 (N - 1), Real.log d ^ 2 / (d : ℝ) +
          Real.log N ^ 2 / (N : ℝ) := by
      conv_lhs => rw [show N = N - 1 + 1 from (Nat.sub_add_cancel hN).symm]
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N - 1 + 1) _, Nat.sub_add_cancel hN]
    have hlog2NN : Real.log N ^ 2 / (N : ℝ) ≤ Real.log N := by
      rw [div_le_iff₀ (by exact_mod_cast (Nat.pos_of_ne_zero (by omega : N ≠ 0)))]
      have hle : Real.log (N : ℝ) ≤ (N : ℝ) := Real.log_le_self (Nat.cast_nonneg N)
      calc Real.log N ^ 2 = Real.log N * Real.log N := by ring
        _ ≤ Real.log N * (N : ℝ) := mul_le_mul_of_nonneg_left hle hlognonneg
    have hRbound : ∑ d ∈ Finset.Icc 1 (N - 1), Real.log d ^ 2 / ((d : ℝ) * ((d : ℝ) + 1)) ≤
        (Real.log N) ^ 2 := by
      have hterm : ∀ d ∈ Finset.Icc 1 (N - 1),
          Real.log d ^ 2 / ((d : ℝ) * ((d : ℝ) + 1)) ≤
            (Real.log N) ^ 2 * ((1 : ℝ) / ((d : ℝ) * ((d : ℝ) + 1))) := by
        intro d hd
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have hsq : Real.log (d : ℝ) ^ 2 ≤ (Real.log N) ^ 2 :=
          pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast hd1))
            (Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero (by omega : d ≠ 0)))
              (by exact_mod_cast (le_trans (Finset.mem_Icc.mp hd).2 (by omega)))) 2
        rw [div_eq_mul_one_div, div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_right hsq (by positivity)
      calc ∑ d ∈ Finset.Icc 1 (N - 1), Real.log d ^ 2 / ((d : ℝ) * ((d : ℝ) + 1))
          ≤ ∑ d ∈ Finset.Icc 1 (N - 1), (Real.log N) ^ 2 *
              ((1 : ℝ) / ((d : ℝ) * ((d : ℝ) + 1))) := Finset.sum_le_sum hterm
        _ = (Real.log N) ^ 2 * ∑ d ∈ Finset.Icc 1 (N - 1),
              (1 : ℝ) / ((d : ℝ) * ((d : ℝ) + 1)) := by rw [Finset.mul_sum]
        _ ≤ (Real.log N) ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left (sum_inv_mul_succ_le_one (N - 1)) (by positivity)
        _ = (Real.log N) ^ 2 := mul_one _
    have hRnonneg : 0 ≤ ∑ d ∈ Finset.Icc 1 (N - 1),
        Real.log d ^ 2 / ((d : ℝ) * ((d : ℝ) + 1)) :=
      Finset.sum_nonneg (fun d hd => by positivity)
    have hH2 := logSqDiv_sum_bound N hN
    rw [← hH8bdef] at hH2
    have hH2sum : |∑ d ∈ Finset.Icc 1 (N - 1), Real.log d ^ 2 / (d : ℝ) -
        (Real.log N) ^ 3 / 3| ≤ (22 + H8b + Real.log N) + Real.log N := by
      have hEq : ∑ d ∈ Finset.Icc 1 (N - 1), Real.log d ^ 2 / (d : ℝ) - (Real.log N) ^ 3 / 3 =
          (∑ d ∈ Finset.Icc 1 N, Real.log d ^ 2 / (d : ℝ) - (Real.log N) ^ 3 / 3) -
            Real.log N ^ 2 / (N : ℝ) := by rw [hH2split]; ring
      rw [hEq]
      calc |(∑ d ∈ Finset.Icc 1 N, Real.log d ^ 2 / (d : ℝ) - (Real.log N) ^ 3 / 3) -
            Real.log N ^ 2 / (N : ℝ)|
          ≤ |∑ d ∈ Finset.Icc 1 N, Real.log d ^ 2 / (d : ℝ) - (Real.log N) ^ 3 / 3| +
            |Real.log N ^ 2 / (N : ℝ)| := abs_sub _ _
        _ ≤ (22 + H8b + Real.log N) + Real.log N := by
            have hnn : |Real.log N ^ 2 / (N : ℝ)| = Real.log N ^ 2 / (N : ℝ) :=
              abs_of_nonneg (by positivity)
            rw [hnn]
            exact add_le_add hH2 hlog2NN
    calc |∑ d ∈ Finset.Icc 1 (N - 1), Real.log d ^ 2 / ((d : ℝ) + 1) - (Real.log N) ^ 3 / 3|
        = |(∑ d ∈ Finset.Icc 1 (N - 1), Real.log d ^ 2 / (d : ℝ) - (Real.log N) ^ 3 / 3) -
          ∑ d ∈ Finset.Icc 1 (N - 1), Real.log d ^ 2 / ((d : ℝ) * ((d : ℝ) + 1))| := by
          rw [hP1eq]
          congr 1
          ring
      _ ≤ |∑ d ∈ Finset.Icc 1 (N - 1), Real.log d ^ 2 / (d : ℝ) - (Real.log N) ^ 3 / 3| +
          |∑ d ∈ Finset.Icc 1 (N - 1), Real.log d ^ 2 / ((d : ℝ) * ((d : ℝ) + 1))| :=
          abs_sub _ _
      _ ≤ ((22 + H8b + Real.log N) + Real.log N) + (Real.log N) ^ 2 :=
          add_le_add hH2sum (by rw [abs_of_nonneg hRnonneg]; exact hRbound)
      _ = 22 + H8b + 2 * Real.log N + (Real.log N) ^ 2 := by ring
  -- The second main sum.
  have hH1sumbound : |∑ d ∈ Finset.Icc 1 (N - 1), Real.log d / (d : ℝ) -
      (Real.log N) ^ 2 / 2| ≤ 23 + H8 + 2 * Real.log N := by
    have hH1split : ∑ d ∈ Finset.Icc 1 N, Real.log d / (d : ℝ) =
        ∑ d ∈ Finset.Icc 1 (N - 1), Real.log d / (d : ℝ) + Real.log N / (N : ℝ) := by
      conv_lhs => rw [show N = N - 1 + 1 from (Nat.sub_add_cancel hN).symm]
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N - 1 + 1) _, Nat.sub_add_cancel hN]
    have hlogNN : Real.log (N : ℝ) / (N : ℝ) ≤ 1 := by
      rw [div_le_one (by exact_mod_cast (Nat.pos_of_ne_zero (by omega : N ≠ 0)))]
      exact Real.log_le_self (Nat.cast_nonneg N)
    have hWnonneg : 0 ≤ Real.log (N : ℝ) / (N : ℝ) :=
      div_nonneg hlognonneg (Nat.cast_nonneg N)
    have hH1 := logDiv_sum_bound N hN
    rw [← hH8def] at hH1
    have hEq : ∑ d ∈ Finset.Icc 1 (N - 1), Real.log d / (d : ℝ) - (Real.log N) ^ 2 / 2 =
        (∑ d ∈ Finset.Icc 1 N, Real.log d / (d : ℝ) - (Real.log N) ^ 2 / 2) -
          Real.log N / (N : ℝ) := by linear_combination -hH1split
    rw [hEq]
    calc |(∑ d ∈ Finset.Icc 1 N, Real.log d / (d : ℝ) - (Real.log N) ^ 2 / 2) -
          Real.log N / (N : ℝ)|
        ≤ |∑ d ∈ Finset.Icc 1 N, Real.log d / (d : ℝ) - (Real.log N) ^ 2 / 2| +
          |Real.log N / (N : ℝ)| := abs_sub _ _
      _ ≤ (22 + H8 + Real.log N) + 1 := by
          have hnn : |Real.log N / (N : ℝ)| = Real.log N / (N : ℝ) := abs_of_nonneg hWnonneg
          rw [hnn]
          exact add_le_add hH1 hlogNN
      _ ≤ 23 + H8 + 2 * Real.log N := by linarith
  have hP2bound : |∑ d ∈ Finset.Icc 1 (N - 1), (d : ℝ) * Real.log d *
        (Real.log ((d : ℝ) + 1) - Real.log d) / ((d : ℝ) + 1) - (Real.log N) ^ 2 / 2| ≤
      23 + H8 + 5 * Real.log N := by
    have hdiff : |∑ d ∈ Finset.Icc 1 (N - 1), (d : ℝ) * Real.log d *
          (Real.log ((d : ℝ) + 1) - Real.log d) / ((d : ℝ) + 1) -
          ∑ d ∈ Finset.Icc 1 (N - 1), Real.log d / (d : ℝ)| ≤ 3 * Real.log N := by
      have hEq : ∑ d ∈ Finset.Icc 1 (N - 1), (d : ℝ) * Real.log d *
            (Real.log ((d : ℝ) + 1) - Real.log d) / ((d : ℝ) + 1) -
            ∑ d ∈ Finset.Icc 1 (N - 1), Real.log d / (d : ℝ) =
          ∑ d ∈ Finset.Icc 1 (N - 1), ((d : ℝ) * Real.log d *
            (Real.log ((d : ℝ) + 1) - Real.log d) / ((d : ℝ) + 1) -
            Real.log d / (d : ℝ)) := by rw [Finset.sum_sub_distrib]
      rw [hEq]
      calc |∑ d ∈ Finset.Icc 1 (N - 1), ((d : ℝ) * Real.log d *
            (Real.log ((d : ℝ) + 1) - Real.log d) / ((d : ℝ) + 1) -
            Real.log d / (d : ℝ))|
          ≤ ∑ d ∈ Finset.Icc 1 (N - 1), |(d : ℝ) * Real.log d *
              (Real.log ((d : ℝ) + 1) - Real.log d) / ((d : ℝ) + 1) -
              Real.log d / (d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d ∈ Finset.Icc 1 (N - 1), 3 * Real.log N / ((d : ℝ) * ((d : ℝ) + 1)) :=
            Finset.sum_le_sum (fun d hd => logWeight_term_bound d N
              (Finset.mem_Icc.mp hd).1 (le_trans (Finset.mem_Icc.mp hd).2 (by omega)))
        _ = 3 * Real.log N * ∑ d ∈ Finset.Icc 1 (N - 1),
              (1 : ℝ) / ((d : ℝ) * ((d : ℝ) + 1)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro d _
            ring
        _ ≤ 3 * Real.log N * 1 :=
            mul_le_mul_of_nonneg_left (sum_inv_mul_succ_le_one (N - 1))
              (by linarith [hlognonneg])
        _ = 3 * Real.log N := mul_one _
    have hEq : ∑ d ∈ Finset.Icc 1 (N - 1), (d : ℝ) * Real.log d *
          (Real.log ((d : ℝ) + 1) - Real.log d) / ((d : ℝ) + 1) - (Real.log N) ^ 2 / 2 =
        (∑ d ∈ Finset.Icc 1 (N - 1), (d : ℝ) * Real.log d *
          (Real.log ((d : ℝ) + 1) - Real.log d) / ((d : ℝ) + 1) -
          ∑ d ∈ Finset.Icc 1 (N - 1), Real.log d / (d : ℝ)) +
        (∑ d ∈ Finset.Icc 1 (N - 1), Real.log d / (d : ℝ) - (Real.log N) ^ 2 / 2) := by ring
    rw [hEq]
    calc |(∑ d ∈ Finset.Icc 1 (N - 1), (d : ℝ) * Real.log d *
          (Real.log ((d : ℝ) + 1) - Real.log d) / ((d : ℝ) + 1) -
          ∑ d ∈ Finset.Icc 1 (N - 1), Real.log d / (d : ℝ)) +
        (∑ d ∈ Finset.Icc 1 (N - 1), Real.log d / (d : ℝ) - (Real.log N) ^ 2 / 2)|
        ≤ |∑ d ∈ Finset.Icc 1 (N - 1), (d : ℝ) * Real.log d *
          (Real.log ((d : ℝ) + 1) - Real.log d) / ((d : ℝ) + 1) -
          ∑ d ∈ Finset.Icc 1 (N - 1), Real.log d / (d : ℝ)| +
          |∑ d ∈ Finset.Icc 1 (N - 1), Real.log d / (d : ℝ) - (Real.log N) ^ 2 / 2| :=
          abs_add_le _ _
      _ ≤ 3 * Real.log N + (23 + H8 + 2 * Real.log N) := add_le_add hdiff hH1sumbound
      _ = 23 + H8 + 5 * Real.log N := by ring
  -- The boundary term.
  have hBoundary : |partialSumIcc q N * Real.log N / (N : ℝ) - A * (Real.log N) ^ 2| ≤
      K * Real.log N + C1 * (1 + Real.log N) * Real.log N := by
    have hSd : partialSumIcc q N = A * (N : ℝ) * Real.log N + e N := by
      simp only [hedef]
      ring
    have hEq : partialSumIcc q N * Real.log N / (N : ℝ) - A * (Real.log N) ^ 2 =
        (e N * Real.log N) / (N : ℝ) := by
      rw [hSd]
      field_simp
      ring
    rw [hEq, abs_div, abs_mul, abs_of_nonneg hlognonneg,
      abs_of_nonneg (le_of_lt (by positivity : (0 : ℝ) < (N : ℝ)))]
    have h1 := herr N hN
    have h2 : |e N| * Real.log N / (N : ℝ) ≤
        (K * (N : ℝ) + C1 * (1 + Real.log N)) * Real.log N / (N : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right h1 hlognonneg) (by positivity)
    have h3 : (K * (N : ℝ) + C1 * (1 + Real.log N)) * Real.log N / (N : ℝ) =
        K * Real.log N + C1 * (1 + Real.log N) * Real.log N / (N : ℝ) := by
      field_simp
    have h4 : C1 * (1 + Real.log N) * Real.log N / (N : ℝ) ≤
        C1 * (1 + Real.log N) * Real.log N :=
      div_le_self (by
        have h5 : (0 : ℝ) ≤ C1 * (1 + Real.log N) * Real.log N :=
          mul_nonneg (mul_nonneg hC1_nonneg (by linarith)) hlognonneg
        exact h5) (by exact_mod_cast hN)
    linarith [h2, h3, h4]
  -- The error sum.
  have hE2bound : |∑ d ∈ Finset.Icc 1 (N - 1), e d *
        (Real.log d / (d : ℝ) - Real.log ((d : ℝ) + 1) / ((d : ℝ) + 1))| ≤
      K * (1 + Real.log N) * (20 + 2 * Real.log N) + C1 * (1 + Real.log N) ^ 2 := by
    have hdiffbound : ∀ d ∈ Finset.Icc 1 (N - 1),
        |Real.log d / (d : ℝ) - Real.log ((d : ℝ) + 1) / ((d : ℝ) + 1)| ≤
          (Real.log d + 1) / ((d : ℝ) * ((d : ℝ) + 1)) := by
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hdpos : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hd1pos : ((d : ℝ) + 1) ≠ 0 := by positivity
      have hident : Real.log d / (d : ℝ) - Real.log ((d : ℝ) + 1) / ((d : ℝ) + 1) =
          Real.log d / ((d : ℝ) * ((d : ℝ) + 1)) -
            (Real.log ((d : ℝ) + 1) - Real.log d) / ((d : ℝ) + 1) := by
        field_simp
        ring
      have hΔnonneg : 0 ≤ Real.log ((d : ℝ) + 1) - Real.log d :=
        sub_nonneg.mpr (Real.log_le_log
          (by exact_mod_cast (Nat.pos_of_ne_zero (by omega : d ≠ 0)) : (0 : ℝ) < (d : ℝ))
          (by linarith))
      have hΔle : Real.log ((d : ℝ) + 1) - Real.log d ≤ 1 / (d : ℝ) :=
        (log_succ_sub_log_bounds d hd1).2
      have h1 : |Real.log d / ((d : ℝ) * ((d : ℝ) + 1)) -
          (Real.log ((d : ℝ) + 1) - Real.log d) / ((d : ℝ) + 1)| ≤
          (Real.log d + 1) / ((d : ℝ) * ((d : ℝ) + 1)) := by
        calc |Real.log d / ((d : ℝ) * ((d : ℝ) + 1)) -
              (Real.log ((d : ℝ) + 1) - Real.log d) / ((d : ℝ) + 1)|
            ≤ |Real.log d / ((d : ℝ) * ((d : ℝ) + 1))| +
              |(Real.log ((d : ℝ) + 1) - Real.log d) / ((d : ℝ) + 1)| := abs_sub _ _
          _ = Real.log d / ((d : ℝ) * ((d : ℝ) + 1)) +
              (Real.log ((d : ℝ) + 1) - Real.log d) / ((d : ℝ) + 1) := by
              rw [abs_of_nonneg (div_nonneg
                (Real.log_nonneg (by exact_mod_cast hd1)) (by positivity)),
                abs_of_nonneg (div_nonneg hΔnonneg (by linarith))]
          _ ≤ (Real.log d + 1) / ((d : ℝ) * ((d : ℝ) + 1)) := by
            have h2 : (Real.log ((d : ℝ) + 1) - Real.log d) / ((d : ℝ) + 1) ≤
                1 / ((d : ℝ) * ((d : ℝ) + 1)) := by
              have hc : (0 : ℝ) ≤ (d : ℝ) + 1 := by positivity
              have h := div_le_div_of_nonneg_right hΔle hc
              rwa [div_div] at h
            have h : Real.log d / ((d : ℝ) * ((d : ℝ) + 1)) +
                (Real.log ((d : ℝ) + 1) - Real.log d) / ((d : ℝ) + 1) ≤
                Real.log d / ((d : ℝ) * ((d : ℝ) + 1)) +
                  1 / ((d : ℝ) * ((d : ℝ) + 1)) := add_le_add le_rfl h2
            have heq := (add_div (Real.log d) (1 : ℝ) ((d : ℝ) * ((d : ℝ) + 1))).symm
            rwa [heq] at h
      rw [hident]
      exact h1
  -- The error sum, continued.
    have hreidx := sum_inv_succ_le_harmonic N
    have hHarm := harmonic_sum_bound N hN
    have hHarmle : ∑ e ∈ Finset.Icc 1 N, (1 : ℝ) / (e : ℝ) ≤ 20 + 2 * Real.log N := by
      have h := (abs_le.mp hHarm).2
      linarith
    have hsumabs : |∑ d ∈ Finset.Icc 1 (N - 1), e d *
          (Real.log d / (d : ℝ) - Real.log ((d : ℝ) + 1) / ((d : ℝ) + 1))| ≤
        ∑ d ∈ Finset.Icc 1 (N - 1), |e d| * ((Real.log d + 1) / ((d : ℝ) * ((d : ℝ) + 1))) := by
      calc |∑ d ∈ Finset.Icc 1 (N - 1), e d *
            (Real.log d / (d : ℝ) - Real.log ((d : ℝ) + 1) / ((d : ℝ) + 1))|
          ≤ ∑ d ∈ Finset.Icc 1 (N - 1), |e d *
              (Real.log d / (d : ℝ) - Real.log ((d : ℝ) + 1) / ((d : ℝ) + 1))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ d ∈ Finset.Icc 1 (N - 1), |e d| * ((Real.log d + 1) / ((d : ℝ) * ((d : ℝ) + 1))) :=
            Finset.sum_le_sum (fun d hd => by
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_left (hdiffbound d hd) (abs_nonneg _))
    have hterm : ∀ d ∈ Finset.Icc 1 (N - 1),
        |e d| * ((Real.log d + 1) / ((d : ℝ) * ((d : ℝ) + 1))) ≤
          K * (1 + Real.log N) / ((d : ℝ) + 1) +
            C1 * (1 + Real.log N) ^ 2 * ((1 : ℝ) / ((d : ℝ) * ((d : ℝ) + 1))) := by
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hdpos : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hd1pos : ((d : ℝ) + 1) ≠ 0 := by positivity
      have hlogle : Real.log (d : ℝ) ≤ Real.log (N : ℝ) :=
        Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero (by omega : d ≠ 0)))
          (by exact_mod_cast (le_trans (Finset.mem_Icc.mp hd).2 (by omega)))
      have hlogdnonneg : 0 ≤ Real.log (d : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hd1)
      have h1 : |e d| * ((Real.log d + 1) / ((d : ℝ) * ((d : ℝ) + 1))) ≤
          (K * (d : ℝ) + C1 * (1 + Real.log d)) * ((Real.log d + 1) / ((d : ℝ) * ((d : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_right (herr d hd1)
          (div_nonneg (by linarith) (by positivity))
      have h2 : (K * (d : ℝ) + C1 * (1 + Real.log d)) *
            ((Real.log d + 1) / ((d : ℝ) * ((d : ℝ) + 1))) =
          K * (Real.log d + 1) / ((d : ℝ) + 1) +
            C1 * (1 + Real.log d) ^ 2 / ((d : ℝ) * ((d : ℝ) + 1)) := by
        field_simp
        ring
      have h3 : K * (Real.log d + 1) / ((d : ℝ) + 1) ≤ K * (1 + Real.log N) / ((d : ℝ) + 1) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) hK_nonneg) (by positivity)
      have h4 : C1 * (1 + Real.log d) ^ 2 / ((d : ℝ) * ((d : ℝ) + 1)) ≤
          C1 * (1 + Real.log N) ^ 2 * ((1 : ℝ) / ((d : ℝ) * ((d : ℝ) + 1))) := by
        have hpow : (1 + Real.log d) ^ 2 ≤ (1 + Real.log N) ^ 2 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 2
        rw [div_eq_mul_one_div, div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow hC1_nonneg) (by positivity)
      linarith [h1, h2, h3, h4]
    calc |∑ d ∈ Finset.Icc 1 (N - 1), e d *
          (Real.log d / (d : ℝ) - Real.log ((d : ℝ) + 1) / ((d : ℝ) + 1))|
        ≤ ∑ d ∈ Finset.Icc 1 (N - 1),
            (K * (1 + Real.log N) / ((d : ℝ) + 1) +
              C1 * (1 + Real.log N) ^ 2 * ((1 : ℝ) / ((d : ℝ) * ((d : ℝ) + 1)))) :=
          le_trans hsumabs (Finset.sum_le_sum hterm)
      _ = K * (1 + Real.log N) * (∑ d ∈ Finset.Icc 1 (N - 1), (1 : ℝ) / ((d : ℝ) + 1)) +
          C1 * (1 + Real.log N) ^ 2 * (∑ d ∈ Finset.Icc 1 (N - 1),
            (1 : ℝ) / ((d : ℝ) * ((d : ℝ) + 1))) := by
          rw [Finset.sum_add_distrib]
          congr 1
          · rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro d _
            rw [div_eq_mul_one_div]
          · rw [Finset.mul_sum]
      _ ≤ K * (1 + Real.log N) * (20 + 2 * Real.log N) + C1 * (1 + Real.log N) ^ 2 * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left (hreidx.trans hHarmle)
            (by positivity : (0 : ℝ) ≤ K * (1 + Real.log N)))
            (mul_le_mul_of_nonneg_left (sum_inv_mul_succ_le_one (N - 1))
              (by positivity : (0 : ℝ) ≤ C1 * (1 + Real.log N) ^ 2))
      _ = K * (1 + Real.log N) * (20 + 2 * Real.log N) + C1 * (1 + Real.log N) ^ 2 := by ring
  -- Assembly.
  have hlogqne : Real.log q ≠ 0 := ne_of_gt hlogqpos
  have hC3 : ((q : ℝ) - 1) / (6 * Real.log q) * (Real.log N) ^ 3 =
      A * ((Real.log N) ^ 3 / 3) := by
    rw [hAdef]
    field_simp
    ring
  have hEq : ∑ d ∈ Finset.Icc 1 N, digitSumVal q d * Real.log d / (d : ℝ) -
        ((q : ℝ) - 1) / (6 * Real.log q) * (Real.log N) ^ 3 =
      (partialSumIcc q N * Real.log N / (N : ℝ) - A * (Real.log N) ^ 2) +
        A * ((Real.log N) ^ 2 / 2) +
        A * (∑ d ∈ Finset.Icc 1 (N - 1), Real.log d ^ 2 / ((d : ℝ) + 1) - (Real.log N) ^ 3 / 3) +
        -(A * (∑ d ∈ Finset.Icc 1 (N - 1), (d : ℝ) * Real.log d *
          (Real.log ((d : ℝ) + 1) - Real.log d) / ((d : ℝ) + 1) - (Real.log N) ^ 2 / 2)) +
          ∑ d ∈ Finset.Icc 1 (N - 1), e d *
            (Real.log d / (d : ℝ) - Real.log ((d : ℝ) + 1) / ((d : ℝ) + 1)) := by
    rw [hId, hSub, hC3]
    ring
  have hTri : |∑ d ∈ Finset.Icc 1 N, digitSumVal q d * Real.log d / (d : ℝ) -
        ((q : ℝ) - 1) / (6 * Real.log q) * (Real.log N) ^ 3| ≤
      |partialSumIcc q N * Real.log N / (N : ℝ) - A * (Real.log N) ^ 2| +
        |A * ((Real.log N) ^ 2 / 2)| +
        |A * (∑ d ∈ Finset.Icc 1 (N - 1), Real.log d ^ 2 / ((d : ℝ) + 1) - (Real.log N) ^ 3 / 3)| +
        (|A * (∑ d ∈ Finset.Icc 1 (N - 1), (d : ℝ) * Real.log d *
          (Real.log ((d : ℝ) + 1) - Real.log d) / ((d : ℝ) + 1) - (Real.log N) ^ 2 / 2)| +
          |∑ d ∈ Finset.Icc 1 (N - 1), e d *
            (Real.log d / (d : ℝ) - Real.log ((d : ℝ) + 1) / ((d : ℝ) + 1))|) := by
    rw [hEq]
    calc |(partialSumIcc q N * Real.log N / (N : ℝ) - A * (Real.log N) ^ 2) +
          A * ((Real.log N) ^ 2 / 2) +
          A * (∑ d ∈ Finset.Icc 1 (N - 1), Real.log d ^ 2 / ((d : ℝ) + 1) - (Real.log N) ^ 3 / 3) +
          -(A * (∑ d ∈ Finset.Icc 1 (N - 1), (d : ℝ) * Real.log d *
            (Real.log ((d : ℝ) + 1) - Real.log d) / ((d : ℝ) + 1) - (Real.log N) ^ 2 / 2)) +
          ∑ d ∈ Finset.Icc 1 (N - 1), e d *
            (Real.log d / (d : ℝ) - Real.log ((d : ℝ) + 1) / ((d : ℝ) + 1))|
        ≤ |(partialSumIcc q N * Real.log N / (N : ℝ) - A * (Real.log N) ^ 2) +
          A * ((Real.log N) ^ 2 / 2) +
          A * (∑ d ∈ Finset.Icc 1 (N - 1), Real.log d ^ 2 / ((d : ℝ) + 1) - (Real.log N) ^ 3 / 3) +
          -(A * (∑ d ∈ Finset.Icc 1 (N - 1), (d : ℝ) * Real.log d *
            (Real.log ((d : ℝ) + 1) - Real.log d) / ((d : ℝ) + 1) - (Real.log N) ^ 2 / 2))| +
          |∑ d ∈ Finset.Icc 1 (N - 1), e d *
            (Real.log d / (d : ℝ) - Real.log ((d : ℝ) + 1) / ((d : ℝ) + 1))| :=
          abs_add_le _ _
      _ ≤ (|partialSumIcc q N * Real.log N / (N : ℝ) - A * (Real.log N) ^ 2| +
          |A * ((Real.log N) ^ 2 / 2)| +
          |A * (∑ d ∈ Finset.Icc 1 (N - 1), Real.log d ^ 2 / ((d : ℝ) + 1) -
            (Real.log N) ^ 3 / 3)| +
          |-(A * (∑ d ∈ Finset.Icc 1 (N - 1), (d : ℝ) * Real.log d *
            (Real.log ((d : ℝ) + 1) - Real.log d) / ((d : ℝ) + 1) - (Real.log N) ^ 2 / 2))|) +
          |∑ d ∈ Finset.Icc 1 (N - 1), e d *
            (Real.log d / (d : ℝ) - Real.log ((d : ℝ) + 1) / ((d : ℝ) + 1))| := by
          gcongr
          exact abs_le_add_four _ _ _ _
      _ = |partialSumIcc q N * Real.log N / (N : ℝ) - A * (Real.log N) ^ 2| +
          |A * ((Real.log N) ^ 2 / 2)| +
          |A * (∑ d ∈ Finset.Icc 1 (N - 1), Real.log d ^ 2 / ((d : ℝ) + 1) -
            (Real.log N) ^ 3 / 3)| +
          (|A * (∑ d ∈ Finset.Icc 1 (N - 1), (d : ℝ) * Real.log d *
            (Real.log ((d : ℝ) + 1) - Real.log d) / ((d : ℝ) + 1) - (Real.log N) ^ 2 / 2)| +
            |∑ d ∈ Finset.Icc 1 (N - 1), e d *
              (Real.log d / (d : ℝ) - Real.log ((d : ℝ) + 1) / ((d : ℝ) + 1))|) := by
          rw [abs_neg]
          ring
  have hsq : (1 + Real.log N) ^ 2 ≤ 2 * (1 + (Real.log N) ^ 2) := by
    nlinarith only [sq_nonneg (Real.log N - 1)]
  have hBnd : |partialSumIcc q N * Real.log N / (N : ℝ) - A * (Real.log N) ^ 2| ≤
      (K + 2 * C1) * (1 + (Real.log N) ^ 2) := by
    calc |partialSumIcc q N * Real.log N / (N : ℝ) - A * (Real.log N) ^ 2|
        ≤ K * Real.log N + C1 * (1 + Real.log N) * Real.log N := hBoundary
      _ ≤ K * (1 + (Real.log N) ^ 2) + 2 * C1 * (1 + (Real.log N) ^ 2) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left
              (show Real.log N ≤ 1 + (Real.log N) ^ 2 by
                nlinarith only [sq_nonneg (Real.log N - 1), hlognonneg])
              hK_nonneg
          · calc C1 * (1 + Real.log N) * Real.log N
                = C1 * ((1 + Real.log N) * Real.log N) := by ring
              _ ≤ C1 * (2 * (1 + (Real.log N) ^ 2)) :=
                mul_le_mul_of_nonneg_left (by
                  nlinarith only [sq_nonneg (Real.log N - 1), hlognonneg]) hC1_nonneg
              _ = 2 * C1 * (1 + (Real.log N) ^ 2) := by ring
      _ = (K + 2 * C1) * (1 + (Real.log N) ^ 2) := by ring
  have hHalf : |A * ((Real.log N) ^ 2 / 2)| ≤ (A / 2) * (1 + (Real.log N) ^ 2) := by
    rw [abs_mul, abs_of_nonneg hA_nonneg,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Real.log N) ^ 2 / 2)]
    calc A * ((Real.log N) ^ 2 / 2) ≤ A * ((1 + (Real.log N) ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left (by linarith [sq_nonneg (Real.log N)]) hA_nonneg
      _ = (A / 2) * (1 + (Real.log N) ^ 2) := by ring
  have hAP1 : |A * (∑ d ∈ Finset.Icc 1 (N - 1), Real.log d ^ 2 / ((d : ℝ) + 1) -
      (Real.log N) ^ 3 / 3)| ≤ A * (26 + H8b) * (1 + (Real.log N) ^ 2) := by
    rw [abs_mul, abs_of_nonneg hA_nonneg]
    calc A * |∑ d ∈ Finset.Icc 1 (N - 1), Real.log d ^ 2 / ((d : ℝ) + 1) - (Real.log N) ^ 3 / 3|
        ≤ A * ((26 + H8b) * (1 + (Real.log N) ^ 2)) :=
          mul_le_mul_of_nonneg_left (by
            nlinarith only [hP1bound, hH8b_nonneg, hlognonneg, sq_nonneg (5 * Real.log N - 1),
              mul_nonneg hH8b_nonneg (sq_nonneg (Real.log N))]) hA_nonneg
      _ = A * (26 + H8b) * (1 + (Real.log N) ^ 2) := by ring
  have hAP2 : |A * (∑ d ∈ Finset.Icc 1 (N - 1), (d : ℝ) * Real.log d *
      (Real.log ((d : ℝ) + 1) - Real.log d) / ((d : ℝ) + 1) - (Real.log N) ^ 2 / 2)| ≤
      A * (28 + H8) * (1 + (Real.log N) ^ 2) := by
    rw [abs_mul, abs_of_nonneg hA_nonneg]
    calc A * |∑ d ∈ Finset.Icc 1 (N - 1), (d : ℝ) * Real.log d *
          (Real.log ((d : ℝ) + 1) - Real.log d) / ((d : ℝ) + 1) - (Real.log N) ^ 2 / 2|
        ≤ A * ((28 + H8) * (1 + (Real.log N) ^ 2)) :=
          mul_le_mul_of_nonneg_left (by
            nlinarith only [hP2bound, hH8_nonneg, hlognonneg, sq_nonneg (Real.log N - 1),
              mul_nonneg hH8_nonneg (sq_nonneg (Real.log N))]) hA_nonneg
      _ = A * (28 + H8) * (1 + (Real.log N) ^ 2) := by ring
  have hE2c : |∑ d ∈ Finset.Icc 1 (N - 1), e d *
        (Real.log d / (d : ℝ) - Real.log ((d : ℝ) + 1) / ((d : ℝ) + 1))| ≤
      (44 * K + 2 * C1) * (1 + (Real.log N) ^ 2) := by
    calc |∑ d ∈ Finset.Icc 1 (N - 1), e d *
          (Real.log d / (d : ℝ) - Real.log ((d : ℝ) + 1) / ((d : ℝ) + 1))|
        ≤ K * (1 + Real.log N) * (20 + 2 * Real.log N) + C1 * (1 + Real.log N) ^ 2 := hE2bound
      _ ≤ 44 * K * (1 + (Real.log N) ^ 2) + 2 * C1 * (1 + (Real.log N) ^ 2) := by
          apply add_le_add
          · calc K * (1 + Real.log N) * (20 + 2 * Real.log N)
                = K * ((1 + Real.log N) * (20 + 2 * Real.log N)) := by ring
              _ ≤ K * (22 * (1 + Real.log N) ^ 2) :=
                  mul_le_mul_of_nonneg_left (by
                    nlinarith only [mul_nonneg (show (0 : ℝ) ≤ 1 + Real.log N by linarith)
                      hlognonneg]) hK_nonneg
              _ ≤ K * (22 * (2 * (1 + (Real.log N) ^ 2))) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq (by norm_num)) hK_nonneg
              _ = 44 * K * (1 + (Real.log N) ^ 2) := by ring
          · calc C1 * (1 + Real.log N) ^ 2 ≤ C1 * (2 * (1 + (Real.log N) ^ 2)) :=
                mul_le_mul_of_nonneg_left hsq hC1_nonneg
              _ = 2 * C1 * (1 + (Real.log N) ^ 2) := by ring
      _ = (44 * K + 2 * C1) * (1 + (Real.log N) ^ 2) := by ring
  have hY : (K + 2 * C1) * (1 + (Real.log N) ^ 2) + (A / 2) * (1 + (Real.log N) ^ 2) +
      A * (26 + H8b) * (1 + (Real.log N) ^ 2) + A * (28 + H8) * (1 + (Real.log N) ^ 2) +
      (44 * K + 2 * C1) * (1 + (Real.log N) ^ 2) =
      ((K + 2 * C1) + A / 2 + A * (26 + H8b) + A * (28 + H8) + 44 * K + 2 * C1) *
        (1 + (Real.log N) ^ 2) := by ring
  linarith [hTri, hBnd, hHalf, hAP1, hAP2, hE2c, hY]

/-- Swapping the Dirichlet convolution sum: summing $s_q * s_q$ over
$n \le N$ is the same as summing $s_q(d)$ times the partial sum up to $N/d$. -/
private theorem convolution_sum_eq (q N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ((digitSumArith q ^ 2) n : ℝ) =
      ∑ d ∈ Finset.Icc 1 N, digitSumVal q d * partialSumIcc q (N / d) := by
  have hterm : ∀ n ∈ Finset.Icc 1 N, ((digitSumArith q ^ 2) n : ℝ) =
      ∑ x ∈ n.divisorsAntidiagonal, digitSumVal q x.1 * digitSumVal q x.2 := by
    intro n _
    rw [digitSumArith_sq_apply]
    simp [digitSumVal]
  rw [Finset.sum_congr rfl hterm]
  have hsigma := Finset.sum_sigma' (Finset.Icc 1 N) (fun n => n.divisorsAntidiagonal)
    (fun n x => digitSumVal q x.1 * digitSumVal q x.2)
  rw [hsigma]
  have hbij : ∑ x ∈ (Finset.Icc 1 N).sigma (fun n => n.divisorsAntidiagonal),
        digitSumVal q x.snd.fst * digitSumVal q x.snd.snd =
      ∑ p ∈ Finset.filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ N)
          (Finset.Icc 1 N ×ˢ Finset.Icc 1 N),
        digitSumVal q p.1 * digitSumVal q p.2 := by
    refine Finset.sum_bij'
      (i := fun (a : Σ _ : ℕ, ℕ × ℕ)
        (_ : a ∈ (Finset.Icc 1 N).sigma (fun n => n.divisorsAntidiagonal)) => a.snd)
      (j := fun (p : ℕ × ℕ)
        (_ : p ∈ Finset.filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ N)
          (Finset.Icc 1 N ×ˢ Finset.Icc 1 N)) => ⟨p.1 * p.2, p⟩) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      have hn : a.fst ∈ Finset.Icc 1 N := (Finset.mem_sigma.mp ha).1
      have hx : a.snd ∈ a.fst.divisorsAntidiagonal := (Finset.mem_sigma.mp ha).2
      rw [Nat.mem_divisorsAntidiagonal] at hx
      have h1 : 1 ≤ a.snd.fst := by
        rcases Nat.eq_zero_or_pos a.snd.fst with h | h
        · have hx0 : (0 : ℕ) = a.1 := by rw [← hx.1, h, Nat.zero_mul]
          exact (hx.2 hx0.symm).elim
        · exact h
      have h2 : 1 ≤ a.snd.snd := by
        rcases Nat.eq_zero_or_pos a.snd.snd with h | h
        · have hx0 : (0 : ℕ) = a.1 := by rw [← hx.1, h, Nat.mul_zero]
          exact (hx.2 hx0.symm).elim
        · exact h
      have hle1 : a.snd.fst ≤ N := by
        calc a.snd.fst ≤ a.snd.fst * a.snd.snd := Nat.le_mul_of_pos_right _ h2
          _ = a.1 := hx.1
          _ ≤ N := (Finset.mem_Icc.mp hn).2
      have hle2 : a.snd.snd ≤ N := by
        calc a.snd.snd ≤ a.snd.fst * a.snd.snd := Nat.le_mul_of_pos_left _ h1
          _ = a.1 := hx.1
          _ ≤ N := (Finset.mem_Icc.mp hn).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨h1, hle1⟩,
        Finset.mem_Icc.mpr ⟨h2, hle2⟩⟩, ?_⟩
      rw [hx.1]
      exact (Finset.mem_Icc.mp hn).2
    · intro p hp
      have hp1 : p ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N := (Finset.mem_filter.mp hp).1
      have hle : p.1 * p.2 ≤ N := (Finset.mem_filter.mp hp).2
      have h1a : 1 ≤ p.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp hp1).1).1
      have h2a : 1 ≤ p.2 := (Finset.mem_Icc.mp (Finset.mem_product.mp hp1).2).1
      have h1 : 1 ≤ p.1 * p.2 := by
        calc 1 = 1 * 1 := (mul_one 1).symm
          _ ≤ p.1 * p.2 := Nat.mul_le_mul h1a h2a
      refine Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨h1, hle⟩, ?_⟩
      rw [Nat.mem_divisorsAntidiagonal]
      exact ⟨rfl, Nat.mul_ne_zero (by omega) (by omega)⟩
    · intro a ha
      obtain ⟨n, x⟩ := a
      have hx : x ∈ n.divisorsAntidiagonal := (Finset.mem_sigma.mp ha).2
      rw [Nat.mem_divisorsAntidiagonal] at hx
      exact Sigma.ext hx.1 HEq.rfl
    · intro p _
      rfl
    · intro a _
      rfl
  rw [hbij, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro d hd
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have hdpos : 0 < d := hd1
  have hfilter : (Finset.Icc 1 N).filter (fun e => d * e ≤ N) = Finset.Icc 1 (N / d) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, _⟩, hle⟩
      refine ⟨h1, ?_⟩
      rw [Nat.le_div_iff_mul_le hdpos]
      rw [mul_comm]
      exact hle
    · rintro ⟨h1, hle⟩
      have hle2 : e * d ≤ N := by
        rw [Nat.le_div_iff_mul_le hdpos] at hle
        exact hle
      have hleN : e ≤ N := le_trans (Nat.le_mul_of_pos_right e hdpos) hle2
      exact ⟨⟨h1, hleN⟩, by rw [mul_comm]; exact hle2⟩
  have hsum : ∑ e ∈ Finset.Icc 1 N, (if d * e ≤ N then digitSumVal q d * digitSumVal q e else 0) =
      ∑ e ∈ Finset.Icc 1 (N / d), digitSumVal q d * digitSumVal q e := by
    rw [← Finset.sum_filter, hfilter]
  rw [hsum]
  change ∑ e ∈ Finset.Icc 1 (N / d), digitSumVal q d * digitSumVal q e =
    digitSumVal q d * (∑ e ∈ Finset.Icc 1 (N / d), digitSumVal q e)
  rw [Finset.mul_sum]

/-- The integer form of the main estimate: for $N \ge 8$, the convolution
partial sum is within $O(N \log^2 N)$ of $\frac{(q-1)^2}{24 \log^2 q} N \log^3 N$. -/
private theorem convolution_bound (q : ℕ) (hq : 2 ≤ q) :
    ∃ Cb : ℝ, ∀ N : ℕ, 8 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, ((digitSumArith q ^ 2) n : ℝ) -
        ((q : ℝ) - 1) ^ 2 / (24 * Real.log q ^ 2) * (N : ℝ) * (Real.log N) ^ 3| ≤
        Cb * (N : ℝ) * (1 + Real.log N) ^ 2 := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogqpos : 0 < Real.log q := Real.log_pos (by linarith)
  have hlogqne : Real.log q ≠ 0 := ne_of_gt hlogqpos
  obtain ⟨CU, hU⟩ := reciprocal_sum_bound q hq
  obtain ⟨CV, hV⟩ := logWeighted_sum_bound q hq
  set A : ℝ := ((q : ℝ) - 1) / (2 * Real.log q) with hAdef
  set K : ℝ := 4 * (q : ℝ) ^ 2 with hKdef
  set C1 : ℝ := K + 2 * A with hC1def
  set B : ℝ := ((q : ℝ) - 1) / (4 * Real.log q) with hBdef
  set C3 : ℝ := ((q : ℝ) - 1) / (6 * Real.log q) with hC3def
  have hA_nonneg : 0 ≤ A := by
    rw [hAdef]
    exact div_nonneg (by linarith) (by linarith [hlogqpos])
  have hB_nonneg : 0 ≤ B := by
    rw [hBdef]
    exact div_nonneg (by linarith) (by linarith [hlogqpos])
  have hK_nonneg : 0 ≤ K := by rw [hKdef]; positivity
  have hC1_nonneg : 0 ≤ C1 := by rw [hC1def]; linarith
  have hCU0 : 0 ≤ CU := by
    have h := hU 8 (by norm_num)
    have hpos : (0 : ℝ) < 1 + Real.log 8 := by
      linarith [digitSumArith_sq_partialSum_isBigO.log_eight_gt]
    have h0 : (0 : ℝ) ≤ CU * (1 + Real.log 8) := le_trans (abs_nonneg _) h
    exact (mul_nonneg_iff_of_pos_right hpos).mp h0
  have hCV0 : 0 ≤ CV := by
    have h := hV 8 (by norm_num)
    have hpos : (0 : ℝ) < 1 + (Real.log 8) ^ 2 := by
      have h2 : (0 : ℝ) ≤ (Real.log 8) ^ 2 := sq_nonneg _
      linarith [digitSumArith_sq_partialSum_isBigO.log_eight_gt]
    have h0 : (0 : ℝ) ≤ CV * (1 + (Real.log 8) ^ 2) := le_trans (abs_nonneg _) h
    exact (mul_nonneg_iff_of_pos_right hpos).mp h0
  set e : ℕ → ℝ := fun d => partialSumIcc q d - A * (d : ℝ) * Real.log d with hedef
  have herr : ∀ d : ℕ, 1 ≤ d → |e d| ≤ K * (d : ℝ) + C1 * (1 + Real.log d) := by
    intro d hd
    have h := partialSumIcc_bound q hq d hd
    rw [← hAdef, ← hKdef, ← hC1def] at h
    have he : e d = partialSumIcc q d - A * (d : ℝ) * Real.log d := by simp [hedef]
    rw [he]
    exact h
  refine ⟨(K * B + K * CU) + (C1 + 2 * A) * (A + K + C1) + A * (CU + CV),
    fun N hN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hlognonneg : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN1)
  have hNpos : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  set L : ℝ := Real.log N with hLdef
  have hA2 : A * (B - C3) = ((q : ℝ) - 1) ^ 2 / (24 * Real.log q ^ 2) := by
    rw [hAdef, hBdef, hC3def]
    field_simp
    ring
  -- The per-divisor approximation of the inner partial sum.
  have hSdiv : ∀ d ∈ Finset.Icc 1 N,
      |partialSumIcc q (N / d) - A * ((N : ℝ) / (d : ℝ)) * Real.log ((N : ℝ) / (d : ℝ))| ≤
        K * ((N : ℝ) / (d : ℝ)) + (C1 * (1 + L) + A * (2 + L)) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdN : d ≤ N := (Finset.mem_Icc.mp hd).2
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (Nat.pos_of_ne_zero (by omega))
    set m := N / d with hmdef
    have hm1 : 1 ≤ m := by
      rw [hmdef, Nat.le_div_iff_mul_le (by omega : 0 < d)]
      simpa using hdN
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (Nat.pos_of_ne_zero (by omega))
    set y : ℝ := (N : ℝ) / (d : ℝ) with hydef
    have hm_le : (m : ℝ) ≤ y := by
      rw [hydef, le_div_iff₀ hdpos]
      have h := Nat.div_mul_le_self N d
      have h2 : ((m : ℕ) : ℝ) * (d : ℝ) ≤ (N : ℝ) := by
        rw [hmdef]
        exact_mod_cast h
      calc (m : ℝ) * (d : ℝ) ≤ (N : ℝ) := h2
        _ = (N : ℝ) := rfl
    have hy_lt : y < (m : ℝ) + 1 := by
      have hltN : N < (m + 1) * d := by
        have hmod : N % d < d := Nat.mod_lt _ (by omega)
        have hdecomp : N = m * d + N % d := by
          rw [hmdef, mul_comm (N / d) d]
          exact (Nat.div_add_mod N d).symm
        have h2 : (m + 1) * d = m * d + d := by ring
        omega
      have h2 : (N : ℝ) < ((m + 1 : ℕ) : ℝ) * (d : ℝ) := by exact_mod_cast hltN
      rw [hydef, div_lt_iff₀ hdpos]
      have h3 : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      rw [h3] at h2
      linarith
    have hlogdiff : 0 ≤ Real.log y - Real.log m ∧ Real.log y - Real.log m ≤ 1 := by
      have hlogeq : Real.log y - Real.log m = Real.log (y / (m : ℝ)) := by
        rw [Real.log_div (ne_of_gt (by positivity : (0 : ℝ) < y)) (ne_of_gt hmpos)]
      have hge : (1 : ℝ) ≤ y / (m : ℝ) := by
        rw [le_div_iff₀ hmpos]
        simpa using hm_le
      have hnonneg : 0 ≤ Real.log (y / (m : ℝ)) := Real.log_nonneg hge
      have hle : Real.log (y / (m : ℝ)) ≤ 1 := by
        have h1 : Real.log (y / (m : ℝ)) ≤ y / (m : ℝ) - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
        have h2 : y / (m : ℝ) - 1 ≤ 1 / (m : ℝ) := by
          have h3 : y - (m : ℝ) ≤ 1 := by linarith [hy_lt]
          have h4 : (y - (m : ℝ)) / (m : ℝ) ≤ 1 / (m : ℝ) :=
            div_le_div_of_nonneg_right h3 (le_of_lt hmpos)
          have h5 : y / (m : ℝ) - 1 = (y - (m : ℝ)) / (m : ℝ) := by
            field_simp
          rw [h5]
          exact h4
        have h3 : (1 : ℝ) / (m : ℝ) ≤ 1 := by
          rw [div_le_one hmpos]
          exact_mod_cast hm1
        linarith
      rw [hlogeq]
      exact ⟨hnonneg, hle⟩
    have hlogdiff2 : Real.log y - Real.log m ≤ 1 / (m : ℝ) := by
      have hlogeq2 : Real.log y - Real.log m = Real.log (y / (m : ℝ)) := by
        rw [Real.log_div (ne_of_gt (by positivity : (0 : ℝ) < y)) (ne_of_gt hmpos)]
      rw [hlogeq2]
      have h1 : Real.log (y / (m : ℝ)) ≤ y / (m : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have h2 : y / (m : ℝ) - 1 ≤ 1 / (m : ℝ) := by
        have h3 : y - (m : ℝ) ≤ 1 := by linarith [hy_lt]
        have h4 : (y - (m : ℝ)) / (m : ℝ) ≤ 1 / (m : ℝ) :=
          div_le_div_of_nonneg_right h3 (le_of_lt hmpos)
        have h5 : y / (m : ℝ) - 1 = (y - (m : ℝ)) / (m : ℝ) := by
          field_simp
        rw [h5]
        exact h4
      exact le_trans h1 h2
    have hlogm : Real.log (m : ℝ) ≤ L := by
      rw [hLdef]
      apply Real.log_le_log hmpos
      exact_mod_cast (Nat.div_le_self N d)
    have hdiff : |A * (m : ℝ) * Real.log m - A * y * Real.log y| ≤ A * (2 + L) := by
      have hnonneg : 0 ≤ y * Real.log y - (m : ℝ) * Real.log m := by
        have hmono : (m : ℝ) * Real.log m ≤ y * Real.log y :=
          mul_le_mul hm_le (Real.log_le_log hmpos hm_le)
            (Real.log_nonneg (by exact_mod_cast hm1 : (1 : ℝ) ≤ (m : ℝ)))
            (by linarith [hm_le, hmpos] : (0 : ℝ) ≤ y)
        linarith
      have hle : y * Real.log y - (m : ℝ) * Real.log m ≤ 2 + L := by
        have h1 : y * Real.log y - (m : ℝ) * Real.log m =
            y * (Real.log y - Real.log m) + (y - (m : ℝ)) * Real.log m := by ring
        rw [h1]
        have h2 : y * (Real.log y - Real.log m) ≤ 2 := by
          have h3 : y * (Real.log y - Real.log m) ≤ y * (1 / (m : ℝ)) :=
            mul_le_mul_of_nonneg_left hlogdiff2 (le_of_lt (by positivity : (0 : ℝ) < y))
          have h4 : y * (1 / (m : ℝ)) = y / (m : ℝ) := mul_one_div _ _
          have h5 : y / (m : ℝ) ≤ 2 := by
            have h6 : y < (m : ℝ) + 1 := hy_lt
            have h7 : y / (m : ℝ) < ((m : ℝ) + 1) / (m : ℝ) :=
              div_lt_div_of_pos_right h6 hmpos
            have h8 : ((m : ℝ) + 1) / (m : ℝ) = 1 + 1 / (m : ℝ) := by
              field_simp
            rw [h8] at h7
            have h9 : (1 : ℝ) / (m : ℝ) ≤ 1 := by
              rw [div_le_one hmpos]
              exact_mod_cast hm1
            linarith
          rw [h4] at h3
          exact le_trans h3 h5
        have h5 : (y - (m : ℝ)) * Real.log m ≤ 1 * L := by
          apply mul_le_mul (by linarith [hy_lt]) hlogm (Real.log_nonneg (by
            exact_mod_cast hm1 : (1 : ℝ) ≤ (m : ℝ))) (by linarith)
        linarith
      have hEq2 : |A * (m : ℝ) * Real.log m - A * y * Real.log y| =
          A * (y * Real.log y - (m : ℝ) * Real.log m) := by
        rw [show A * (m : ℝ) * Real.log m - A * y * Real.log y =
            -(A * (y * Real.log y - (m : ℝ) * Real.log m)) by ring, abs_neg,
          abs_of_nonneg (mul_nonneg hA_nonneg hnonneg)]
      rw [hEq2]
      exact mul_le_mul_of_nonneg_left hle hA_nonneg
    have hmain : |partialSumIcc q m - A * (m : ℝ) * Real.log m| ≤
        K * (m : ℝ) + C1 * (1 + Real.log m) := by
      have h := herr m hm1
      have he : e m = partialSumIcc q m - A * (m : ℝ) * Real.log m := by simp [hedef]
      rw [he] at h
      exact h
    have hsum : |partialSumIcc q m - A * y * Real.log y| ≤
        K * y + (C1 * (1 + L) + A * (2 + L)) := by
      have hEq : partialSumIcc q m - A * y * Real.log y =
          (partialSumIcc q m - A * (m : ℝ) * Real.log m) +
            (A * (m : ℝ) * Real.log m - A * y * Real.log y) := by ring
      rw [hEq]
      calc |(partialSumIcc q m - A * (m : ℝ) * Real.log m) +
            (A * (m : ℝ) * Real.log m - A * y * Real.log y)|
          ≤ |partialSumIcc q m - A * (m : ℝ) * Real.log m| +
            |A * (m : ℝ) * Real.log m - A * y * Real.log y| := abs_add_le _ _
        _ ≤ (K * (m : ℝ) + C1 * (1 + Real.log m)) + A * (2 + L) :=
            add_le_add hmain hdiff
        _ ≤ K * y + (C1 * (1 + L) + A * (2 + L)) := by
            have h1 : K * (m : ℝ) ≤ K * y :=
              mul_le_mul_of_nonneg_left hm_le hK_nonneg
            have h2 : C1 * (1 + Real.log m) ≤ C1 * (1 + L) :=
              mul_le_mul_of_nonneg_left (by linarith) hC1_nonneg
            linarith
    rw [hmdef] at hsum ⊢
    have hy_eq : y = (N : ℝ) / (d : ℝ) := rfl
    rw [hy_eq] at hsum
    exact hsum
  -- The main identity and error estimates.
  set UU : ℝ := ∑ d ∈ Finset.Icc 1 N, digitSumVal q d / (d : ℝ) with hUUdef
  set VV : ℝ := ∑ d ∈ Finset.Icc 1 N, digitSumVal q d * Real.log d / (d : ℝ) with hVVdef
  set SS : ℝ := partialSumIcc q N with hSSdef
  have hUapp := hU N hN1
  rw [← hLdef] at hUapp
  have hVapp := hV N hN1
  rw [← hLdef] at hVapp
  have hUle : UU ≤ B * L ^ 2 + CU * (1 + L) := by
    have h := (abs_le.mp hUapp).2
    linarith
  have hVle : VV ≤ C3 * L ^ 3 + CV * (1 + L ^ 2) := by
    have h := (abs_le.mp hVapp).2
    linarith
  have hSle : SS ≤ A * (N : ℝ) * L + K * (N : ℝ) + C1 * (1 + L) := by
    have h := herr N hN1
    rw [← hLdef] at h
    have he : e N = SS - A * (N : ℝ) * L := by simp only [hedef, hSSdef, ← hLdef]
    rw [he] at h
    have h2 := (abs_le.mp h).2
    linarith
  have hSSnonneg : 0 ≤ SS := Finset.sum_nonneg (fun d _ => Nat.cast_nonneg _)
  have hlogdiv : ∀ d ∈ Finset.Icc 1 N,
      Real.log ((N : ℝ) / (d : ℝ)) = L - Real.log (d : ℝ) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdpos : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [Real.log_div (by positivity : (N : ℝ) ≠ 0) hdpos, hLdef]
  have hsumA : ∑ d ∈ Finset.Icc 1 N, digitSumVal q d *
        (A * ((N : ℝ) / (d : ℝ)) * Real.log ((N : ℝ) / (d : ℝ))) =
      A * (N : ℝ) * (L * UU - VV) := by
    have hper : ∀ d ∈ Finset.Icc 1 N, digitSumVal q d *
          (A * ((N : ℝ) / (d : ℝ)) * Real.log ((N : ℝ) / (d : ℝ))) =
        A * (N : ℝ) * (digitSumVal q d / (d : ℝ) * (L - Real.log (d : ℝ))) := by
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hdpos : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      rw [hlogdiv d hd]
      field_simp
    rw [Finset.sum_congr rfl hper, ← Finset.mul_sum]
    congr 1
    have hUV : ∑ d ∈ Finset.Icc 1 N, digitSumVal q d / (d : ℝ) * (L - Real.log (d : ℝ)) =
        L * UU - VV := by
      rw [Finset.sum_congr rfl (fun d _ => mul_sub _ _ _), Finset.sum_sub_distrib]
      congr 1
      · rw [hUUdef, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        rw [mul_comm]
      · rw [hVVdef]
        apply Finset.sum_congr rfl
        intro d _
        rw [div_mul_eq_mul_div]
    rw [hUV]
  have hErrEq : (∑ d ∈ Finset.Icc 1 N, digitSumVal q d *
        (partialSumIcc q (N / d) - A * ((N : ℝ) / (d : ℝ)) * Real.log ((N : ℝ) / (d : ℝ)))) =
      (∑ n ∈ Finset.Icc 1 N, ((digitSumArith q ^ 2) n : ℝ)) -
        A * (N : ℝ) * (L * UU - VV) := by
    rw [convolution_sum_eq]
    rw [Finset.sum_congr rfl (fun d hd => mul_sub _ _ _), Finset.sum_sub_distrib, hsumA]
  have hMainEq : (∑ n ∈ Finset.Icc 1 N, ((digitSumArith q ^ 2) n : ℝ)) -
        ((q : ℝ) - 1) ^ 2 / (24 * Real.log q ^ 2) * (N : ℝ) * L ^ 3 =
      (∑ d ∈ Finset.Icc 1 N, digitSumVal q d *
        (partialSumIcc q (N / d) - A * ((N : ℝ) / (d : ℝ)) * Real.log ((N : ℝ) / (d : ℝ)))) +
        A * (N : ℝ) * (L * (UU - B * L ^ 2) - (VV - C3 * L ^ 3)) := by
    rw [hErrEq, ← hA2]
    ring
  have hErr : |(∑ d ∈ Finset.Icc 1 N, digitSumVal q d *
        (partialSumIcc q (N / d) - A * ((N : ℝ) / (d : ℝ)) * Real.log ((N : ℝ) / (d : ℝ))))| ≤
      K * (N : ℝ) * UU + (C1 * (1 + L) + A * (2 + L)) * SS := by
    calc |(∑ d ∈ Finset.Icc 1 N, digitSumVal q d *
          (partialSumIcc q (N / d) - A * ((N : ℝ) / (d : ℝ)) * Real.log ((N : ℝ) / (d : ℝ))))|
        ≤ ∑ d ∈ Finset.Icc 1 N, |digitSumVal q d *
            (partialSumIcc q (N / d) - A * ((N : ℝ) / (d : ℝ)) * Real.log ((N : ℝ) / (d : ℝ)))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ d ∈ Finset.Icc 1 N, digitSumVal q d *
            |partialSumIcc q (N / d) - A * ((N : ℝ) / (d : ℝ)) * Real.log ((N : ℝ) / (d : ℝ))| := by
          apply Finset.sum_congr rfl
          intro d _
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      _ ≤ ∑ d ∈ Finset.Icc 1 N, digitSumVal q d *
            (K * ((N : ℝ) / (d : ℝ)) + (C1 * (1 + L) + A * (2 + L))) :=
          Finset.sum_le_sum (fun d hd => mul_le_mul_of_nonneg_left (hSdiv d hd)
            (Nat.cast_nonneg _))
      _ = K * (N : ℝ) * UU + (C1 * (1 + L) + A * (2 + L)) * SS := by
          rw [Finset.sum_congr rfl (fun d _ => mul_add _ _ _), Finset.sum_add_distrib]
          congr 1
          · have h1 : ∀ d ∈ Finset.Icc 1 N, digitSumVal q d * (K * ((N : ℝ) / (d : ℝ))) =
                K * (N : ℝ) * (digitSumVal q d / (d : ℝ)) := by
              intro d hd
              have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
              have hdpos : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
              field_simp
            rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, ← hUUdef]
          · have hSS' : ∑ d ∈ Finset.Icc 1 N, digitSumVal q d = partialSumIcc q N := rfl
            rw [Finset.sum_congr rfl (fun d _ => mul_comm _ _), ← Finset.mul_sum, hSS',
              ← hSSdef]
  have hErr1 : K * (N : ℝ) * UU ≤ (K * B + K * CU) * (N : ℝ) * (1 + L) ^ 2 := by
    have h1 : K * (N : ℝ) * UU ≤ K * (N : ℝ) * (B * L ^ 2 + CU * (1 + L)) :=
      mul_le_mul_of_nonneg_left hUle (mul_nonneg hK_nonneg (Nat.cast_nonneg N))
    have h2 : L ^ 2 ≤ (1 + L) ^ 2 :=
      pow_le_pow_left₀ hlognonneg (by linarith) 2
    have h3 : (1 : ℝ) + L ≤ (1 + L) ^ 2 := by
      have h4 : (0 : ℝ) ≤ L ^ 2 := sq_nonneg _
      nlinarith only [sq_nonneg L, hlognonneg]
    calc K * (N : ℝ) * UU ≤ K * (N : ℝ) * (B * L ^ 2 + CU * (1 + L)) := h1
      _ ≤ K * (N : ℝ) * (B * (1 + L) ^ 2 + CU * (1 + L) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK_nonneg (Nat.cast_nonneg N))
          exact add_le_add (mul_le_mul_of_nonneg_left h2 hB_nonneg)
            (mul_le_mul_of_nonneg_left h3 hCU0)
      _ = (K * B + K * CU) * (N : ℝ) * (1 + L) ^ 2 := by ring
  have hErr2 : (C1 * (1 + L) + A * (2 + L)) * SS ≤
      (C1 + 2 * A) * (A + K + C1) * (N : ℝ) * (1 + L) ^ 2 := by
    have hF1 : C1 * (1 + L) + A * (2 + L) ≤ (C1 + 2 * A) * (1 + L) := by
      have h : A * (2 + L) ≤ 2 * A * (1 + L) := by
        calc A * (2 + L) ≤ A * (2 * (1 + L)) :=
              mul_le_mul_of_nonneg_left (by linarith) hA_nonneg
          _ = 2 * A * (1 + L) := by ring
      linarith
    have hS1 : SS ≤ (N : ℝ) * ((A + K + C1) * (1 + L)) := by
      calc SS ≤ A * (N : ℝ) * L + K * (N : ℝ) + C1 * (1 + L) := hSle
        _ ≤ A * (N : ℝ) * (1 + L) + K * (N : ℝ) * (1 + L) + C1 * (1 + L) * (N : ℝ) := by
            have h1 : A * (N : ℝ) * L ≤ A * (N : ℝ) * (1 + L) :=
              mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hA_nonneg (Nat.cast_nonneg N))
            have h2 : K * (N : ℝ) ≤ K * (N : ℝ) * (1 + L) :=
              le_mul_of_one_le_right (mul_nonneg hK_nonneg (Nat.cast_nonneg N)) (by linarith)
            have h3 : C1 * (1 + L) ≤ C1 * (1 + L) * (N : ℝ) :=
              le_mul_of_one_le_right (mul_nonneg hC1_nonneg (by linarith))
                (by exact_mod_cast hN1)
            linarith
        _ = (N : ℝ) * ((A + K + C1) * (1 + L)) := by ring
    calc (C1 * (1 + L) + A * (2 + L)) * SS ≤
        ((C1 + 2 * A) * (1 + L)) * ((N : ℝ) * ((A + K + C1) * (1 + L))) :=
          mul_le_mul hF1 hS1 hSSnonneg (by positivity)
      _ = (C1 + 2 * A) * (A + K + C1) * (N : ℝ) * (1 + L) ^ 2 := by ring
  have hMain2 : A * (N : ℝ) * (L * |UU - B * L ^ 2| + |VV - C3 * L ^ 3|) ≤
      A * (CU + CV) * (N : ℝ) * (1 + L) ^ 2 := by
    have hu : |UU - B * L ^ 2| ≤ CU * (1 + L) := by rw [hUUdef]; exact hUapp
    have hv : |VV - C3 * L ^ 3| ≤ CV * (1 + L ^ 2) := by rw [hVVdef]; exact hVapp
    have h1 : L * |UU - B * L ^ 2| ≤ CU * (1 + L) ^ 2 := by
      calc L * |UU - B * L ^ 2| ≤ L * (CU * (1 + L)) :=
            mul_le_mul_of_nonneg_left hu hlognonneg
        _ ≤ (1 + L) * (CU * (1 + L)) := by
            apply mul_le_mul_of_nonneg_right _ (mul_nonneg hCU0 (by linarith))
            linarith
        _ = CU * (1 + L) ^ 2 := by ring
    have h2 : |VV - C3 * L ^ 3| ≤ CV * (1 + L) ^ 2 := by
      calc |VV - C3 * L ^ 3| ≤ CV * (1 + L ^ 2) := hv
        _ ≤ CV * (1 + L) ^ 2 :=
            mul_le_mul_of_nonneg_left (by linarith only [hlognonneg]) hCV0
    calc A * (N : ℝ) * (L * |UU - B * L ^ 2| + |VV - C3 * L ^ 3|)
        ≤ A * (N : ℝ) * (CU * (1 + L) ^ 2 + CV * (1 + L) ^ 2) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2) (mul_nonneg hA_nonneg (Nat.cast_nonneg N))
      _ = A * (CU + CV) * (N : ℝ) * (1 + L) ^ 2 := by ring
  have hTri : |(∑ n ∈ Finset.Icc 1 N, ((digitSumArith q ^ 2) n : ℝ)) -
        ((q : ℝ) - 1) ^ 2 / (24 * Real.log q ^ 2) * (N : ℝ) * L ^ 3| ≤
      |(∑ d ∈ Finset.Icc 1 N, digitSumVal q d *
        (partialSumIcc q (N / d) - A * ((N : ℝ) / (d : ℝ)) * Real.log ((N : ℝ) / (d : ℝ))))| +
        A * (N : ℝ) * (L * |UU - B * L ^ 2| + |VV - C3 * L ^ 3|) := by
    have hAbs : |(∑ d ∈ Finset.Icc 1 N, digitSumVal q d *
        (partialSumIcc q (N / d) - A * ((N : ℝ) / (d : ℝ)) * Real.log ((N : ℝ) / (d : ℝ)))) +
        A * (N : ℝ) * (L * (UU - B * L ^ 2) - (VV - C3 * L ^ 3))| ≤
        |(∑ d ∈ Finset.Icc 1 N, digitSumVal q d *
        (partialSumIcc q (N / d) - A * ((N : ℝ) / (d : ℝ)) * Real.log ((N : ℝ) / (d : ℝ))))| +
        |A * (N : ℝ) * (L * (UU - B * L ^ 2) - (VV - C3 * L ^ 3))| := abs_add_le _ _
    have hAbs2 : |A * (N : ℝ) * (L * (UU - B * L ^ 2) - (VV - C3 * L ^ 3))| ≤
        A * (N : ℝ) * (L * |UU - B * L ^ 2| + |VV - C3 * L ^ 3|) := by
      have h1 : |L * (UU - B * L ^ 2) - (VV - C3 * L ^ 3)| ≤
          L * |UU - B * L ^ 2| + |VV - C3 * L ^ 3| := by
        calc |L * (UU - B * L ^ 2) - (VV - C3 * L ^ 3)|
            ≤ |L * (UU - B * L ^ 2)| + |VV - C3 * L ^ 3| := abs_sub _ _
          _ = L * |UU - B * L ^ 2| + |VV - C3 * L ^ 3| := by
              rw [abs_mul, abs_of_nonneg hlognonneg]
      calc |A * (N : ℝ) * (L * (UU - B * L ^ 2) - (VV - C3 * L ^ 3))|
          = A * (N : ℝ) * |L * (UU - B * L ^ 2) - (VV - C3 * L ^ 3)| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hA_nonneg,
              abs_of_nonneg (Nat.cast_nonneg N)]
        _ ≤ A * (N : ℝ) * (L * |UU - B * L ^ 2| + |VV - C3 * L ^ 3|) :=
            mul_le_mul_of_nonneg_left h1 (mul_nonneg hA_nonneg (Nat.cast_nonneg N))
    rw [hMainEq]
    exact le_trans hAbs (add_le_add le_rfl hAbs2)
  have hY : (K * B + K * CU) * (N : ℝ) * (1 + L) ^ 2 +
      (C1 + 2 * A) * (A + K + C1) * (N : ℝ) * (1 + L) ^ 2 +
      A * (CU + CV) * (N : ℝ) * (1 + L) ^ 2 =
      ((K * B + K * CU) + (C1 + 2 * A) * (A + K + C1) + A * (CU + CV)) *
        (N : ℝ) * (1 + L) ^ 2 := by ring
  have hErr : |(∑ d ∈ Finset.Icc 1 N, digitSumVal q d *
        (partialSumIcc q (N / d) - A * ((N : ℝ) / (d : ℝ)) * Real.log ((N : ℝ) / (d : ℝ))))| ≤
      (K * B + K * CU) * (N : ℝ) * (1 + L) ^ 2 +
        (C1 + 2 * A) * (A + K + C1) * (N : ℝ) * (1 + L) ^ 2 := by
    calc |(∑ d ∈ Finset.Icc 1 N, digitSumVal q d *
          (partialSumIcc q (N / d) - A * ((N : ℝ) / (d : ℝ)) * Real.log ((N : ℝ) / (d : ℝ))))|
        ≤ K * (N : ℝ) * UU + (C1 * (1 + L) + A * (2 + L)) * SS := hErr
      _ ≤ (K * B + K * CU) * (N : ℝ) * (1 + L) ^ 2 +
          (C1 + 2 * A) * (A + K + C1) * (N : ℝ) * (1 + L) ^ 2 := by
          exact add_le_add hErr1 hErr2
  linarith only [hTri, hErr, hMain2, hY]

end digitSumArith_sq_partialSum_isBigO

open Filter Asymptotics Real

/-- **Partial sums of the second digit-sum convolution.** Let $q \ge 2$ be an integer, let
$s_q(n)$ be the sum of the base-$q$ digits of $n$, and let $s_q^{(2)} = s_q * s_q$ be its
Dirichlet square, so $s_q^{(2)}(n) = \sum_{de = n} s_q(d) \, s_q(e)$. Then
$$\sum_{1 \le n \le x} s_q^{(2)}(n) = \frac{(q - 1)^2}{24 \log^2 q} \, x \log^3 x + O(x \log^2 x)$$
as $x \to \infty$ through the reals.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Theorem 2 (`integers-2026-A43-thm-2`). -/
theorem digitSumArith_sq_partialSum_isBigO (q : ℕ) (hq : 2 ≤ q) :
    (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((digitSumArith q ^ 2) n : ℝ) -
        ((q : ℝ) - 1) ^ 2 * x * log x ^ 3 / (24 * log q ^ 2)) =O[atTop]
      (fun x => x * log x ^ 2) := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogqpos : 0 < Real.log q := Real.log_pos (by linarith)
  have hlogqne : Real.log q ≠ 0 := ne_of_gt hlogqpos
  obtain ⟨Cb, hCb⟩ := digitSumArith_sq_partialSum_isBigO.convolution_bound q hq
  set A2 : ℝ := ((q : ℝ) - 1) ^ 2 / (24 * Real.log q ^ 2) with hA2def
  have hA2_nonneg : 0 ≤ A2 := by
    rw [hA2def]
    exact div_nonneg (sq_nonneg _) (by positivity)
  have hCb0 : 0 ≤ Cb := by
    have h := hCb 8 (by norm_num)
    push_cast at h
    have hpos : (0 : ℝ) < 8 * (1 + Real.log 8) ^ 2 := by
      have h1 : (0 : ℝ) < 1 + Real.log 8 := by
        linarith [digitSumArith_sq_partialSum_isBigO.log_eight_gt]
      exact mul_pos (by norm_num) (pow_pos h1 2)
    have hle : (0 : ℝ) ≤ Cb * 8 * (1 + Real.log 8) ^ 2 := le_trans (abs_nonneg _) h
    have h0 : (0 : ℝ) ≤ (8 * (1 + Real.log 8) ^ 2) * Cb := by linarith [hle]
    exact nonneg_of_mul_nonneg_right h0 hpos
  have hterm : ∀ x : ℝ, ((q : ℝ) - 1) ^ 2 * x * log x ^ 3 / (24 * log q ^ 2) =
      A2 * x * (log x) ^ 3 := by
    intro x
    rw [hA2def]
    field_simp
  have hreal : ∀ x : ℝ, 8 ≤ x →
      |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((digitSumArith q ^ 2) n : ℝ) -
        ((q : ℝ) - 1) ^ 2 * x * log x ^ 3 / (24 * log q ^ 2)| ≤
        (3 * Cb + 2 * A2) * (x * (log x) ^ 2) := by
    intro x hx
    set N := ⌊x⌋₊ with hNdef
    have hx0 : (0 : ℝ) ≤ x := by linarith
    have hN8 : 8 ≤ N := (Nat.le_floor_iff hx0).mpr (by exact_mod_cast hx)
    have hNle : (N : ℝ) ≤ x := Nat.floor_le hx0
    have hlt : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hlogN : Real.log (N : ℝ) ≤ Real.log x := Real.log_le_log hNpos hNle
    have hlogx : (2 : ℝ) < Real.log x := by
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 8) hx
      linarith [digitSumArith_sq_partialSum_isBigO.log_eight_gt]
    have hlogNnonneg : 0 ≤ Real.log (N : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
    rw [hterm x]
    have hdiff : |A2 * (N : ℝ) * (Real.log N) ^ 3 - A2 * x * (Real.log x) ^ 3| ≤
        A2 * ((Real.log x) ^ 3 + 3 * (Real.log x) ^ 2) := by
      have hmono : (N : ℝ) * (Real.log N) ^ 3 ≤ x * (Real.log x) ^ 3 :=
        mul_le_mul hNle (pow_le_pow_left₀ hlogNnonneg hlogN 3) (by positivity)
          (by linarith : (0 : ℝ) ≤ x)
      have hle : x * (Real.log x) ^ 3 - (N : ℝ) * (Real.log N) ^ 3 ≤
          (Real.log x) ^ 3 + 3 * (Real.log x) ^ 2 := by
        have h1 : x * (Real.log x) ^ 3 - (N : ℝ) * (Real.log N) ^ 3 =
            (x - (N : ℝ)) * (Real.log x) ^ 3 +
              (N : ℝ) * ((Real.log x) ^ 3 - (Real.log N) ^ 3) := by ring
        rw [h1]
        have h2 : (x - (N : ℝ)) * (Real.log x) ^ 3 ≤ (Real.log x) ^ 3 := by
          calc (x - (N : ℝ)) * (Real.log x) ^ 3 ≤ 1 * (Real.log x) ^ 3 :=
                mul_le_mul_of_nonneg_right (by linarith) (by positivity)
            _ = (Real.log x) ^ 3 := one_mul _
        have h3 : (N : ℝ) * ((Real.log x) ^ 3 - (Real.log N) ^ 3) ≤ 3 * (Real.log x) ^ 2 := by
          have hdiff3 : (Real.log x) ^ 3 - (Real.log N) ^ 3 =
              (Real.log x - Real.log N) *
                ((Real.log x) ^ 2 + Real.log x * Real.log N + (Real.log N) ^ 2) := by ring
          rw [hdiff3]
          have hlogdiff : Real.log x - Real.log N = Real.log (x / (N : ℝ)) := by
            rw [Real.log_div (by positivity : x ≠ 0) (ne_of_gt hNpos)]
          have hle1 : Real.log (x / (N : ℝ)) ≤ 1 / (N : ℝ) := by
            have h1' : Real.log (x / (N : ℝ)) ≤ x / (N : ℝ) - 1 :=
              Real.log_le_sub_one_of_pos (by positivity)
            have h2' : x / (N : ℝ) - 1 ≤ 1 / (N : ℝ) := by
              have h3' : x - (N : ℝ) ≤ 1 := by linarith
              have h4' : (x - (N : ℝ)) / (N : ℝ) ≤ 1 / (N : ℝ) :=
                div_le_div_of_nonneg_right h3' (le_of_lt hNpos)
              have h5' : x / (N : ℝ) - 1 = (x - (N : ℝ)) / (N : ℝ) := by
                field_simp
              rw [h5']
              exact h4'
            linarith
          have hprod : (N : ℝ) * (Real.log x - Real.log N) ≤ 1 := by
            rw [hlogdiff]
            have h1' := mul_le_mul_of_nonneg_left hle1 (le_of_lt hNpos)
            rwa [mul_div_cancel₀ _ (ne_of_gt hNpos)] at h1'
          have hfac : (Real.log x) ^ 2 + Real.log x * Real.log N + (Real.log N) ^ 2 ≤
              3 * (Real.log x) ^ 2 := by
            have ha : Real.log x * Real.log N ≤ (Real.log x) ^ 2 := by
              calc Real.log x * Real.log N ≤ Real.log x * Real.log x :=
                    mul_le_mul_of_nonneg_left hlogN (by linarith : (0 : ℝ) ≤ Real.log x)
                _ = (Real.log x) ^ 2 := by ring
            have hb : (Real.log N) ^ 2 ≤ (Real.log x) ^ 2 :=
              pow_le_pow_left₀ hlogNnonneg hlogN 2
            linarith
          calc (N : ℝ) * ((Real.log x - Real.log N) *
                ((Real.log x) ^ 2 + Real.log x * Real.log N + (Real.log N) ^ 2))
              = ((N : ℝ) * (Real.log x - Real.log N)) *
                ((Real.log x) ^ 2 + Real.log x * Real.log N + (Real.log N) ^ 2) := by ring
            _ ≤ 1 * (3 * (Real.log x) ^ 2) :=
                mul_le_mul hprod hfac (by positivity) (by norm_num)
            _ = 3 * (Real.log x) ^ 2 := one_mul _
        linarith
      calc |A2 * (N : ℝ) * (Real.log N) ^ 3 - A2 * x * (Real.log x) ^ 3|
          = |A2 * ((N : ℝ) * (Real.log N) ^ 3 - x * (Real.log x) ^ 3)| := by
            congr 1
            ring
        _ = A2 * (x * (Real.log x) ^ 3 - (N : ℝ) * (Real.log N) ^ 3) := by
            rw [show A2 * ((N : ℝ) * (Real.log N) ^ 3 - x * (Real.log x) ^ 3) =
                -(A2 * (x * (Real.log x) ^ 3 - (N : ℝ) * (Real.log N) ^ 3)) by ring,
              abs_neg, abs_of_nonneg (mul_nonneg hA2_nonneg (by linarith))]
        _ ≤ A2 * ((Real.log x) ^ 3 + 3 * (Real.log x) ^ 2) :=
            mul_le_mul_of_nonneg_left hle hA2_nonneg
    have hstep : |∑ n ∈ Finset.Icc 1 N, ((digitSumArith q ^ 2) n : ℝ) - A2 * x * (Real.log x) ^ 3| ≤
        |∑ n ∈ Finset.Icc 1 N, ((digitSumArith q ^ 2) n : ℝ) - A2 * (N : ℝ) * (Real.log N) ^ 3| +
          |A2 * (N : ℝ) * (Real.log N) ^ 3 - A2 * x * (Real.log x) ^ 3| := by
      have h := abs_add_le (∑ n ∈ Finset.Icc 1 N, ((digitSumArith q ^ 2) n : ℝ) -
        A2 * (N : ℝ) * (Real.log N) ^ 3)
        (A2 * (N : ℝ) * (Real.log N) ^ 3 - A2 * x * (Real.log x) ^ 3)
      have heq : (∑ n ∈ Finset.Icc 1 N, ((digitSumArith q ^ 2) n : ℝ) -
        A2 * (N : ℝ) * (Real.log N) ^ 3) +
        (A2 * (N : ℝ) * (Real.log N) ^ 3 - A2 * x * (Real.log x) ^ 3) =
        ∑ n ∈ Finset.Icc 1 N, ((digitSumArith q ^ 2) n : ℝ) - A2 * x * (Real.log x) ^ 3 := by
        ring
      rwa [heq] at h
    have h1 : |∑ n ∈ Finset.Icc 1 N, ((digitSumArith q ^ 2) n : ℝ) -
        A2 * (N : ℝ) * (Real.log N) ^ 3| ≤ Cb * (N : ℝ) * (1 + Real.log N) ^ 2 := by
      have h2 := hCb N hN8
      exact h2
    calc |∑ n ∈ Finset.Icc 1 N, ((digitSumArith q ^ 2) n : ℝ) - A2 * x * (Real.log x) ^ 3|
        ≤ |∑ n ∈ Finset.Icc 1 N, ((digitSumArith q ^ 2) n : ℝ) -
            A2 * (N : ℝ) * (Real.log N) ^ 3| + A2 * ((Real.log x) ^ 3 + 3 * (Real.log x) ^ 2) :=
          le_trans hstep (add_le_add le_rfl hdiff)
      _ ≤ Cb * (N : ℝ) * (1 + Real.log N) ^ 2 + A2 * ((Real.log x) ^ 3 + 3 * (Real.log x) ^ 2) :=
          add_le_add h1 le_rfl
      _ ≤ (3 * Cb + 2 * A2) * (x * (Real.log x) ^ 2) := by
          have h1' : Cb * (N : ℝ) * (1 + Real.log N) ^ 2 ≤
              Cb * (x * (Real.log x) ^ 2) * (9 / 4) := by
            have hsq : (1 + Real.log N) ^ 2 ≤ ((3 : ℝ) / 2 * Real.log x) ^ 2 := by
              apply pow_le_pow_left₀ (by linarith) _ 2
              linarith [hlogN, hlogx]
            have h2 : (N : ℝ) * (1 + Real.log N) ^ 2 ≤ x * ((3 : ℝ) / 2 * Real.log x) ^ 2 :=
              mul_le_mul hNle hsq (by positivity) (by positivity)
            calc Cb * (N : ℝ) * (1 + Real.log N) ^ 2
                = Cb * ((N : ℝ) * (1 + Real.log N) ^ 2) := by ring
              _ ≤ Cb * (x * ((3 : ℝ) / 2 * Real.log x) ^ 2) :=
                  mul_le_mul_of_nonneg_left h2 hCb0
              _ = Cb * (x * (Real.log x) ^ 2) * (9 / 4) := by ring
          have h2 : A2 * ((Real.log x) ^ 3 + 3 * (Real.log x) ^ 2) ≤
              2 * A2 * (x * (Real.log x) ^ 2) := by
            have h3 : (Real.log x) ^ 3 + 3 * (Real.log x) ^ 2 ≤
                2 * (x * (Real.log x) ^ 2) := by
              have hle : Real.log x ≤ x := Real.log_le_self (le_of_lt (by linarith : (0 : ℝ) < x))
              have hfac : (0 : ℝ) ≤ (2 * x - Real.log x - 3) * (Real.log x) ^ 2 :=
                mul_nonneg (by linarith [hle, hx]) (sq_nonneg _)
              linarith [hfac]
            calc A2 * ((Real.log x) ^ 3 + 3 * (Real.log x) ^ 2) ≤
                  A2 * (2 * (x * (Real.log x) ^ 2)) :=
                    mul_le_mul_of_nonneg_left h3 hA2_nonneg
              _ = 2 * A2 * (x * (Real.log x) ^ 2) := by ring
          nlinarith [h1', h2, hCb0, hA2_nonneg, hlogx,
            mul_nonneg hCb0 (mul_nonneg (by linarith : (0 : ℝ) ≤ x) (sq_nonneg (Real.log x)))]
  refine Asymptotics.IsBigO.of_bound (3 * Cb + 2 * A2) ?_
  rw [Filter.eventually_atTop]
  refine ⟨8, fun x hx => ?_⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have hgx : (0 : ℝ) ≤ x * (log x) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  rw [abs_of_nonneg hgx]
  have h := hreal x hx
  rw [hterm x] at h
  rw [hterm x]
  exact h

end

end MetaMathlibExt
