/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Mazur's Scottish Book Problem 88 fails

`mazur88_refuted` shows that the Scottish Book Problem 88 claim is false: a dyadic
Rudin–Shapiro witness satisfies the Hankel summability hypothesis but not the weighted
summability conclusion.
-/

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook88Wanted

/-- **Scottish Book Problem 88 (Mazur).** The claim that every real sequence $(a_n)_{n \ge 0}$
with the following property satisfies $\sum_n n |a_n| < \infty$: for every real sequence
$(x_n)_{n \ge 0}$ with $|x_n| \le 1$ for all $n$, each series $\sum_n a_{m+n} x_n$ with $m \ge 0$
converges, as the limit of its partial sums, to some $L_m$, and $\sum_m |L_m| < \infty$.

The inner series is required to converge as a limit of partial sums, not absolutely, as in
Mazur's original question. -/
def ScottishBookProblem88Claim : Prop :=
  ∀ a : ℕ → ℝ,
    (∀ x : ℕ → ℝ, (∀ n, |x n| ≤ 1) →
      ∃ L : ℕ → ℝ,
        (∀ m, Filter.Tendsto
          (fun N => ∑ n ∈ Finset.range N, a (m + n) * x n)
          Filter.atTop (nhds (L m))) ∧
        Summable (fun m => |L m|)) →
    Summable (fun n : ℕ => (n : ℝ) * |a n|)

open Finset Filter
open scoped Topology

private def signs : ℕ → Bool → ℕ → ℝ
  | 0, _, _ => 1
  | m + 1, b, j =>
    if j < 2 ^ m then signs m false j
    else if b then -signs m true (j - 2 ^ m) else signs m true (j - 2 ^ m)

private lemma abs_signs (m : ℕ) (b : Bool) (j : ℕ) : |signs m b j| = 1 := by
  induction m generalizing b j with
  | zero => simp [signs]
  | succ m ih => cases b <;> simp [signs, apply_ite abs, ih]

private noncomputable def blockSum (m : ℕ) (b : Bool) (f : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ range (2 ^ m), signs m b j * f (i + j)

private lemma blockSum_succ (m : ℕ) (b : Bool) (f : ℕ → ℝ) (i : ℕ) :
    blockSum (m + 1) b f i = blockSum m false f i +
      (if b then -blockSum m true f (i + 2 ^ m) else blockSum m true f (i + 2 ^ m)) := by
  unfold blockSum
  rw [pow_succ, Nat.mul_two, sum_range_add]
  congr 1
  · apply sum_congr rfl
    intro j hj
    simp [signs, mem_range.mp hj]
  · cases b <;> simp [signs, add_assoc, sum_neg_distrib]

private lemma energy_le (f : ℕ → ℝ) {B : ℝ} (hf : ∀ i, f i ^ 2 ≤ B) (m R : ℕ) :
    (∑ i ∈ range R, (blockSum m false f i ^ 2 + blockSum m true f i ^ 2)) ≤
      2 * (2 : ℝ) ^ m * (R + (2 : ℝ) ^ m) * B := by
  have hB := (sq_nonneg (f 0)).trans (hf 0)
  induction m generalizing R with
  | zero =>
    simp only [blockSum, pow_zero, sum_range_one, signs, Nat.add_zero, one_mul]
    calc
      _ ≤ ∑ _ ∈ range R, (B + B) := sum_le_sum fun i _ => add_le_add (hf i) (hf i)
      _ ≤ _ := by simp; nlinarith
  | succ m ih =>
    let N := 2 ^ m
    let P := blockSum m false f
    let Q := blockSum m true f
    have hP : (∑ i ∈ range R, P i ^ 2) ≤ ∑ i ∈ range (R + N), P i ^ 2 :=
      sum_le_sum_of_subset_of_nonneg (range_mono (Nat.le_add_right R N)) (fun i _ _ => sq_nonneg _)
    have hQ : (∑ i ∈ range R, Q (i + N) ^ 2) ≤ ∑ i ∈ range (R + N), Q i ^ 2 := by
      rw [Nat.add_comm R N, sum_range_add]
      have h₀ : 0 ≤ ∑ i ∈ range N, Q i ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
      simpa [Nat.add_comm] using le_add_of_nonneg_left
        (a := ∑ i ∈ range R, Q (N + i) ^ 2) h₀
    calc
      _ = 2 * ((∑ i ∈ range R, P i ^ 2) + ∑ i ∈ range R, Q (i + N) ^ 2) := by
        rw [← sum_add_distrib, mul_sum]
        apply sum_congr rfl
        intro i _
        simp [blockSum_succ, P, Q, N]
        ring
      _ ≤ 2 * ∑ i ∈ range (R + N), (P i ^ 2 + Q i ^ 2) := by
        rw [sum_add_distrib]
        linarith
      _ ≤ _ := by
        have h := ih (R + N)
        dsimp [N] at h ⊢
        push_cast at h
        rw [pow_succ]
        dsimp [P, Q]
        linarith

-- tail sums
private noncomputable def tailSum (m : ℕ) (b : Bool) (f : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ t ∈ range (2 ^ m - i), signs m b (t + i) * f t

private lemma tailSum_succ_lt {m : ℕ} {f : ℕ → ℝ} {i : ℕ} (hi : i < 2 ^ m) :
    tailSum (m + 1) false f i = tailSum m false f i + blockSum m true f (2 ^ m - i) := by
  have hpow : (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
  have hsplit : 2 ^ (m + 1) - i = (2 ^ m - i) + 2 ^ m := by omega
  unfold tailSum blockSum
  rw [hsplit, sum_range_add]
  congr 1
  · apply sum_congr rfl
    intro t ht
    have ht' := mem_range.mp ht
    have hlt : t + i < 2 ^ m := by omega
    simp [signs, hlt]
  · apply sum_congr rfl
    intro t ht
    have harg : (2 ^ m - i) + t + i = 2 ^ m + t := by omega
    rw [harg, add_comm (2 ^ m - i) t]
    simp [signs]

private lemma tailSum_succ_true_lt {m : ℕ} {f : ℕ → ℝ} {i : ℕ} (hi : i < 2 ^ m) :
    tailSum (m + 1) true f i = tailSum m false f i - blockSum m true f (2 ^ m - i) := by
  have hsplit : 2 ^ (m + 1) - i = (2 ^ m - i) + 2 ^ m := by omega
  unfold tailSum blockSum
  rw [hsplit, sum_range_add]
  congr 1
  · apply sum_congr rfl
    intro t ht
    have ht' := mem_range.mp ht
    have hlt : t + i < 2 ^ m := by omega
    simp [signs, hlt]
  · rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro t ht
    have harg : (2 ^ m - i) + t + i = 2 ^ m + t := by omega
    rw [harg, add_comm (2 ^ m - i) t]
    simp [signs]

private lemma tailSum_succ_ge {m : ℕ} {b : Bool} {f : ℕ → ℝ} {i : ℕ} (hi : i < 2 ^ m) :
    tailSum (m + 1) b f (2 ^ m + i) = (if b then -1 else 1) * tailSum m true f i := by
  have hsplit : 2 ^ (m + 1) - (2 ^ m + i) = 2 ^ m - i := by omega
  unfold tailSum
  rw [hsplit, mul_sum]
  apply sum_congr rfl
  intro t ht
  have harg : t + (2 ^ m + i) = 2 ^ m + (t + i) := by omega
  rw [harg]
  cases b <;> simp [signs]

private lemma tail_energy (f : ℕ → ℝ) {B : ℝ} (hf : ∀ i, f i ^ 2 ≤ B) (m : ℕ) :
    (∑ i ∈ range (2 ^ m), (tailSum m false f i ^ 2 + tailSum m true f i ^ 2)) ≤
      6 * (4 : ℝ) ^ m * B := by
  have hB : 0 ≤ B := (sq_nonneg (f 0)).trans (hf 0)
  induction m with
  | zero =>
    have h0 : tailSum 0 false f 0 = f 0 := by simp [tailSum, signs]
    have h1 : tailSum 0 true f 0 = f 0 := by simp [tailSum, signs]
    simp only [pow_zero, range_one, sum_singleton]
    rw [h0, h1]
    nlinarith [hf 0]
  | succ m ih =>
    set N := 2 ^ m with hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_two_pow
    have hNm : (N : ℝ) = (2 : ℝ) ^ m := by exact_mod_cast hN
    have hNsq : (N : ℝ) ^ 2 = (4 : ℝ) ^ m := by
      rw [hNm, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
      congr 1; ring
    have hpow : (2 : ℕ) ^ (m + 1) = N + N := by rw [hN, pow_succ]; ring
    rw [hpow, sum_range_add]
    have hfirst : ∀ i ∈ range N, tailSum (m + 1) false f i ^ 2 +
        tailSum (m + 1) true f i ^ 2 =
        2 * ((tailSum m false f i) ^ 2 + (blockSum m true f (N - i)) ^ 2) := by
      intro i hi
      have hi' : i < 2 ^ m := by rw [← hN]; exact mem_range.mp hi
      rw [tailSum_succ_lt hi', tailSum_succ_true_lt hi']
      ring
    have hsecond : ∀ i ∈ range N, tailSum (m + 1) false f (N + i) ^ 2 +
        tailSum (m + 1) true f (N + i) ^ 2 = 2 * (tailSum m true f i) ^ 2 := by
      intro i hi
      have hi' : i < 2 ^ m := by rw [← hN]; exact mem_range.mp hi
      rw [tailSum_succ_ge (b := false) hi', tailSum_succ_ge (b := true) hi']
      simp; ring
    rw [sum_congr rfl hfirst, sum_congr rfl hsecond,
      ← Finset.mul_sum, ← Finset.mul_sum, ← mul_add]
    have hsq : ∑ i ∈ range N, (blockSum m true f (N - i)) ^ 2 ≤
        ∑ j ∈ range (N + 1), (blockSum m false f j ^ 2 + blockSum m true f j ^ 2) := by
      have hreflect : ∑ i ∈ range N, (blockSum m true f (N - i)) ^ 2 =
          ∑ i ∈ range N, (blockSum m true f (i + 1)) ^ 2 := by
        rw [← sum_range_reflect (fun i => (blockSum m true f (i + 1)) ^ 2) N]
        apply sum_congr rfl
        intro i hi
        have hi' := mem_range.mp hi
        congr 2
        omega
      rw [hreflect]
      have hle : ∑ i ∈ range N, (blockSum m true f (i + 1)) ^ 2 ≤
          ∑ i ∈ range N, (blockSum m false f (i + 1) ^ 2 + blockSum m true f (i + 1) ^ 2) :=
        sum_le_sum fun i _ => le_add_of_nonneg_left (sq_nonneg _)
      have hsucc := sum_range_succ' (fun j => blockSum m false f j ^ 2 + blockSum m true f j ^ 2) N
      have hnn : 0 ≤ blockSum m false f 0 ^ 2 + blockSum m true f 0 ^ 2 :=
        add_nonneg (sq_nonneg _) (sq_nonneg _)
      linarith
    have henergy := energy_le f hf m (N + 1)
    have henergy' : (∑ j ∈ range (N + 1), (blockSum m false f j ^ 2 + blockSum m true f j ^ 2)) ≤
        6 * (4 : ℝ) ^ m * B := by
      apply henergy.trans
      have hcast : ((N + 1 : ℕ) : ℝ) + (2 : ℝ) ^ m = 2 * N + 1 := by push_cast; rw [hNm]; ring
      rw [hcast, ← hNm]
      nlinarith [hN1, hNsq, hB, mul_nonneg (mul_nonneg
        (show (0:ℝ) ≤ (N:ℝ) by positivity)
        (show (0:ℝ) ≤ (N:ℝ) - 1 by linarith)) hB]
    have hAB : (∑ i ∈ range N, ((tailSum m false f i) ^ 2 + (blockSum m true f (N - i)) ^ 2)) +
        (∑ i ∈ range N, (tailSum m true f i) ^ 2) =
        (∑ i ∈ range N, (tailSum m false f i ^ 2 + tailSum m true f i ^ 2)) +
        (∑ i ∈ range N, (blockSum m true f (N - i)) ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      ring
    have h4 : (4 : ℝ) ^ (m + 1) = 4 * (4 : ℝ) ^ m := by rw [pow_succ]; ring
    nlinarith [ih, hsq, henergy', hAB, hB, hNsq, h4]

private noncomputable def witness (n : ℕ) : ℝ :=
  if n = 0 then 0
  else (1 / 4 : ℝ) ^ (Nat.log 2 n) *
    signs (Nat.log 2 n) false (n - 2 ^ (Nat.log 2 n))

private lemma witness_eq_of_mem {k j : ℕ} (hj : j < 2 ^ k) :
    witness (2 ^ k + j) = (1 / 4 : ℝ) ^ k * signs k false j := by
  have hne : 2 ^ k + j ≠ 0 := by positivity
  have hlog : Nat.log 2 (2 ^ k + j) = k :=
    Nat.log_eq_of_pow_le_of_lt_pow (Nat.le_add_right _ _) (by rw [pow_succ]; omega)
  simp only [witness, hne, ite_false, hlog, Nat.add_sub_cancel_left]

private lemma abs_witness_of_mem {k j : ℕ} (hj : j < 2 ^ k) :
    |witness (2 ^ k + j)| = (1 / 4 : ℝ) ^ k := by
  rw [witness_eq_of_mem hj, abs_mul, abs_signs, mul_one,
    abs_of_nonneg (by positivity)]

private lemma abs_witness_le (n : ℕ) : |witness n| ≤ 4 / (n : ℝ) ^ 2 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [witness]
  · set k := Nat.log 2 n with hk
    have hlt : (n : ℝ) < 2 * (2 : ℝ) ^ k := by
      have h : (n : ℝ) < (2 : ℝ) ^ (k + 1) := by
        rw [hk]; exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) n
      rw [pow_succ] at h
      linarith
    have hpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have hsq : ((2 : ℝ) ^ k) ^ 2 = (4 : ℝ) ^ k := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]; congr 1; ring
    have hle : (n : ℝ) ^ 2 ≤ 4 * (4 : ℝ) ^ k := by
      have h := pow_lt_pow_left₀ hlt (show (0:ℝ) ≤ n by positivity) (two_ne_zero)
      rw [mul_pow] at h
      nlinarith [hsq, h, hpos]
    have h1 : (1 : ℝ) / (4 * (4 : ℝ) ^ k) ≤ 1 / (n : ℝ) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) hle
    have hw : witness n = (1 / 4 : ℝ) ^ k * signs k false (n - 2 ^ k) := by
      simp only [witness, hn, ite_false, hk]
    rw [hw, abs_mul, abs_signs, mul_one, abs_of_nonneg (by positivity)]
    have heq : (1 / 4 : ℝ) ^ k = 4 * (1 / (4 * (4 : ℝ) ^ k)) := by
      rw [one_div_pow]; field_simp
    rw [heq]
    calc 4 * (1 / (4 * (4 : ℝ) ^ k)) ≤ 4 * (1 / (n : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = 4 / (n : ℝ) ^ 2 := by ring

private lemma summable_abs_witness : Summable (fun n : ℕ => |witness n|) := by
  have hsum : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (2 : ℝ)) :=
    (Real.summable_one_div_nat_rpow).mpr (by norm_num)
  have hsum2 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := by
    have h := (Real.summable_one_div_nat_rpow (p := 2)).mpr (by norm_num)
    simpa only [Real.rpow_two] using h
  have h4 : Summable (fun n : ℕ => 4 / (n : ℝ) ^ 2) := by
    simpa [div_eq_mul_inv] using hsum2.mul_left 4
  exact Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => abs_witness_le n) h4

private lemma summable_witness_shift (m : ℕ) (x : ℕ → ℝ) (hx : ∀ n, |x n| ≤ 1) :
    Summable (fun n => witness (m + n) * x n) := by
  apply Summable.of_norm_bounded (g := fun n => |witness (n + m)|)
  · exact (summable_nat_add_iff m).mpr summable_abs_witness
  · intro n
    rw [Real.norm_eq_abs, abs_mul]
    calc |witness (m + n)| * |x n| ≤ |witness (m + n)| * 1 :=
          mul_le_mul_of_nonneg_left (hx n) (abs_nonneg _)
      _ = |witness (n + m)| := by rw [mul_one, add_comm]

private lemma sqrt_pow_eight (k : ℕ) : Real.sqrt ((8 : ℝ) ^ k) = (Real.sqrt 8) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

private lemma sqrt_bound_aux (k : ℕ) (A C D : ℝ) (hC0 : 0 ≤ C) (hA : A ≤ C * (8 : ℝ) ^ k)
    (hC : Real.sqrt C ≤ D) :
    (1 / 4 : ℝ) ^ k * Real.sqrt A ≤ D * ((Real.sqrt 2) / 2) ^ k := by
  have h8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have hr : (1 / 4 : ℝ) * Real.sqrt 8 = (Real.sqrt 2) / 2 := by rw [h8]; ring
  have hsqrt : Real.sqrt (C * (8 : ℝ) ^ k) = Real.sqrt C * (Real.sqrt 8) ^ k := by
    rw [Real.sqrt_mul hC0, sqrt_pow_eight]
  calc (1 / 4 : ℝ) ^ k * Real.sqrt A
      ≤ (1 / 4 : ℝ) ^ k * Real.sqrt (C * (8 : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hA) (by positivity)
    _ = Real.sqrt C * ((1 / 4 : ℝ) * Real.sqrt 8) ^ k := by
        rw [hsqrt, mul_pow]; ring
    _ = Real.sqrt C * ((Real.sqrt 2) / 2) ^ k := by rw [hr]
    _ ≤ D * ((Real.sqrt 2) / 2) ^ k :=
        mul_le_mul_of_nonneg_right hC (by positivity)

private noncomputable def blockContrib (k m : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range (2 ^ k),
    if m ≤ 2 ^ k + j then (1 / 4 : ℝ) ^ k * signs k false j * x (2 ^ k + j - m) else 0

private lemma blockContrib_le (k m : ℕ) (x : ℕ → ℝ) (hx : ∀ n, |x n| ≤ 1) :
    |blockContrib k m x| ≤ (1 / 2 : ℝ) ^ k := by
  unfold blockContrib
  calc |∑ j ∈ range (2 ^ k),
          (if m ≤ 2 ^ k + j then (1 / 4 : ℝ) ^ k * signs k false j *
            x (2 ^ k + j - m) else 0)|
      ≤ ∑ j ∈ range (2 ^ k),
          |(if m ≤ 2 ^ k + j then (1 / 4 : ℝ) ^ k * signs k false j *
            x (2 ^ k + j - m) else 0)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ range (2 ^ k), (1 / 4 : ℝ) ^ k := by
        apply sum_le_sum
        intro j _
        split
        · rw [abs_mul, abs_mul, abs_signs, mul_one, abs_of_nonneg (by positivity)]
          exact mul_le_of_le_one_right (by positivity) (hx _)
        · simp
    _ = (1 / 2 : ℝ) ^ k := by
        rw [sum_const, card_range, nsmul_eq_mul]; push_cast; rw [← mul_pow]; norm_num

private lemma blockContrib_eq_blockSum {k m : ℕ} (x : ℕ → ℝ) (hm : m ≤ 2 ^ k) :
    blockContrib k m x = (1 / 4 : ℝ) ^ k * blockSum k false x (2 ^ k - m) := by
  unfold blockContrib blockSum
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  rw [ite_eq_left (by omega : m ≤ 2 ^ k + j)]
  have harg : 2 ^ k + j - m = (2 ^ k - m) + j := by omega
  rw [harg]; ring

private lemma blockContrib_eq_tailSum {k i : ℕ} (x : ℕ → ℝ) (hi : i < 2 ^ k) :
    blockContrib k (2 ^ k + i) x = (1 / 4 : ℝ) ^ k * tailSum k false x i := by
  have hle : i ≤ 2 ^ k := hi.le
  have key : (∑ t ∈ range (2 ^ k - i), (1 / 4 : ℝ) ^ k * (signs k false (t + i) * x t)) =
      ∑ j ∈ range (i + (2 ^ k - i)),
        (if 2 ^ k + i ≤ 2 ^ k + j then (1 / 4 : ℝ) ^ k * signs k false j *
          x (2 ^ k + j - (2 ^ k + i)) else 0) := by
    rw [sum_range_add]
    have h1 : (∑ j ∈ range i, (if 2 ^ k + i ≤ 2 ^ k + j then (1 / 4 : ℝ) ^ k *
        signs k false j * x (2 ^ k + j - (2 ^ k + i)) else 0)) = 0 := by
      apply sum_eq_zero
      intro j hj
      rw [ite_eq_right (by have := mem_range.mp hj; omega)]
    have h2 : (∑ t ∈ range (2 ^ k - i), (if 2 ^ k + i ≤ 2 ^ k + (i + t) then
        (1 / 4 : ℝ) ^ k * signs k false (i + t) *
          x (2 ^ k + (i + t) - (2 ^ k + i)) else 0)) =
        ∑ t ∈ range (2 ^ k - i), (1 / 4 : ℝ) ^ k * (signs k false (t + i) * x t) := by
      apply sum_congr rfl
      intro t _
      rw [ite_eq_left (by omega)]
      have harg : 2 ^ k + (i + t) - (2 ^ k + i) = t := by omega
      rw [harg, add_comm i t]; ring
    rw [h1, h2, zero_add]
  rw [show i + (2 ^ k - i) = 2 ^ k from Nat.add_sub_cancel' hle] at key
  unfold tailSum
  rw [mul_sum]
  exact key.symm

private lemma blockContrib_eq_zero {k m : ℕ} (x : ℕ → ℝ) (hm : 2 ^ (k + 1) ≤ m) :
    blockContrib k m x = 0 := by
  unfold blockContrib
  apply sum_eq_zero
  intro j hj
  rw [ite_eq_right (by have := mem_range.mp hj; rw [pow_succ] at hm; omega)]

private lemma sum_abs_le_sqrt_card (s : Finset ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ s, |f i| ≤ Real.sqrt (s.card * ∑ i ∈ s, f i ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => |f i|)
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one, sq_abs] at h
  have hnn : 0 ≤ (s.card : ℝ) * ∑ i ∈ s, f i ^ 2 :=
    mul_nonneg (by positivity) (sum_nonneg fun i _ => sq_nonneg _)
  exact (Real.le_sqrt (sum_nonneg fun i _ => abs_nonneg _) hnn).mpr h

private lemma blockContrib_tsum_le (k : ℕ) (x : ℕ → ℝ) (hx : ∀ n, |x n| ≤ 1) :
    ∑' m, |blockContrib k m x| ≤ 7 * ((Real.sqrt 2) / 2) ^ k := by
  have hf1 : ∀ i, x i ^ 2 ≤ 1 := fun i => (sq_le_one_iff_abs_le_one _).mpr (hx i)
  have hsupp : ∀ m ∉ Finset.range (2 ^ (k + 1)), |blockContrib k m x| = 0 := by
    intro m hm
    rw [Finset.mem_range] at hm
    rw [blockContrib_eq_zero x (by omega), abs_zero]
  have hsum : Summable (fun m => |blockContrib k m x|) :=
    summable_of_ne_finset_zero hsupp
  rw [tsum_eq_sum hsupp]
  have hsplit : ∑ m ∈ Finset.range (2 ^ (k + 1)), |blockContrib k m x| =
      (∑ m ∈ Finset.range (2 ^ k), |blockContrib k m x|) +
      (∑ i ∈ Finset.range (2 ^ k), |blockContrib k (2 ^ k + i) x|) := by
    rw [pow_succ, Nat.mul_two, Finset.sum_range_add]
  rw [hsplit]
  set N := 2 ^ k with hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_two_pow
  have hNm : (N : ℝ) = (2 : ℝ) ^ k := by exact_mod_cast hN
  have hNsq : (N : ℝ) ^ 2 = (4 : ℝ) ^ k := by
    rw [hNm, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]; congr 1; ring
  have hN3 : (N : ℝ) ^ 3 = (8 : ℝ) ^ k := by
    rw [hNm, show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_mul]; congr 1; ring
  -- first sum: block sums
  have hS1 : (∑ m ∈ Finset.range (2 ^ k), |blockContrib k m x|) ≤
      4 * ((Real.sqrt 2) / 2) ^ k := by
    have hstep : (∑ m ∈ Finset.range (2 ^ k), |blockContrib k m x|) =
        (1 / 4 : ℝ) ^ k * (∑ m ∈ Finset.range (2 ^ k), |blockSum k false x (2 ^ k - m)|) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro m hm
      rw [blockContrib_eq_blockSum x (by have := mem_range.mp hm; omega),
        abs_mul, abs_of_nonneg (by positivity)]
    have hrefl : (∑ m ∈ Finset.range (2 ^ k), |blockSum k false x (2 ^ k - m)|) =
        ∑ m ∈ Finset.range (2 ^ k), |blockSum k false x (m + 1)| := by
      rw [← sum_range_reflect (fun i => |blockSum k false x (i + 1)|) (2 ^ k)]
      apply sum_congr rfl
      intro m hm
      have hm' := mem_range.mp hm
      congr 2
      omega
    have hle1 : (∑ m ∈ Finset.range (2 ^ k), |blockSum k false x (m + 1)|) ≤
        ∑ j ∈ Finset.range (2 ^ k + 1), |blockSum k false x j| := by
      have hsucc := sum_range_succ' (fun j => |blockSum k false x j|) (2 ^ k)
      have hle : (∑ m ∈ Finset.range (2 ^ k), |blockSum k false x (m + 1)|) ≤
          ∑ m ∈ Finset.range (2 ^ k), |blockSum k false x (m + 1)| +
            |blockSum k false x 0| := le_add_of_nonneg_right (abs_nonneg _)
      linarith
    have hsqrt := sum_abs_le_sqrt_card (Finset.range (2 ^ k + 1))
      (fun j => blockSum k false x j)
    have henergy := energy_le x hf1 k (2 ^ k + 1)
    have hbound : ((Finset.range (2 ^ k + 1)).card : ℝ) *
        (∑ j ∈ Finset.range (2 ^ k + 1), (blockSum k false x j) ^ 2) ≤ 12 * (8 : ℝ) ^ k := by
      have hcard : ((Finset.range (2 ^ k + 1)).card : ℝ) = (N : ℝ) + 1 := by
        simp [hN]
      have hsum2 : (∑ j ∈ Finset.range (2 ^ k + 1), (blockSum k false x j) ^ 2) ≤
          ∑ j ∈ Finset.range (2 ^ k + 1),
            ((blockSum k false x j) ^ 2 + (blockSum k true x j) ^ 2) :=
        sum_le_sum fun i _ => le_add_of_nonneg_right (sq_nonneg _)
      rw [hcard]
      have hcast : ((2 ^ k + 1 : ℕ) : ℝ) + (2 : ℝ) ^ k = 2 * N + 1 := by push_cast; rw [hNm]; ring
      have henergy2 : (∑ j ∈ Finset.range (2 ^ k + 1),
            ((blockSum k false x j) ^ 2 + (blockSum k true x j) ^ 2)) ≤
          2 * (N : ℝ) * (2 * N + 1) := by
        have h := henergy
        rw [hcast, ← hNm] at h
        simpa using h
      nlinarith [henergy2, hsum2, hN1, hN3, mul_nonneg (show (0:ℝ) ≤ (N:ℝ) + 1 by linarith)
        (show (0:ℝ) ≤ (∑ j ∈ Finset.range (2 ^ k + 1), (blockSum k false x j) ^ 2) from
          sum_nonneg fun i _ => sq_nonneg _)]
    have hsqrt12 : Real.sqrt 12 ≤ 4 := by
      have h : Real.sqrt 12 ≤ Real.sqrt 16 := Real.sqrt_le_sqrt (by norm_num)
      have h16 : Real.sqrt 16 = 4 := by
        rw [show (16:ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rwa [h16] at h
    calc (∑ m ∈ Finset.range (2 ^ k), |blockContrib k m x|)
        = (1 / 4 : ℝ) ^ k * (∑ m ∈ Finset.range (2 ^ k), |blockSum k false x (2 ^ k - m)|) := hstep
      _ ≤ (1 / 4 : ℝ) ^ k * (∑ j ∈ Finset.range (2 ^ k + 1), |blockSum k false x j|) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [hrefl]; exact hle1
      _ ≤ (1 / 4 : ℝ) ^ k * Real.sqrt (((Finset.range (2 ^ k + 1)).card : ℝ) *
            ∑ j ∈ Finset.range (2 ^ k + 1), (blockSum k false x j) ^ 2) := by
          apply mul_le_mul_of_nonneg_left hsqrt (by positivity)
      _ ≤ 4 * ((Real.sqrt 2) / 2) ^ k :=
          sqrt_bound_aux k _ 12 4 (by norm_num) hbound hsqrt12
  -- second sum: tail sums
  have hS2 : (∑ i ∈ Finset.range (2 ^ k), |blockContrib k (2 ^ k + i) x|) ≤
      3 * ((Real.sqrt 2) / 2) ^ k := by
    have hstep : (∑ i ∈ Finset.range (2 ^ k), |blockContrib k (2 ^ k + i) x|) =
        (1 / 4 : ℝ) ^ k * (∑ i ∈ Finset.range (2 ^ k), |tailSum k false x i|) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      rw [blockContrib_eq_tailSum x (mem_range.mp hi),
        abs_mul, abs_of_nonneg (by positivity)]
    have hsqrt := sum_abs_le_sqrt_card (Finset.range (2 ^ k)) (fun i => tailSum k false x i)
    have henergy := tail_energy x hf1 k
    have hbound : ((Finset.range (2 ^ k)).card : ℝ) *
        (∑ i ∈ Finset.range (2 ^ k), (tailSum k false x i) ^ 2) ≤ 6 * (8 : ℝ) ^ k := by
      have hcard : ((Finset.range (2 ^ k)).card : ℝ) = (N : ℝ) := by simp [hN]
      have hsum2 : (∑ i ∈ Finset.range (2 ^ k), (tailSum k false x i) ^ 2) ≤
          ∑ i ∈ Finset.range (2 ^ k),
            ((tailSum k false x i) ^ 2 + (tailSum k true x i) ^ 2) :=
        sum_le_sum fun i _ => le_add_of_nonneg_right (sq_nonneg _)
      rw [hcard]
      have heq : (N : ℝ) * (6 * (4 : ℝ) ^ k) = 6 * (8 : ℝ) ^ k := by
        rw [hNm, show (2 : ℝ) ^ k * (6 * (4 : ℝ) ^ k) = 6 * ((2 : ℝ) ^ k * (4 : ℝ) ^ k) by ring,
          ← mul_pow]; norm_num
      calc (N : ℝ) * (∑ i ∈ Finset.range (2 ^ k), (tailSum k false x i) ^ 2)
          ≤ (N : ℝ) * (6 * (4 : ℝ) ^ k) :=
            mul_le_mul_of_nonneg_left (by linarith [hsum2, henergy]) (by positivity)
        _ = 6 * (8 : ℝ) ^ k := heq
    have hsqrt6 : Real.sqrt 6 ≤ 3 := by
      have h : Real.sqrt 6 ≤ Real.sqrt 9 := Real.sqrt_le_sqrt (by norm_num)
      have h9 : Real.sqrt 9 = 3 := by
        rw [show (9:ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rwa [h9] at h
    calc (∑ i ∈ Finset.range (2 ^ k), |blockContrib k (2 ^ k + i) x|)
        = (1 / 4 : ℝ) ^ k * (∑ i ∈ Finset.range (2 ^ k), |tailSum k false x i|) := hstep
      _ ≤ (1 / 4 : ℝ) ^ k * Real.sqrt (((Finset.range (2 ^ k)).card : ℝ) *
            ∑ i ∈ Finset.range (2 ^ k), (tailSum k false x i) ^ 2) := by
          apply mul_le_mul_of_nonneg_left hsqrt (by positivity)
      _ ≤ 3 * ((Real.sqrt 2) / 2) ^ k :=
          sqrt_bound_aux k _ 6 3 (by norm_num) hbound hsqrt6
  rw [← hN] at hS1 hS2
  linarith [hS1, hS2]

private lemma dyadic_sum (F : ℕ → ℝ) (K : ℕ) :
    ∑ k ∈ range K, ∑ j ∈ range (2 ^ k), F (2 ^ k + j) = ∑ t ∈ range (2 ^ K), F t - F 0 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ, ih, pow_succ, Nat.mul_two, sum_range_add]
    ring

private lemma blockContrib_eq_sum (k m : ℕ) (x : ℕ → ℝ) :
    blockContrib k m x =
      ∑ j ∈ range (2 ^ k),
        (if m ≤ 2 ^ k + j then witness (2 ^ k + j) * x (2 ^ k + j - m) else 0) := by
  unfold blockContrib
  apply sum_congr rfl
  intro j hj
  by_cases h : m ≤ 2 ^ k + j
  · rw [ite_eq_left h, ite_eq_left h, witness_eq_of_mem (mem_range.mp hj)]
  · rw [ite_eq_right h, ite_eq_right h]

private lemma partial_block_sum (K m : ℕ) (x : ℕ → ℝ) (hm : m < 2 ^ K) :
    ∑ k ∈ range K, blockContrib k m x =
      ∑ n ∈ range (2 ^ K - m), witness (m + n) * x n := by
  set F : ℕ → ℝ := fun t => if m ≤ t then witness t * x (t - m) else 0 with hF
  have hF0 : F 0 = 0 := by
    by_cases h : m = 0
    · subst h; simp [hF, witness]
    · simp only [hF, ite_eq_right (by omega : ¬ m ≤ 0)]
  have h1 : ∑ k ∈ range K, blockContrib k m x =
      ∑ k ∈ range K, ∑ j ∈ range (2 ^ k), F (2 ^ k + j) := by
    apply sum_congr rfl
    intro k _
    rw [blockContrib_eq_sum]
  rw [h1, dyadic_sum, hF0, sub_zero]
  have hsplit : (∑ t ∈ range (2 ^ K), F t) =
      ∑ n ∈ range (2 ^ K - m), witness (m + n) * x n := by
    conv_lhs => rw [show (2 : ℕ) ^ K = m + (2 ^ K - m) by omega]
    rw [sum_range_add]
    have hz : (∑ t ∈ range m, F t) = 0 := by
      apply sum_eq_zero
      intro t ht
      rw [hF]
      exact ite_eq_right (by have := mem_range.mp ht; omega)
    rw [hz, zero_add]
    apply sum_congr rfl
    intro n _
    simp only [hF]
    rw [ite_eq_left (by omega : m ≤ m + n), Nat.add_sub_cancel_left]
  exact hsplit

private lemma summable_blockContrib (m : ℕ) (x : ℕ → ℝ) (hx : ∀ n, |x n| ≤ 1) :
    Summable (fun k => blockContrib k m x) := by
  apply Summable.of_norm_bounded
    (g := fun k => (1 / 2 : ℝ) ^ k)
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  intro k
  rw [Real.norm_eq_abs]
  exact blockContrib_le k m x hx

private lemma summable_abs_blockContrib (m : ℕ) (x : ℕ → ℝ) (hx : ∀ n, |x n| ≤ 1) :
    Summable (fun k => |blockContrib k m x|) := by
  apply Summable.of_norm_bounded
    (g := fun k => (1 / 2 : ℝ) ^ k)
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  intro k
  rw [Real.norm_eq_abs, abs_abs]
  exact blockContrib_le k m x hx

private lemma tsum_blockContrib (m : ℕ) (x : ℕ → ℝ) (hx : ∀ n, |x n| ≤ 1) :
    ∑' k, blockContrib k m x = ∑' n, witness (m + n) * x n := by
  have hB := summable_blockContrib m x hx
  have hW := summable_witness_shift m x hx
  have h1 : Filter.Tendsto (fun K => ∑ k ∈ range K, blockContrib k m x) Filter.atTop
      (nhds (∑' k, blockContrib k m x)) := hB.hasSum.tendsto_sum_nat
  have h2 : Filter.Tendsto (fun K => ∑ n ∈ range (2 ^ K - m), witness (m + n) * x n) Filter.atTop
      (nhds (∑' n, witness (m + n) * x n)) := by
    apply Filter.Tendsto.comp hW.hasSum.tendsto_sum_nat
    rw [Filter.tendsto_atTop_atTop]
    intro b
    obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (b + m : ℕ) (by norm_num : (1 : ℕ) < 2)
    refine ⟨K, fun K' hK' => ?_⟩
    have hpow : (2 : ℕ) ^ K ≤ (2 : ℕ) ^ K' := Nat.pow_le_pow_right (by norm_num) hK'
    omega
  have heq : (fun K => ∑ n ∈ range (2 ^ K - m), witness (m + n) * x n) =ᶠ[Filter.atTop]
      (fun K => ∑ k ∈ range K, blockContrib k m x) := by
    obtain ⟨K0, hK0⟩ := pow_unbounded_of_one_lt (m : ℕ) (by norm_num : (1 : ℕ) < 2)
    filter_upwards [Filter.eventually_ge_atTop K0] with K hK
    have hpow : (2 : ℕ) ^ K0 ≤ (2 : ℕ) ^ K := Nat.pow_le_pow_right (by norm_num) hK
    exact (partial_block_sum K m x (by omega)).symm
  have h3 : Filter.Tendsto (fun K => ∑ k ∈ range K, blockContrib k m x) Filter.atTop
      (nhds (∑' n, witness (m + n) * x n)) :=
    Filter.Tendsto.congr' heq h2
  exact tendsto_nhds_unique h1 h3

private lemma abs_tsum_blockContrib_le (m : ℕ) (x : ℕ → ℝ) (hx : ∀ n, |x n| ≤ 1) :
    |∑' n, witness (m + n) * x n| ≤ ∑' k, |blockContrib k m x| := by
  rw [← tsum_blockContrib m x hx]
  have hB := summable_blockContrib m x hx
  have hA := summable_abs_blockContrib m x hx
  have hf : Filter.Tendsto (fun K => |∑ k ∈ range K, blockContrib k m x|) Filter.atTop
      (nhds |∑' k, blockContrib k m x|) := hB.hasSum.tendsto_sum_nat.abs
  have hg : Filter.Tendsto (fun K => ∑ k ∈ range K, |blockContrib k m x|) Filter.atTop
      (nhds (∑' k, |blockContrib k m x|)) := hA.hasSum.tendsto_sum_nat
  have hle : (fun K => |∑ k ∈ range K, blockContrib k m x|) ≤ᶠ[Filter.atTop]
      (fun K => ∑ k ∈ range K, |blockContrib k m x|) :=
    Filter.Eventually.of_forall fun K => abs_sum_le_sum_abs _ _
  exact le_of_tendsto_of_tendsto hf hg hle

private lemma summable_abs_blockContrib_m (k : ℕ) (x : ℕ → ℝ) (_hx : ∀ n, |x n| ≤ 1) :
    Summable (fun m => |blockContrib k m x|) := by
  apply summable_of_ne_finset_zero (s := Finset.range (2 ^ (k + 1)))
  intro m hm
  rw [Finset.mem_range] at hm
  rw [blockContrib_eq_zero x (Nat.le_of_not_lt hm), abs_zero]

private lemma summable_abs_L (x : ℕ → ℝ) (hx : ∀ n, |x n| ≤ 1) :
    Summable (fun m => |∑' n, witness (m + n) * x n|) := by
  have hr0 : (0 : ℝ) ≤ (Real.sqrt 2) / 2 := by positivity
  have hr1 : (Real.sqrt 2) / 2 < 1 := by
    have h2 : Real.sqrt 2 < 2 := by
      have h := Real.sqrt_lt_sqrt (show (0:ℝ) ≤ 2 by norm_num) (show (2:ℝ) < 2 ^ 2 by norm_num)
      rwa [Real.sqrt_sq (by norm_num)] at h
    linarith
  have hH : Summable (fun k => 7 * ((Real.sqrt 2) / 2) ^ k) :=
    Summable.mul_left 7 (summable_geometric_of_lt_one hr0 hr1)
  refine summable_of_sum_range_le (c := ∑' k, 7 * ((Real.sqrt 2) / 2) ^ k)
    (fun m => abs_nonneg _) ?_
  intro M
  have hper : ∀ k, (∑ m ∈ Finset.range M, |blockContrib k m x|) ≤
      7 * ((Real.sqrt 2) / 2) ^ k := fun k =>
    (summable_abs_blockContrib_m k x hx).sum_le_tsum (Finset.range M)
      (fun m _ => abs_nonneg _) |>.trans (blockContrib_tsum_le k x hx)
  have hmid : Summable (fun k => ∑ m ∈ Finset.range M, |blockContrib k m x|) :=
    Summable.of_nonneg_of_le (fun k => sum_nonneg fun m _ => abs_nonneg _) hper hH
  have hstep : (∑ m ∈ Finset.range M, |∑' n, witness (m + n) * x n|) ≤
      ∑' k, (∑ m ∈ Finset.range M, |blockContrib k m x|) := by
    have hswap : ∑' k, (∑ m ∈ Finset.range M, |blockContrib k m x|) =
        ∑ m ∈ Finset.range M, ∑' k, |blockContrib k m x| := by
      have h := hasSum_sum (s := Finset.range M)
        (f := fun m k => |blockContrib k m x|)
        (a := fun m => ∑' k, |blockContrib k m x|)
        (fun m _ => (summable_abs_blockContrib m x hx).hasSum)
      exact h.tsum_eq
    rw [hswap]
    apply sum_le_sum
    intro m _
    exact abs_tsum_blockContrib_le m x hx
  exact hstep.trans (Summable.tsum_le_tsum hper hmid hH)

private lemma not_summable_weighted :
    ¬ Summable (fun n : ℕ => (n : ℝ) * |witness n|) := by
  intro hs
  set F : ℕ → ℝ := fun n : ℕ => (n : ℝ) * |witness n| with hF
  have hF0 : F 0 = 0 := by simp [hF, witness]
  have hFnn : ∀ n, 0 ≤ F n :=
    fun n => mul_nonneg (Nat.cast_nonneg n) (abs_nonneg _)
  have hblock : ∀ k, (1 : ℝ) ≤ ∑ j ∈ Finset.range (2 ^ k), F (2 ^ k + j) := by
    intro k
    calc (1 : ℝ) = ∑ _j ∈ Finset.range (2 ^ k), ((2 : ℝ) ^ k * (1 / 4 : ℝ) ^ k) := by
          rw [sum_const, card_range, nsmul_eq_mul]
          have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
          rw [hcast]
          have h1 : (2 : ℝ) ^ k * ((2 : ℝ) ^ k * (1 / 4 : ℝ) ^ k) =
              ((2 : ℝ) * (2 : ℝ)) ^ k * (1 / 4 : ℝ) ^ k := by rw [mul_pow]; ring
          rw [h1, show ((2 : ℝ) * (2 : ℝ)) ^ k * (1 / 4 : ℝ) ^ k =
              (((2 : ℝ) * (2 : ℝ)) * (1 / 4 : ℝ)) ^ k by rw [← mul_pow]]
          norm_num
      _ ≤ ∑ j ∈ Finset.range (2 ^ k), F (2 ^ k + j) := by
          apply sum_le_sum
          intro j hj
          have hj' := mem_range.mp hj
          simp only [hF]
          rw [abs_witness_of_mem hj']
          have hge : (2 : ℝ) ^ k ≤ (2 ^ k + j : ℕ) := by exact_mod_cast Nat.le_add_right _ _
          exact mul_le_mul_of_nonneg_right hge (by positivity)
  have htotal : ∀ K : ℕ, ((K : ℝ) + 1) ≤ ∑' n, F n := by
    intro K
    have hdy := dyadic_sum F (K + 1)
    rw [hF0, sub_zero] at hdy
    have hge : ((K : ℝ) + 1) ≤
        ∑ k ∈ Finset.range (K + 1), ∑ j ∈ Finset.range (2 ^ k), F (2 ^ k + j) := by
      calc ((K : ℝ) + 1) = ∑ _k ∈ Finset.range (K + 1), (1 : ℝ) := by
            rw [sum_const, card_range, nsmul_eq_mul, mul_one]; push_cast; ring
        _ ≤ _ := sum_le_sum fun k _ => hblock k
    apply hge.trans
    rw [hdy]
    exact hs.sum_le_tsum _ (fun n _ => hFnn n)
  obtain ⟨K, hK⟩ := exists_nat_gt (∑' n, F n)
  have hle := htotal K
  linarith

/--
**Mazur's Scottish Book Problem 88 fails.** The Scottish Book Problem 88 claim is false: there is
a real sequence $(a_n)_{n \ge 0}$ such that for every real sequence $(x_n)_{n \ge 0}$ with
$|x_n| \le 1$ for all $n$, each series $\sum_n a_{m+n} x_n$ with $m \ge 0$ converges, as the
limit of its partial sums, to some $L_m$, and $\sum_m |L_m| < \infty$, but $\sum_n n |a_n|$
diverges.

Source: S. Mazur, Problem 88 of the Scottish
Book; negative solution as an immediate consequence of Peller (1982),
J. Operator Theory 7, 341-372, §5, via V. V. Peller, "On S. Mazur's Problems
8 and 88 from the Scottish Book", arXiv:math/0703716: a Hankel matrix in the
injective tensor product need not have finite sum of moduli of its entries.
-/
theorem mazur88_refuted : ¬ ScottishBookProblem88Claim := by
  intro hclaim
  have hprem : ∀ x : ℕ → ℝ, (∀ n, |x n| ≤ 1) →
      ∃ L : ℕ → ℝ,
        (∀ m, Filter.Tendsto
          (fun N => ∑ n ∈ Finset.range N, witness (m + n) * x n)
          Filter.atTop (nhds (L m))) ∧
        Summable (fun m => |L m|) := by
    intro x hx
    refine ⟨fun m => ∑' n, witness (m + n) * x n, fun m => ?_, ?_⟩
    · exact (summable_witness_shift m x hx).hasSum.tendsto_sum_nat
    · exact summable_abs_L x hx
  exact not_summable_weighted (hclaim witness hprem)

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook88Wanted
