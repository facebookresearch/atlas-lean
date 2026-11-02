/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Hardy's inequality for series

This file proves the sharp `ℓᵖ` bound for the sequence of prefix averages of a
nonnegative real sequence when `1 < p`.
-/

namespace MetaMathlibExt

@[expose] public section

private noncomputable def hardy_average (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range n, a i) / (n : ℝ)

private lemma hardy_average_nonneg {a : ℕ → ℝ} (hnonneg : ∀ n, 0 ≤ a n) (n : ℕ) :
    0 ≤ hardy_average a n := by
  exact div_nonneg (Finset.sum_nonneg fun i _ ↦ hnonneg i) (Nat.cast_nonneg n)

private lemma hardy_cast_mul_average (a : ℕ → ℝ) (n : ℕ) :
    (n : ℝ) * hardy_average a n = ∑ i ∈ Finset.range n, a i := by
  cases n with
  | zero => simp [hardy_average]
  | succ n =>
      rw [hardy_average, mul_div_cancel₀]
      exact_mod_cast Nat.succ_ne_zero n

private lemma hardy_average_recurrence (a : ℕ → ℝ) (n : ℕ) :
    ((n : ℝ) + 1) * hardy_average a (n + 1) - (n : ℝ) * hardy_average a n = a n := by
  have hsucc := hardy_cast_mul_average a (n + 1)
  have hn := hardy_cast_mul_average a n
  norm_num [Nat.cast_add, Nat.cast_one] at hsucc
  rw [hsucc, hn, Finset.sum_range_succ]
  ring

private lemma hardy_young {x y p : ℝ} (hp : 1 < p) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x * y.rpow (p - 1) ≤
      x.rpow p / p + y.rpow p / Real.conjExponent p := by
  have hpq : p.HolderConjugate (Real.conjExponent p) :=
    Real.HolderConjugate.conjExponent hp
  calc
    x * y.rpow (p - 1) ≤
        x.rpow p / p + (y.rpow (p - 1)).rpow (Real.conjExponent p) /
          Real.conjExponent p :=
      Real.young_inequality_of_nonneg hx (Real.rpow_nonneg hy _) hpq
    _ = x.rpow p / p + y.rpow p / Real.conjExponent p := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_mul hy, hpq.sub_one_mul_conj]

private lemma hardy_rpow_sub_one_conj {x p : ℝ} (hp : 1 < p) (hx : 0 ≤ x) :
    (x.rpow (p - 1)).rpow (Real.conjExponent p) = x.rpow p := by
  have hpq : p.HolderConjugate (Real.conjExponent p) :=
    Real.HolderConjugate.conjExponent hp
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_mul hx, hpq.sub_one_mul_conj]

private lemma hardy_mul_rpow_sub_one {x p : ℝ} (hp : 1 < p) (hx : 0 ≤ x) :
    x * x.rpow (p - 1) = x.rpow p := by
  calc
    x * x.rpow (p - 1) = x.rpow (p - 1) * x := mul_comm _ _
    _ = x.rpow ((p - 1) + 1) := by
      simp only [Real.rpow_eq_pow]
      exact (Real.rpow_add_one' hx (by linarith)).symm
    _ = x.rpow p := by
      congr 1
      ring

private lemma hardy_pointwise {a : ℕ → ℝ} {p : ℝ} (hp : 1 < p)
    (hnonneg : ∀ n, 0 ≤ a n) (n : ℕ) :
    (hardy_average a (n + 1)).rpow p -
        Real.conjExponent p * a n * (hardy_average a (n + 1)).rpow (p - 1) ≤
      ((n : ℝ) * (hardy_average a n).rpow p -
          ((n : ℝ) + 1) * (hardy_average a (n + 1)).rpow p) /
        (p - 1) := by
  let A := hardy_average a (n + 1)
  let B := hardy_average a n
  have hA : 0 ≤ A := by simpa [A] using hardy_average_nonneg hnonneg (n + 1)
  have hB : 0 ≤ B := by simpa [B] using hardy_average_nonneg hnonneg n
  have hpq : p.HolderConjugate (Real.conjExponent p) :=
    Real.HolderConjugate.conjExponent hp
  have hrec : ((n : ℝ) + 1) * A - (n : ℝ) * B = a n := by
    simpa [A, B] using hardy_average_recurrence a n
  have hAA : A * A.rpow (p - 1) = A.rpow p := hardy_mul_rpow_sub_one hp hA
  have hy := hardy_young hp hB hA
  have hy_scaled :
      p * (B * A.rpow (p - 1)) ≤ B.rpow p + (p - 1) * A.rpow p := by
    calc
      p * (B * A.rpow (p - 1)) ≤
          p * (B.rpow p / p + A.rpow p / Real.conjExponent p) :=
        mul_le_mul_of_nonneg_left hy (le_trans (by norm_num) hp.le)
      _ = B.rpow p + (p / Real.conjExponent p) * A.rpow p := by
        rw [mul_add, mul_div_cancel₀ _ (ne_of_gt (lt_trans (by norm_num) hp))]
        ring
      _ = B.rpow p + (p - 1) * A.rpow p := by
        rw [hpq.div_conj_eq_sub_one]
  have hyn := mul_le_mul_of_nonneg_left hy_scaled (Nat.cast_nonneg n : 0 ≤ (n : ℝ))
  have har :
      a n * A.rpow (p - 1) =
        ((n : ℝ) + 1) * A.rpow p - (n : ℝ) * (B * A.rpow (p - 1)) := by
    calc
      a n * A.rpow (p - 1) =
          (((n : ℝ) + 1) * A - (n : ℝ) * B) * A.rpow (p - 1) := by rw [hrec]
      _ = ((n : ℝ) + 1) * A.rpow p -
          (n : ℝ) * (B * A.rpow (p - 1)) := by
        rw [sub_mul, mul_assoc, hAA]
        ring
  rw [le_div_iff₀ (sub_pos.mpr hp)]
  change
    (A.rpow p - Real.conjExponent p * a n * A.rpow (p - 1)) * (p - 1) ≤
      (n : ℝ) * B.rpow p - ((n : ℝ) + 1) * A.rpow p
  calc
    (A.rpow p - Real.conjExponent p * a n * A.rpow (p - 1)) * (p - 1) =
        (p - 1) * A.rpow p -
          ((p - 1) * Real.conjExponent p) * (a n * A.rpow (p - 1)) := by ring
    _ = (p - 1) * A.rpow p - p * (a n * A.rpow (p - 1)) := by
      rw [hpq.sub_one_mul_conj]
    _ = (p - 1) * A.rpow p -
        p * (((n : ℝ) + 1) * A.rpow p -
          (n : ℝ) * (B * A.rpow (p - 1))) := by rw [har]
    _ ≤ (n : ℝ) * B.rpow p - ((n : ℝ) + 1) * A.rpow p := by
      nlinarith

private lemma hardy_telescope (a : ℕ → ℝ) (p : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N,
        ((n : ℝ) * (hardy_average a n).rpow p -
          ((n : ℝ) + 1) * (hardy_average a (n + 1)).rpow p)) =
      -(N : ℝ) * (hardy_average a N).rpow p := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring

private lemma hardy_telescoping_bound {a : ℕ → ℝ} {p : ℝ} (hp : 1 < p)
    (hnonneg : ∀ n, 0 ≤ a n) (N : ℕ) :
    (∑ n ∈ Finset.range N, (hardy_average a (n + 1)).rpow p) ≤
      Real.conjExponent p *
        ∑ n ∈ Finset.range N,
          a n * (hardy_average a (n + 1)).rpow (p - 1) := by
  have hsum :
      (∑ n ∈ Finset.range N,
          ((hardy_average a (n + 1)).rpow p -
            Real.conjExponent p * a n *
              (hardy_average a (n + 1)).rpow (p - 1))) ≤
        ∑ n ∈ Finset.range N,
          (((n : ℝ) * (hardy_average a n).rpow p -
              ((n : ℝ) + 1) * (hardy_average a (n + 1)).rpow p) /
            (p - 1)) := by
    exact Finset.sum_le_sum fun n _ ↦ hardy_pointwise hp hnonneg n
  rw [← Finset.sum_div, hardy_telescope] at hsum
  have hend :
      (-(N : ℝ) * (hardy_average a N).rpow p) / (p - 1) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg N))
        (Real.rpow_nonneg (hardy_average_nonneg hnonneg N) p)
    · exact (sub_pos.mpr hp).le
  have hsum' := hsum.trans hend
  rw [Finset.sum_sub_distrib] at hsum'
  simp_rw [mul_assoc] at hsum'
  rw [← Finset.mul_sum] at hsum'
  linarith

private lemma hardy_holder {a : ℕ → ℝ} {p : ℝ} (hp : 1 < p)
    (hnonneg : ∀ n, 0 ≤ a n) (N : ℕ) :
    (∑ n ∈ Finset.range N,
        a n * (hardy_average a (n + 1)).rpow (p - 1)) ≤
      (∑ n ∈ Finset.range N, (a n).rpow p).rpow (1 / p) *
        (∑ n ∈ Finset.range N,
          (hardy_average a (n + 1)).rpow p).rpow
            (1 / Real.conjExponent p) := by
  have hpq : p.HolderConjugate (Real.conjExponent p) :=
    Real.HolderConjugate.conjExponent hp
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg (Finset.range N) hpq
    (fun n _ ↦ hnonneg n)
    (fun n _ ↦ Real.rpow_nonneg (hardy_average_nonneg hnonneg (n + 1)) (p - 1))
  have hpow :
      (∑ n ∈ Finset.range N,
          ((hardy_average a (n + 1)).rpow (p - 1)).rpow
            (Real.conjExponent p)) =
        ∑ n ∈ Finset.range N, (hardy_average a (n + 1)).rpow p := by
    apply Finset.sum_congr rfl
    intro n _
    exact hardy_rpow_sub_one_conj hp (hardy_average_nonneg hnonneg (n + 1))
  simp only [Real.rpow_eq_pow] at hpow
  rw [hpow] at h
  simpa only [Real.rpow_eq_pow] using h

private lemma hardy_rpow_inv_rpow {x p : ℝ} (hp : 1 < p) (hx : 0 ≤ x) :
    (x.rpow (1 / p)).rpow p = x := by
  simpa only [one_div, Real.rpow_eq_pow] using
    Real.rpow_inv_rpow hx (ne_of_gt (lt_trans (by norm_num) hp))

private theorem hardy_finite {a : ℕ → ℝ} {p : ℝ} (hp : 1 < p)
    (hnonneg : ∀ n, 0 ≤ a n) (N : ℕ) :
    (∑ n ∈ Finset.range N, (hardy_average a (n + 1)).rpow p) ≤
      (Real.conjExponent p).rpow p *
        ∑ n ∈ Finset.range N, (a n).rpow p := by
  let T := ∑ n ∈ Finset.range N, (hardy_average a (n + 1)).rpow p
  let X := ∑ n ∈ Finset.range N, (a n).rpow p
  let I := ∑ n ∈ Finset.range N,
    a n * (hardy_average a (n + 1)).rpow (p - 1)
  let q := Real.conjExponent p
  change T ≤ q.rpow p * X
  have hpq : p.HolderConjugate q := by
    simpa [q] using Real.HolderConjugate.conjExponent hp
  have hq0 : 0 ≤ q := hpq.symm.pos.le
  have hT0 : 0 ≤ T := by
    exact Finset.sum_nonneg fun n _ ↦
      Real.rpow_nonneg (hardy_average_nonneg hnonneg (n + 1)) p
  have hX0 : 0 ≤ X := by
    exact Finset.sum_nonneg fun n _ ↦ Real.rpow_nonneg (hnonneg n) p
  have htel : T ≤ q * I := by
    simpa [T, I, q] using hardy_telescoping_bound hp hnonneg N
  have hhold :
      I ≤ X.rpow (1 / p) * T.rpow (1 / q) := by
    simpa [T, X, I, q] using hardy_holder hp hnonneg N
  have hmain : T ≤ q * (X.rpow (1 / p) * T.rpow (1 / q)) :=
    htel.trans (mul_le_mul_of_nonneg_left hhold hq0)
  rcases eq_or_lt_of_le hT0 with hTzero | hTpos
  · rw [← hTzero]
    exact mul_nonneg (Real.rpow_nonneg hq0 p) hX0
  · have hsplit : T.rpow (1 / p) * T.rpow (1 / q) = T := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_add hTpos]
      rw [show 1 / p + 1 / q = 1 by
        simpa only [one_div] using hpq.inv_add_inv_eq_one]
      exact Real.rpow_one T
    have hV : 0 < T.rpow (1 / q) := Real.rpow_pos_of_pos hTpos _
    have hcancel : T.rpow (1 / p) ≤ q * X.rpow (1 / p) := by
      apply (mul_le_mul_iff_left₀ hV).mp
      calc
        T.rpow (1 / p) * T.rpow (1 / q) = T := hsplit
        _ ≤ q * (X.rpow (1 / p) * T.rpow (1 / q)) := hmain
        _ = (q * X.rpow (1 / p)) * T.rpow (1 / q) := by ring
    have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hT0 (1 / p)) hcancel
      (le_trans (by norm_num) hp.le)
    calc
      T = (T.rpow (1 / p)).rpow p := (hardy_rpow_inv_rpow hp hT0).symm
      _ ≤ (q * X.rpow (1 / p)).rpow p := hpow
      _ = q.rpow p * (X.rpow (1 / p)).rpow p := by
        simp only [Real.rpow_eq_pow]
        exact Real.mul_rpow hq0 (Real.rpow_nonneg hX0 (1 / p))
      _ = q.rpow p * X := by rw [hardy_rpow_inv_rpow hp hX0]

/-- **Hardy's inequality.** Let $p > 1$ be a real number and let $(a_n)_{n \ge 0}$ be a sequence
of nonnegative real numbers such that $\sum_n a_n^p$ converges. Write
$A_n = \frac{1}{n+1} \sum_{i=0}^{n} a_i$ for the average of $a_0, \dots, a_n$. Then
$\sum_n A_n^p$ converges and
$$\sum_{n=0}^{\infty} A_n^p \le \left(\frac{p}{p-1}\right)^p \sum_{n=0}^{\infty} a_n^p.$$

Proof: Elliott's finite telescoping argument is combined with Young's and Hölder's inequalities,
following E. B. Elliott (1926) as presented in Hardy--Littlewood--Pólya, *Inequalities*,
Theorem 326.

Proves `Wanted` entry `hardy_inequality`.

Source: G. H. Hardy, *Note on a theorem of Hilbert*, Mathematische Zeitschrift 6 (1920), 314-317
(statement hardy-ineq-s1): the discrete series form with constant `(p / (p - 1)) ^ p` for `p > 1`.
-/
theorem hardy_inequality {a : ℕ → ℝ} {p : ℝ} (hp : 1 < p)
    (hnonneg : ∀ n, 0 ≤ a n)
    (hsumm : Summable fun n => (a n).rpow p) :
    Summable (fun n => ((Finset.sum (Finset.range (n + 1)) a / ((n : ℝ) + 1)).rpow p)) ∧
    ∑' n, ((Finset.sum (Finset.range (n + 1)) a / ((n : ℝ) + 1)).rpow p) ≤
      (p / (p - 1)).rpow p * ∑' n, (a n).rpow p := by
  have hpq : p.HolderConjugate (Real.conjExponent p) :=
    Real.HolderConjugate.conjExponent hp
  have hqpow0 : 0 ≤ (Real.conjExponent p).rpow p :=
    Real.rpow_nonneg hpq.symm.pos.le p
  have havg0 : ∀ n, 0 ≤ (hardy_average a (n + 1)).rpow p := fun n ↦
    Real.rpow_nonneg (hardy_average_nonneg hnonneg (n + 1)) p
  have hbound : ∀ N,
      (∑ n ∈ Finset.range N, (hardy_average a (n + 1)).rpow p) ≤
        (Real.conjExponent p).rpow p * ∑' n, (a n).rpow p := by
    intro N
    calc
      (∑ n ∈ Finset.range N, (hardy_average a (n + 1)).rpow p) ≤
          (Real.conjExponent p).rpow p *
            ∑ n ∈ Finset.range N, (a n).rpow p :=
        hardy_finite hp hnonneg N
      _ ≤ (Real.conjExponent p).rpow p * ∑' n, (a n).rpow p := by
        apply mul_le_mul_of_nonneg_left _ hqpow0
        exact hsumm.sum_le_tsum (Finset.range N) fun n _ ↦
          Real.rpow_nonneg (hnonneg n) p
  have havg_summable : Summable fun n ↦ (hardy_average a (n + 1)).rpow p :=
    summable_of_sum_range_le havg0 hbound
  have havg_tsum :
      ∑' n, (hardy_average a (n + 1)).rpow p ≤
        (Real.conjExponent p).rpow p * ∑' n, (a n).rpow p :=
    Real.tsum_le_of_sum_range_le havg0 hbound
  simpa [hardy_average, Real.conjExponent, Nat.cast_add, Nat.cast_one] using
    And.intro havg_summable havg_tsum

end

end MetaMathlibExt
