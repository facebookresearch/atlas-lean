/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.LSeries.RiemannZeta

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Alternating stride sum series for the Riemann zeta function

This module defines the alternating stride sum and proves convergence of its weighted
partial sums to the Riemann zeta function at positive integer arguments greater than one.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Theorem 1,
equation (9).
-/

namespace MetaMathlibExt

open Filter Topology

@[expose] public section

/-- **Alternating stride sum.** For natural numbers $q$, $t$ and $n$, let
$K = \lfloor (n + q - 1)/q \rfloor$ if $q \ge 1$ and $K = 0$ if $q = 0$. The alternating stride
sum is the real number
$$
S_{q,t}(n) = \sum_{i=0}^{K-1} \frac{(-1)^i}{(n - qi)^t}.
$$
For $q \ge 1$ this is the alternating sum of $m^{-t}$ over $m = n, n - q, n - 2q, \dots$ with
$m \ge 1$; with $j = i + 1$ it reads $\sum_{j=1}^{K} (-1)^{j+1}/(n + q - qj)^t$.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Theorem 1,
equation (9). -/
public noncomputable def strideAlternatingSum (q t n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range ((n + q - 1) / q), (-1 : ℝ) ^ i / ((n - q * i : ℕ) : ℝ) ^ t

private theorem div_eq_one_of_le_local {q n : ℕ} (hn : 0 < n) (hnq : n ≤ q) :
    (n + q - 1) / q = 1 :=
  Nat.div_eq_of_lt_le (by omega) (by omega)

private theorem div_add_eq_local {q n : ℕ} (hq : 0 < q) (hn : 0 < n) :
    (n + q + q - 1) / q = (n + q - 1) / q + 1 := by
  rw [(by omega : n + q + q - 1 = n + q - 1 + q), Nat.add_div_right _ hq]

/-- **Alternating stride sum with a single term.** For natural numbers $q$, $t$ and $n$ with
$1 \le n \le q$, the alternating stride sum satisfies $S_{q,t}(n) = 1/n^t$.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, equation (9). -/
public theorem strideAlternatingSum_of_le {q t n : ℕ} (hn : 0 < n) (hnq : n ≤ q) :
    strideAlternatingSum q t n = 1 / (n : ℝ) ^ t := by
  simp [strideAlternatingSum, div_eq_one_of_le_local hn hnq]

/-- **Recurrence for the alternating stride sum.** Let $q \ge 1$, $n \ge 1$ and $t \ge 0$ be
integers and let $S_{q,t}$ denote the alternating stride sum. Then
$S_{q,t}(n + q) = 1/(n + q)^t - S_{q,t}(n)$.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, equation (9). -/
public theorem strideAlternatingSum_add {q t n : ℕ} (hq : 0 < q) (hn : 0 < n) :
    strideAlternatingSum q t (n + q) = 1 / ((n + q : ℕ) : ℝ) ^ t - strideAlternatingSum q t n := by
  rw [strideAlternatingSum, div_add_eq_local hq hn, Finset.sum_range_succ', strideAlternatingSum,
    sub_eq_neg_add, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [(by rw [Nat.mul_succ]; omega : n + q - q * (i + 1) = n - q * i), pow_succ]
    ring

/-- If `a 0, …, a K` are nonnegative and nondecreasing, the norm of their alternating sum
is at most twice the last term `a K`. -/
public theorem norm_sum_range_neg_one_pow_mul_le_two_mul (a : ℕ → ℝ) (K : ℕ)
    (ha : ∀ i ≤ K, 0 ≤ a i) (hm : ∀ i < K, a i ≤ a (i + 1)) :
    ‖∑ i ∈ Finset.range (K + 1), (-1 : ℝ) ^ i * a i‖ ≤ 2 * a K := by
  have hid : (∑ i ∈ Finset.range (K + 1), (-1 : ℝ) ^ i * a i) =
      a K * (∑ i ∈ Finset.range (K + 1), (-1 : ℝ) ^ i) -
        ∑ i ∈ Finset.range K, (a (i + 1) - a i) *
          (∑ j ∈ Finset.range (i + 1), (-1 : ℝ) ^ j) := by
    simpa [smul_eq_mul, mul_comm] using
      Finset.sum_range_by_parts a (fun i => (-1 : ℝ) ^ i) (K + 1)
  rw [hid]
  calc
    _ ≤ ‖a K * (∑ i ∈ Finset.range (K + 1), (-1 : ℝ) ^ i)‖ +
        ‖∑ i ∈ Finset.range K, (a (i + 1) - a i) *
          (∑ j ∈ Finset.range (i + 1), (-1 : ℝ) ^ j)‖ := norm_sub_le _ _
    _ ≤ a K + ∑ i ∈ Finset.range K, (a (i + 1) - a i) := by
      apply add_le_add
      · rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (ha K le_rfl)]
        simpa using mul_le_mul_of_nonneg_left (norm_sum_neg_one_pow_le (K + 1)) (ha K le_rfl)
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
        have h := sub_nonneg.mpr (hm i (Finset.mem_range.mp hi))
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg h]
        simpa using mul_le_mul_of_nonneg_left (norm_sum_neg_one_pow_le (i + 1)) h
    _ ≤ 2 * a K := by
      rw [Finset.sum_range_sub]
      linarith [ha 0 (Nat.zero_le K)]

private theorem stride_bound (q t n : ℕ) (hq : 0 < q) (hn : 0 < n) :
    ‖strideAlternatingSum q t n‖ ≤ 2 := by
  have hK : 0 < (n + q - 1) / q := by
    apply Nat.div_pos
    · omega
    · exact hq
  obtain ⟨K, hK⟩ := Nat.exists_eq_succ_of_ne_zero hK.ne'
  have hpos (i : ℕ) (hi : i ≤ K) : 0 < n - q * i := by
    have hlt : i < (n + q - 1) / q := by omega
    have hmul := (Nat.le_div_iff_mul_le hq).mp (Nat.succ_le_of_lt hlt)
    rw [Nat.succ_mul, Nat.mul_comm i q] at hmul
    omega
  have ha (i : ℕ) (hi : i ≤ K) : 0 ≤ 1 / ((n - q * i : ℕ) : ℝ) ^ t := by
    positivity
  have hm (i : ℕ) (hi : i < K) :
      1 / ((n - q * i : ℕ) : ℝ) ^ t ≤ 1 / ((n - q * (i + 1) : ℕ) : ℝ) ^ t := by
    apply one_div_le_one_div_of_le
    · exact pow_pos (by exact_mod_cast hpos (i + 1) (by omega)) t
    · apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast Nat.sub_le_sub_left (Nat.mul_le_mul_left q (Nat.le_succ i)) n
  have hb : 1 / ((n - q * K : ℕ) : ℝ) ^ t ≤ 1 := by
    apply (div_le_one (pow_pos (by exact_mod_cast hpos K le_rfl) t)).mpr
    exact one_le_pow₀ (by exact_mod_cast hpos K le_rfl)
  calc
    ‖strideAlternatingSum q t n‖ =
        ‖∑ i ∈ Finset.range (K + 1), (-1 : ℝ) ^ i *
          (1 / ((n - q * i : ℕ) : ℝ) ^ t)‖ := by
      simp [strideAlternatingSum, hK, div_eq_mul_inv]
    _ ≤ 2 * (1 / ((n - q * K : ℕ) : ℝ) ^ t) :=
      norm_sum_range_neg_one_pow_mul_le_two_mul _ K ha hm
    _ ≤ 2 := by linarith

private theorem weighted_term (q t n : ℕ) (hq : 0 < q) (hn : 0 < n) :
    (2 * (n : ℝ) + q) / ((n : ℝ) * ((n : ℝ) + q)) * strideAlternatingSum q t n =
      strideAlternatingSum q t n / n -
        strideAlternatingSum q t (n + q) / (n + q : ℕ) +
          1 / ((n + q : ℕ) : ℝ) ^ (t + 1) := by
  rw [strideAlternatingSum_add hq hn, Nat.cast_add, pow_succ]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnq0 : (n : ℝ) + q ≠ 0 := by positivity
  field_simp
  ring

private theorem window_shift (f : ℕ → ℝ) (q N : ℕ) :
    (∑ j ∈ Finset.range q, f (N + j + 1)) -
        (∑ j ∈ Finset.range q, f (N + 1 + j + 1)) =
      f (N + 1) - f (N + q + 1) := by
  have h := (Finset.sum_range_succ' (fun j => f (N + j + 1)) q).symm.trans
    (Finset.sum_range_succ (fun j => f (N + j + 1)) q)
  simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.zero_add] at h ⊢
  linarith

private theorem finite_identity (q t : ℕ) (hq : 0 < q) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      (2 * ((n : ℝ) + 1) + q) / (((n : ℝ) + 1) * ((n : ℝ) + 1 + q)) *
        strideAlternatingSum q t (n + 1)) =
      (∑ n ∈ Finset.range (N + q), 1 / ((n + 1 : ℕ) : ℝ) ^ (t + 1)) -
        ∑ j ∈ Finset.range q,
          strideAlternatingSum q t (N + j + 1) / (N + j + 1 : ℕ) := by
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, zero_add]
    symm
    rw [sub_eq_zero]
    apply Finset.sum_congr rfl
    intro j hj
    rw [strideAlternatingSum_of_le (by omega) (by simpa using Finset.mem_range.mp hj)]
    simp [pow_succ, div_eq_mul_inv, mul_comm]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have h := weighted_term q t (N + 1) hq (by omega)
    simp only [Nat.cast_add, Nat.cast_one] at h
    rw [h]
    rw [(by omega : N + 1 + q = N + q + 1), Finset.sum_range_succ]
    have hw := window_shift (fun n => strideAlternatingSum q t n / (n : ℝ)) q N
    simp only [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] at hw ⊢
    linarith

private theorem stride_div_tendsto_zero (q t j : ℕ) (hq : 0 < q) :
    Tendsto (fun N : ℕ => strideAlternatingSum q t (N + j + 1) / (N + j + 1 : ℕ))
      atTop (𝓝 (0 : ℝ)) := by
  apply squeeze_zero_norm (a := fun N : ℕ => 2 / (N + j + 1 : ℕ))
  · intro N
    rw [norm_div, Real.norm_natCast]
    exact div_le_div_of_nonneg_right (stride_bound q t (N + j + 1) hq (by omega))
      (by positivity)
  · exact (tendsto_natCast_atTop_atTop (R := ℝ) |>.comp
      (tendsto_add_atTop_nat (j + 1))).const_div_atTop 2

private theorem boundary_tendsto_zero (q t : ℕ) (hq : 0 < q) :
    Tendsto (fun N : ℕ => ∑ j ∈ Finset.range q,
      strideAlternatingSum q t (N + j + 1) / (N + j + 1 : ℕ)) atTop (𝓝 (0 : ℝ)) := by
  simpa using tendsto_finsetSum (Finset.range q)
    (fun j _ => stride_div_tendsto_zero q t j hq)

private theorem zeta_partial_sums (t : ℕ) (ht : 0 < t) :
    Tendsto (fun N : ℕ => ((∑ n ∈ Finset.range N,
      1 / ((n + 1 : ℕ) : ℝ) ^ (t + 1) : ℝ) : ℂ))
      atTop (𝓝 (riemannZeta ((t : ℂ) + 1))) := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (t + 1)) :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  have hsc : Summable (fun n : ℕ => 1 / (n : ℂ) ^ (t + 1)) := by
    simpa using Complex.summable_ofReal.mpr hs
  have hz : riemannZeta ((t : ℂ) + 1) =
      ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℂ) ^ (t + 1) := by
    rw [← Nat.cast_add_one, zeta_nat_eq_tsum_of_gt_one (by omega), hsc.tsum_eq_zero_add]
    simp [zero_pow (by omega : t + 1 ≠ 0)]
  have hshift := (summable_nat_add_iff 1).mpr hsc
  rw [hz]
  simpa using hshift.hasSum.tendsto_sum_nat

/-- **Alternating stride sum series for $\zeta(t + 1)$.** Let $q \ge 1$ and $t \ge 1$ be integers
and let $S_{q,t}$ denote the alternating stride sum. Then the partial sums
$$
\sum_{n=1}^{N} \frac{2n + q}{n(n + q)} \, S_{q,t}(n)
$$
converge to $\zeta(t + 1)$ as $N \to \infty$, where $\zeta$ is the Riemann zeta function.

The series converges only conditionally, which is why it is stated through its partial sums.
On the subsequence $n = 1 + mq$, reversing the alternating sum gives a magnitude
$|S_{q,t}(n)| \ge 1 - (1 + q)^{-t}$; the weight is at least $1/n$, yielding a divergent harmonic
lower bound for the series of absolute values. The second expression in equation (9) and the
general identity (8) use a quantity $A^{(t)}$ that the record does not define and are not stated
here.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Theorem 1,
equation (9). -/
public theorem tendsto_strideAlternatingSum_riemannZeta (q t : ℕ) (hq : 0 < q)
    (ht : 0 < t) :
    Tendsto (fun N : ℕ => ((∑ n ∈ Finset.range N,
        (2 * ((n : ℝ) + 1) + q) / (((n : ℝ) + 1) * ((n : ℝ) + 1 + q)) *
          strideAlternatingSum q t (n + 1) : ℝ) : ℂ))
      atTop (𝓝 (riemannZeta ((t : ℂ) + 1))) := by
  have hz := (zeta_partial_sums t ht).comp (tendsto_add_atTop_nat q)
  have hb := (Complex.continuous_ofReal.tendsto 0).comp (boundary_tendsto_zero q t hq)
  have h := hz.sub hb
  simp only [Complex.ofReal_zero, sub_zero] at h
  apply h.congr
  intro N
  simp only [Function.comp_apply, finite_identity q t hq N, Complex.ofReal_sub]

end

end MetaMathlibExt
