/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.LpShiftOperator
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Analysis.RCLike.Basic

import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Dense periodic points of the Rolewicz backward shift

Let `B` be the backward shift on `ℓ²(ℕ, 𝕜)`, `(B x) n = x (n + 1)`.
This file studies the periodic points of its scalar multiples `μ • B`:
a vector `x` is periodic of period `n` if `(μ • B) ^ n x = x`.

The main result is a dichotomy. If `‖μ‖ > 1`, the periodic points are
dense in `ℓ²(ℕ, 𝕜)`: given `y` and a period `N`, the truncation of `y`
to its first `N` coordinates is extended to a periodic vector by the
geometric series `∑' m, (μ⁻¹ ^ N) ^ m • F ^ (N * m) (trunc N y)`, where
`F` is the forward shift; as `N → ∞` the truncation error and the
geometric tail both tend to `0`. If `‖μ‖ ≤ 1`, the only periodic point
is `0`: a periodic vector satisfies `x k = μ ^ (n * m) * x (k + n * m)`
for all `m`, while `‖x j‖ → 0` as `j → ∞` since `x` is square-summable.

In particular, the set of periodic points of `μ • B` is dense if and
only if `‖μ‖ > 1`. Together with Rolewicz's theorem (batch 94:
`μ • B` is hypercyclic if and only if `‖μ‖ > 1`), this is the two
ingredients of Devaney chaos for the Rolewicz operators; the
hypercyclicity itself is proved in batch 94 and is not re-proved here.

This is a companion to the Baire-category, bounded-operator, and
Hilbert-space material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/`. It is not one of the
72 v1 targets. The construction reuses the canonical shifts in
`MathlibExt.Analysis.InnerProductSpace.LpShiftOperator` and Mathlib’s
periodic-point API. Classical reference:
S. Rolewicz, "On orbits of elements", *Studia Math.* 32 (1969),
17–22; see also F. Bayart and É. Matheron, *Dynamics of Linear
Operators*, Cambridge University Press, 2009, Chapter 1.

## Main declarations

* `Function.IsPeriodicPt` and `Function.periodicPts` : Mathlib’s periodic-point API.
* `periodicApprox` : the periodic extension of a truncation of `y`,
  as a geometric series of forward shifts.
* `periodicApprox_isPeriodicPoint` : `periodicApprox μ N y` is
  periodic of period `N` when `‖μ‖ > 1`.
* `dense_periodicPoints_of_one_lt_norm` : the periodic points of
  `μ • B` are dense when `‖μ‖ > 1`.
* `eq_zero_of_isPeriodicPoint_of_norm_le_one` : the only periodic
  point of `μ • B` is `0` when `‖μ‖ ≤ 1`.
* `dense_periodicPoints_iff` : the periodic points are dense if and
  only if `‖μ‖ > 1`.
-/

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.RolewiczPeriodic

open Filter Topology Set Metric
open MathlibExt.Analysis.InnerProductSpace.LpShiftOperator
open scoped _root_.lp ENNReal

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The squared `ℓ²` norm is the sum of squared coordinate norms. -/
theorem norm_sq_eq_tsum (z : ℓ²(ℕ, 𝕜)) :
    ‖z‖ ^ 2 = ∑' i, ‖(z : ℕ → 𝕜) i‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (show (0 : ℝ) < (2 : ℝ≥0∞).toReal by simp) z
  simp only [show (2 : ℝ≥0∞).toReal = (2 : ℝ) by simp, Real.rpow_two] at h
  exact h

/-- The squared coordinate norms of an `ℓ²` vector are summable. -/
theorem summable_norm_sq (z : ℓ²(ℕ, 𝕜)) :
    Summable (fun i => ‖(z : ℕ → 𝕜) i‖ ^ 2) := by
  have h := (lp.memℓp z).summable (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
  simp only [show (2 : ℝ≥0∞).toReal = (2 : ℝ) by simp, Real.rpow_two] at h
  exact h

/-! ### Powers of the shifts -/

/-- Pointwise action of the `n`-th power of the backward shift:
`(Bⁿ x) i = x (i + n)`. -/
theorem backwardCLM_pow_apply : ∀ (n : ℕ) (x : ℓ²(ℕ, 𝕜)) (i : ℕ),
    ((backwardCLM ^ n) x) i = x (i + n) := by
  intro n
  induction n with
  | zero => intro x i; simp
  | succ n ih =>
    intro x i
    rw [pow_succ, mul_apply_eq_comp, ih, backwardCLM_apply, backwardFun_apply]
    congr 1

/-- Pointwise action of the `n`-th power of the forward shift:
`(Fⁿ x) i = 0` for `i < n` and `x (i - n)` otherwise. -/
theorem shiftCLM_pow_apply : ∀ (n : ℕ) (x : ℓ²(ℕ, 𝕜)) (i : ℕ),
    ((shiftCLM ^ n) x) i = if i < n then 0 else x (i - n) := by
  intro n
  induction n with
  | zero => intro x i; simp
  | succ n ih =>
    intro x i
    rw [pow_succ, mul_apply_eq_comp, ih]
    by_cases hi : i < n
    · rw [ite_eq_left hi, ite_eq_left (hi.trans (Nat.lt_succ_self n))]
    · rw [ite_eq_right hi]
      rcases Nat.eq_zero_or_pos (i - n) with h0 | hpos
      · have hi' : i = n := by omega
        rw [hi', Nat.sub_self, shiftCLM_apply, shiftFun_zero,
          ite_eq_left (Nat.lt_succ_self n)]
      · obtain ⟨m, hm⟩ : ∃ m, i - n = m + 1 := ⟨i - n - 1, by omega⟩
        rw [hm, shiftCLM_apply, shiftFun_succ,
          ite_eq_right (by omega : ¬ i < n + 1)]
        have hsub : i - (n + 1) = m := by omega
        rw [hsub]

/-- `Bⁿ Fⁿ = 1`: the powers of the backward shift undo the powers of
the forward shift. -/
theorem backwardCLM_pow_shiftCLM_pow_apply (n : ℕ) (x : ℓ²(ℕ, 𝕜)) :
    (backwardCLM ^ n) ((shiftCLM ^ n) x) = x := by
  apply lp.ext
  funext i
  rw [backwardCLM_pow_apply, shiftCLM_pow_apply,
    ite_eq_right (by omega : ¬ i + n < n)]
  have hsub : i + n - n = i := by omega
  rw [hsub]

/-- Powers of the forward shift preserve norms. -/
theorem norm_shiftCLM_pow_apply (n : ℕ) (x : ℓ²(ℕ, 𝕜)) :
    ‖(shiftCLM ^ n) x‖ = ‖x‖ := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_apply_eq_comp, ih, norm_shiftCLM_apply]

/-- Powers of the backward shift do not increase norms. -/
theorem norm_backwardCLM_pow_apply_le (n : ℕ) (x : ℓ²(ℕ, 𝕜)) :
    ‖(backwardCLM ^ n) x‖ ≤ ‖x‖ := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_apply_eq_comp]
    exact le_trans (ih (backwardCLM x)) (norm_backwardLinMap_apply_le x)

/-- Pointwise action of a power of a scalar multiple of the backward shift. -/
theorem smul_backwardCLM_pow_apply (μ : 𝕜) (n : ℕ) (x : ℓ²(ℕ, 𝕜)) :
    (((μ • backwardCLM) ^ n) x) = μ ^ n • (backwardCLM ^ n) x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    calc (((μ • backwardCLM) ^ (n + 1)) x)
        = ((μ • backwardCLM) ^ n) ((μ • backwardCLM) x) := by
          rw [pow_succ, mul_apply_eq_comp]
      _ = μ ^ n • (backwardCLM ^ n) ((μ • backwardCLM) x) := by rw [ih]
      _ = μ ^ n • (μ • (backwardCLM ^ n) (backwardCLM x)) := by
          congr 1
          rw [smul_apply, map_smul]
      _ = (μ ^ n * μ) • (backwardCLM ^ n) (backwardCLM x) := by rw [smul_smul]
      _ = μ ^ (n + 1) • (backwardCLM ^ (n + 1)) x := by
          have h1 : μ ^ (n + 1) = μ ^ n * μ := pow_succ _ _
          have h2 : (backwardCLM ^ (n + 1)) x =
              (backwardCLM ^ n) (backwardCLM x) := by
            rw [pow_succ, mul_apply_eq_comp]
          rw [h1, h2]

/-- Coordinate form of a power of a scalar multiple of the backward shift. -/
theorem smul_backwardCLM_pow_apply_coord (μ : 𝕜) (n : ℕ) (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    (((μ • backwardCLM) ^ n) x) i = μ ^ n * (x : ℕ → 𝕜) (i + n) := by
  rw [smul_backwardCLM_pow_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    backwardCLM_pow_apply]

/-- A power of a scalar multiple of the backward shift, as an operator. -/
theorem smul_backwardCLM_pow (μ : 𝕜) (n : ℕ) :
    (μ • backwardCLM (𝕜 := 𝕜)) ^ n = μ ^ n • (backwardCLM (𝕜 := 𝕜) ^ n) := by
  apply ContinuousLinearMap.ext
  intro x
  rw [smul_backwardCLM_pow_apply, smul_apply]

/-! ### Periodic points -/

/-- Operator powers and function iterates give the same periodic-point equation. -/
private theorem isPeriodicPt_iff_pow_apply_eq (T : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜))
    (n : ℕ) (x : ℓ²(ℕ, 𝕜)) : Function.IsPeriodicPt (⇑T) n x ↔ (T ^ n) x = x := by
  change (⇑T.toLinearMap)^[n] x = x ↔ (T ^ n) x = x
  rw [← Module.End.pow_apply T.toLinearMap n x, ← ContinuousLinearMap.toLinearMap_pow]
  rfl

/-- `0` is a periodic point of every period for every operator. -/
theorem isPeriodicPoint_zero (T : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) (n : ℕ) :
    Function.IsPeriodicPt (⇑T) n 0 := by
  exact (show Function.IsFixedPt (⇑T) 0 from map_zero T).isPeriodicPt n

/-! ### Truncation -/

/-- The truncation of `y` to its first `N` coordinates. -/
noncomputable def trunc (N : ℕ) (y : ℓ²(ℕ, 𝕜)) : ℓ²(ℕ, 𝕜) :=
  ∑ i ∈ Finset.range N, lp.single 2 i (y i)

/-- Coordinate form of the truncation. -/
theorem trunc_apply (N : ℕ) (y : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    (trunc N y : ℕ → 𝕜) i = if i < N then (y : ℕ → 𝕜) i else 0 := by
  change (∑ j ∈ Finset.range N, lp.single 2 j (y j) : ℓ²(ℕ, 𝕜)) i = _
  rw [lp.coeFn_sum]
  simp only [Finset.sum_apply, lp.single_apply, Pi.single_apply, Finset.sum_ite_eq,
    Finset.mem_range]

/-- The squared norm of a truncation is the partial sum of squared norms. -/
theorem trunc_norm_sq (N : ℕ) (y : ℓ²(ℕ, 𝕜)) :
    ‖trunc N y‖ ^ 2 = ∑ i ∈ Finset.range N, ‖(y : ℕ → 𝕜) i‖ ^ 2 := by
  rw [norm_sq_eq_tsum, tsum_eq_sum (s := Finset.range N)
    (f := fun i => ‖(trunc N y : ℕ → 𝕜) i‖ ^ 2)
    (fun i hi => by
      rw [trunc_apply, ite_eq_right (fun hlt => hi (Finset.mem_range.mpr hlt))]
      simp)]
  exact Finset.sum_congr rfl fun i hi => by
    simp only [trunc_apply, ite_eq_left (Finset.mem_range.mp hi)]

/-- A truncation does not increase the norm. -/
theorem norm_trunc_le (N : ℕ) (y : ℓ²(ℕ, 𝕜)) : ‖trunc N y‖ ≤ ‖y‖ := by
  have hsum := summable_norm_sq y
  have hsplit := hsum.sum_add_tsum_nat_add N
  have htail : 0 ≤ ∑' (i : ℕ), ‖(y : ℕ → 𝕜) (i + N)‖ ^ 2 :=
    tsum_nonneg fun i => by positivity
  exact le_of_sq_le_sq (by rw [trunc_norm_sq, norm_sq_eq_tsum]; linarith) (norm_nonneg _)

/-- The squared norm of the truncation error is total minus partial sum. -/
theorem trunc_sub_norm_sq (N : ℕ) (y : ℓ²(ℕ, 𝕜)) :
    ‖trunc N y - y‖ ^ 2 =
      ∑' i, ‖(y : ℕ → 𝕜) i‖ ^ 2 - ∑ i ∈ Finset.range N, ‖(y : ℕ → 𝕜) i‖ ^ 2 := by
  have hsum := summable_norm_sq y
  have hcoord : ∀ i, ((trunc N y - y : ℓ²(ℕ, 𝕜)) : ℕ → 𝕜) i =
      if i < N then 0 else -(y : ℕ → 𝕜) i := by
    intro i
    rw [lp.coeFn_sub, Pi.sub_apply, trunc_apply]
    by_cases hi : i < N <;> simp [hi]
  have hnorm : ∀ i, ‖((trunc N y - y : ℓ²(ℕ, 𝕜)) : ℕ → 𝕜) i‖ ^ 2 =
      ‖(y : ℕ → 𝕜) i‖ ^ 2 - (if i < N then ‖(y : ℕ → 𝕜) i‖ ^ 2 else 0) := by
    intro i
    rw [hcoord]
    by_cases hi : i < N <;> simp [hi]
  have hsumh : Summable (fun j => if j < N then ‖(y : ℕ → 𝕜) j‖ ^ 2 else 0) :=
    summable_of_ne_finset_zero (s := Finset.range N) (fun j hj => by
      rw [ite_eq_right (fun hlt => hj (Finset.mem_range.mpr hlt))])
  rw [norm_sq_eq_tsum]
  simp only [hnorm]
  rw [hsum.tsum_sub hsumh,
    tsum_eq_sum (s := Finset.range N)
      (f := fun j => if j < N then ‖(y : ℕ → 𝕜) j‖ ^ 2 else 0) (fun j hj => by
        rw [ite_eq_right (fun hlt => hj (Finset.mem_range.mpr hlt))])]
  rw [show (∑ i ∈ Finset.range N, (if i < N then ‖(y : ℕ → 𝕜) i‖ ^ 2 else 0))
        = ∑ i ∈ Finset.range N, ‖(y : ℕ → 𝕜) i‖ ^ 2 from
    Finset.sum_congr rfl fun j hj => by rw [ite_eq_left (Finset.mem_range.mp hj)]]

/-- Truncations converge to the original vector as `N → ∞`. -/
theorem tendsto_norm_trunc_sub (y : ℓ²(ℕ, 𝕜)) :
    Tendsto (fun N => ‖trunc N y - y‖) atTop (𝓝 0) := by
  have hsum := summable_norm_sq y
  have hsq : Tendsto (fun N => ‖trunc N y - y‖ ^ 2) atTop (𝓝 0) := by
    have hlim : Tendsto (fun N => ∑ i ∈ Finset.range N, ‖(y : ℕ → 𝕜) i‖ ^ 2) atTop
        (𝓝 (∑' i, ‖(y : ℕ → 𝕜) i‖ ^ 2)) := hsum.tendsto_sum_tsum_nat
    have hsub : Tendsto (fun N => ∑' i, ‖(y : ℕ → 𝕜) i‖ ^ 2 -
        ∑ i ∈ Finset.range N, ‖(y : ℕ → 𝕜) i‖ ^ 2) atTop
        (𝓝 (∑' i, ‖(y : ℕ → 𝕜) i‖ ^ 2 - ∑' i, ‖(y : ℕ → 𝕜) i‖ ^ 2)) :=
      tendsto_const_nhds.sub hlim
    rw [sub_self] at hsub
    exact hsub.congr (fun N => (trunc_sub_norm_sq N y).symm)
  have hsqrt : Tendsto (fun N => Real.sqrt (‖trunc N y - y‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) :=
    hsq.sqrt
  rw [Real.sqrt_zero] at hsqrt
  exact hsqrt.congr (fun N => Real.sqrt_sq (norm_nonneg _))

/-! ### The periodic approximant -/

/-- The periodic extension of the truncation of `y` to its first `N`
coordinates: the geometric series over forward shifts by blocks of
length `N`, with coefficients `(μ⁻¹ ^ N) ^ m`. -/
noncomputable def periodicApprox (μ : 𝕜) (N : ℕ) (y : ℓ²(ℕ, 𝕜)) : ℓ²(ℕ, 𝕜) :=
  ∑' m : ℕ, (μ⁻¹ ^ N) ^ m • ((shiftCLM ^ N) ^ m) (trunc N y)

/-- The geometric ratio `‖μ⁻¹ ^ N‖` is `< 1` when `‖μ‖ > 1` and `N > 0`. -/
theorem norm_inv_pow_lt_one {μ : 𝕜} (hμ : 1 < ‖μ‖) {N : ℕ} (hN : 0 < N) :
    ‖μ⁻¹ ^ N‖ < 1 := by
  rw [norm_pow, norm_inv]
  exact pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hμ) (Nat.ne_of_gt hN)

/-- The geometric series bounding the periodic approximant terms is summable. -/
theorem summable_geom_trunc {μ : 𝕜} (hμ : 1 < ‖μ‖) {N : ℕ} (hN : 0 < N) (y : ℓ²(ℕ, 𝕜)) :
    Summable (fun m => ‖μ⁻¹ ^ N‖ ^ m * ‖trunc N y‖) :=
  (summable_geometric_of_lt_one (show (0 : ℝ) ≤ ‖μ⁻¹ ^ N‖ by positivity)
    (norm_inv_pow_lt_one hμ hN)).mul_right _

/-- The norm of a term of the periodic approximant. -/
theorem norm_periodicApprox_term (μ : 𝕜) (N m : ℕ) (y : ℓ²(ℕ, 𝕜)) :
    ‖(μ⁻¹ ^ N) ^ m • ((shiftCLM ^ N) ^ m) (trunc N y)‖ =
      ‖μ⁻¹ ^ N‖ ^ m * ‖trunc N y‖ := by
  rw [norm_smul, norm_pow, ← pow_mul, norm_shiftCLM_pow_apply]

/-- Summability of the terms of the periodic approximant. -/
theorem summable_periodicApprox_terms {μ : 𝕜} (hμ : 1 < ‖μ‖) {N : ℕ} (hN : 0 < N)
    (y : ℓ²(ℕ, 𝕜)) :
    Summable (fun m => (μ⁻¹ ^ N) ^ m • ((shiftCLM ^ N) ^ m) (trunc N y)) := by
  apply Summable.of_norm_bounded (summable_geom_trunc hμ hN y)
  intro m
  exact le_of_eq (norm_periodicApprox_term μ N m y)

/-- The `m = 0` term of the periodic approximant is the truncation. -/
theorem periodicApprox_term_zero (μ : 𝕜) (N : ℕ) (y : ℓ²(ℕ, 𝕜)) :
    (μ⁻¹ ^ N) ^ 0 • ((shiftCLM ^ N) ^ 0) (trunc N y) = trunc N y := by
  simp

/-- Applying the backward shift `N` times to a truncation gives `0`. -/
theorem backwardCLM_pow_trunc (N : ℕ) (y : ℓ²(ℕ, 𝕜)) :
    (backwardCLM ^ N) (trunc N y) = 0 := by
  apply lp.ext
  funext i
  rw [backwardCLM_pow_apply, trunc_apply,
    ite_eq_right (by omega : ¬ i + N < N)]
  simp

/-- How `(μ • B) ^ N` acts on a term of the periodic approximant:
the `m = 0` term is killed, and every later term shifts down by one. -/
theorem periodicApprox_step {μ : 𝕜} (hμ : 1 < ‖μ‖) {N : ℕ}
    (y : ℓ²(ℕ, 𝕜)) (m : ℕ) : ((μ • backwardCLM) ^ N)
      ((μ⁻¹ ^ N) ^ m • ((shiftCLM ^ N) ^ m) (trunc N y)) =
    if m = 0 then 0 else (μ⁻¹ ^ N) ^ (m - 1) • ((shiftCLM ^ N) ^ (m - 1)) (trunc N y) := by
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hμ
    norm_num at hμ
  rw [smul_backwardCLM_pow, map_smul, smul_apply, smul_smul]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [ite_eq_left rfl]
    simp only [pow_zero, one_mul, one_apply_eq_self]
    rw [backwardCLM_pow_trunc]
    exact smul_zero _
  · rw [ite_eq_right (Nat.ne_of_gt hm)]
    have hcancel : μ ^ N * (μ⁻¹ ^ N) ^ m = (μ⁻¹ ^ N) ^ (m - 1) := by
      have hr_eq : (μ⁻¹ ^ N) ^ m = (μ⁻¹ ^ N) * (μ⁻¹ ^ N) ^ (m - 1) := by
        conv_lhs => rw [← Nat.succ_pred_eq_of_pos hm, pow_succ', Nat.pred_eq_sub_one]
      rw [hr_eq]
      calc μ ^ N * ((μ⁻¹ ^ N) * (μ⁻¹ ^ N) ^ (m - 1))
          = (μ ^ N * (μ⁻¹ ^ N)) * (μ⁻¹ ^ N) ^ (m - 1) := by ring
        _ = (μ⁻¹ ^ N) ^ (m - 1) := by
            rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero N hμ0), one_mul]
    have hshift : (backwardCLM ^ N) (((shiftCLM ^ N) ^ m) (trunc N y)) =
        ((shiftCLM ^ N) ^ (m - 1)) (trunc N y) := by
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos hm, pow_succ', mul_apply_eq_comp,
        Nat.pred_eq_sub_one]
      exact backwardCLM_pow_shiftCLM_pow_apply N _
    rw [hshift, mul_comm ((μ⁻¹ ^ N) ^ m) (μ ^ N), hcancel]

/-- Summability of the terms of the periodic approximant after applying
`(μ • B) ^ N`. -/
theorem summable_periodicApprox_map {μ : 𝕜} (hμ : 1 < ‖μ‖) {N : ℕ} (hN : 0 < N)
    (y : ℓ²(ℕ, 𝕜)) : Summable (fun m => ((μ • backwardCLM) ^ N)
      ((μ⁻¹ ^ N) ^ m • ((shiftCLM ^ N) ^ m) (trunc N y))) := by
  apply Summable.of_norm_bounded (g := fun m => ‖(μ • backwardCLM (𝕜 := 𝕜)) ^ N‖ *
    (‖μ⁻¹ ^ N‖ ^ m * ‖trunc N y‖))
  · exact (summable_geom_trunc hμ hN y).mul_left _
  · intro m
    calc ‖((μ • backwardCLM) ^ N)
            ((μ⁻¹ ^ N) ^ m • ((shiftCLM ^ N) ^ m) (trunc N y))‖
        ≤ ‖(μ • backwardCLM (𝕜 := 𝕜)) ^ N‖ *
            ‖(μ⁻¹ ^ N) ^ m • ((shiftCLM ^ N) ^ m) (trunc N y)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖(μ • backwardCLM (𝕜 := 𝕜)) ^ N‖ * (‖μ⁻¹ ^ N‖ ^ m * ‖trunc N y‖) := by
          rw [norm_periodicApprox_term]

/-- The periodic approximant is periodic of period `N` when `‖μ‖ > 1`. -/
theorem periodicApprox_isPeriodicPoint {μ : 𝕜} (hμ : 1 < ‖μ‖) {N : ℕ} (hN : 0 < N)
    (y : ℓ²(ℕ, 𝕜)) : Function.IsPeriodicPt (⇑(μ • backwardCLM)) N (periodicApprox μ N y) := by
  have hterm := summable_periodicApprox_terms hμ hN y
  have hsum := summable_periodicApprox_map hμ hN y
  apply (isPeriodicPt_iff_pow_apply_eq _ _ _).mpr
  rw [periodicApprox, ((μ • backwardCLM) ^ N).map_tsum hterm]
  rw [hsum.tsum_eq_zero_add, periodicApprox_step hμ y 0, ite_eq_left rfl, zero_add]
  change ∑' (m : ℕ), ((μ • backwardCLM) ^ N)
        ((μ⁻¹ ^ N) ^ (m + 1) • ((shiftCLM ^ N) ^ (m + 1)) (trunc N y)) =
      ∑' (m : ℕ), (μ⁻¹ ^ N) ^ m • ((shiftCLM ^ N) ^ m) (trunc N y)
  exact tsum_congr (fun m => by
    rw [periodicApprox_step hμ y (m + 1), ite_eq_right (by omega : ¬ m + 1 = 0),
      Nat.add_sub_cancel])

/-- The distance from the periodic approximant to the truncation is at
most the geometric tail `(r / (1 - r)) * ‖y‖`, where `r = ‖μ‖⁻¹ ^ N`. -/
theorem norm_periodicApprox_sub_trunc {μ : 𝕜} (hμ : 1 < ‖μ‖) {N : ℕ} (hN : 0 < N)
    (y : ℓ²(ℕ, 𝕜)) :
    ‖periodicApprox μ N y - trunc N y‖ ≤
      (‖μ‖⁻¹ ^ N / (1 - ‖μ‖⁻¹ ^ N)) * ‖y‖ := by
  have hr0 : 0 ≤ ‖μ‖⁻¹ ^ N := by positivity
  have hr1 : ‖μ‖⁻¹ ^ N < 1 := by
    have h := norm_inv_pow_lt_one hμ hN
    rwa [norm_pow, norm_inv] at h
  have hterm := summable_periodicApprox_terms hμ hN y
  have hsub : periodicApprox μ N y - trunc N y =
      ∑' m, (μ⁻¹ ^ N) ^ (m + 1) • ((shiftCLM ^ N) ^ (m + 1)) (trunc N y) := by
    rw [periodicApprox, hterm.tsum_eq_zero_add, periodicApprox_term_zero, add_sub_cancel_left]
  have hnorm : ∀ m, ‖(μ⁻¹ ^ N) ^ (m + 1) • ((shiftCLM ^ N) ^ (m + 1)) (trunc N y)‖ =
      (‖μ‖⁻¹ ^ N) ^ (m + 1) * ‖trunc N y‖ := by
    intro m
    rw [norm_smul, norm_pow, ← pow_mul, norm_shiftCLM_pow_apply, norm_pow, norm_inv]
  have hsum : Summable (fun m => ‖(μ⁻¹ ^ N) ^ (m + 1) •
      ((shiftCLM ^ N) ^ (m + 1)) (trunc N y)‖) := by
    have hgeom : Summable (fun m => (‖μ‖⁻¹ ^ N) ^ (m + 1) * ‖trunc N y‖) := by
      have h2 := (summable_geometric_of_lt_one hr0 hr1).mul_right ‖trunc N y‖
      exact (summable_nat_add_iff 1).mpr h2
    exact Summable.congr hgeom (fun m => (hnorm m).symm)
  calc ‖periodicApprox μ N y - trunc N y‖
      = ‖∑' m, (μ⁻¹ ^ N) ^ (m + 1) • ((shiftCLM ^ N) ^ (m + 1)) (trunc N y)‖ := by
        rw [hsub]
    _ ≤ ∑' m, ‖(μ⁻¹ ^ N) ^ (m + 1) • ((shiftCLM ^ N) ^ (m + 1)) (trunc N y)‖ :=
        norm_tsum_le_tsum_norm hsum
    _ = ∑' m, (‖μ‖⁻¹ ^ N) ^ (m + 1) * ‖trunc N y‖ := tsum_congr hnorm
    _ = (‖μ‖⁻¹ ^ N / (1 - ‖μ‖⁻¹ ^ N)) * ‖trunc N y‖ := by
        rw [tsum_mul_right]
        have hgeo : ∑' m, (‖μ‖⁻¹ ^ N) ^ (m + 1) = ‖μ‖⁻¹ ^ N / (1 - ‖μ‖⁻¹ ^ N) := by
          have h := (summable_geometric_of_lt_one hr0 hr1).tsum_eq_zero_add
          rw [tsum_geometric_of_lt_one hr0 hr1, pow_zero] at h
          have hne : (1 : ℝ) - ‖μ‖⁻¹ ^ N ≠ 0 := by
            have hpos : (0 : ℝ) < 1 - ‖μ‖⁻¹ ^ N := by linarith
            exact ne_of_gt hpos
          have hsub : ∑' m, (‖μ‖⁻¹ ^ N) ^ (m + 1) = (1 - ‖μ‖⁻¹ ^ N)⁻¹ - 1 := by linarith
          rw [hsub, eq_comm, div_eq_iff hne, sub_mul, inv_mul_cancel₀ hne, one_mul]
          ring
        rw [hgeo]
    _ ≤ (‖μ‖⁻¹ ^ N / (1 - ‖μ‖⁻¹ ^ N)) * ‖y‖ := by
        apply mul_le_mul_of_nonneg_left (norm_trunc_le N y)
        exact div_nonneg hr0 (by linarith)

/-! ### Density of periodic points when `‖μ‖ > 1` -/

/-- The periodic points of `μ • B` are dense when `‖μ‖ > 1`. -/
theorem dense_periodicPoints_of_one_lt_norm {μ : 𝕜} (hμ : 1 < ‖μ‖) :
    Dense (Function.periodicPts (⇑(μ • backwardCLM (𝕜 := 𝕜)))) := by
  change ∀ x, x ∈ closure (Function.periodicPts (⇑(μ • backwardCLM (𝕜 := 𝕜))))
  intro y
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hbound : Tendsto (fun N => ‖trunc N y - y‖ +
      ‖y‖ * (‖μ‖⁻¹ ^ N / (1 - ‖μ‖⁻¹ ^ N))) atTop (𝓝 0) := by
    have hr : Tendsto (fun N => ‖μ‖⁻¹ ^ N) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
        (inv_lt_one_of_one_lt₀ hμ)
    have hdiv : Tendsto (fun N => ‖μ‖⁻¹ ^ N / (1 - ‖μ‖⁻¹ ^ N)) atTop (𝓝 (0 / (1 - 0))) :=
      hr.div (tendsto_const_nhds.sub hr) (by norm_num)
    rw [zero_div] at hdiv
    have hmul : Tendsto (fun N => ‖y‖ * (‖μ‖⁻¹ ^ N / (1 - ‖μ‖⁻¹ ^ N))) atTop (𝓝 (‖y‖ * 0)) :=
      tendsto_const_nhds.mul hdiv
    rw [mul_zero] at hmul
    have hadd := (tendsto_norm_trunc_sub y).add hmul
    rw [add_zero] at hadd
    exact hadd
  obtain ⟨N, hN1, hNbound⟩ :=
    ((Filter.eventually_ge_atTop 1).and (hbound.eventually (Iio_mem_nhds hε))).exists
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN1
  refine ⟨periodicApprox μ N y,
    Function.mk_mem_periodicPts hNpos (periodicApprox_isPeriodicPoint hμ hNpos y), ?_⟩
  rw [dist_eq_norm]
  calc ‖y - periodicApprox μ N y‖
      = ‖(y - trunc N y) + (trunc N y - periodicApprox μ N y)‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ ‖y - trunc N y‖ + ‖trunc N y - periodicApprox μ N y‖ := norm_add_le _ _
    _ = ‖trunc N y - y‖ + ‖periodicApprox μ N y - trunc N y‖ := by
        rw [norm_sub_rev y (trunc N y), norm_sub_rev (trunc N y) (periodicApprox μ N y)]
    _ ≤ ‖trunc N y - y‖ + (‖μ‖⁻¹ ^ N / (1 - ‖μ‖⁻¹ ^ N)) * ‖y‖ :=
        add_le_add le_rfl (norm_periodicApprox_sub_trunc hμ hNpos y)
    _ = ‖trunc N y - y‖ + ‖y‖ * (‖μ‖⁻¹ ^ N / (1 - ‖μ‖⁻¹ ^ N)) := by ring
    _ < ε := hNbound

/-! ### Only `0` is periodic when `‖μ‖ ≤ 1` -/

/-- If `x` is periodic for `μ • B`, its coordinates satisfy
`x k = μ ^ (n * m) * x (k + n * m)` for all `m`. -/
theorem periodic_coord_iterate {μ : 𝕜} {n : ℕ} {x : ℓ²(ℕ, 𝕜)}
    (hx : Function.IsPeriodicPt (⇑(μ • backwardCLM)) n x) (k : ℕ) (m : ℕ) :
    (x : ℕ → 𝕜) k = μ ^ (n * m) * (x : ℕ → 𝕜) (k + n * m) := by
  have hxpow := (isPeriodicPt_iff_pow_apply_eq _ _ _).mp hx
  have step : ∀ j, (x : ℕ → 𝕜) j = μ ^ n * (x : ℕ → 𝕜) (j + n) := by
    intro j
    have hpt : (((μ • backwardCLM) ^ n) x : ℕ → 𝕜) j = (x : ℕ → 𝕜) j := by
      rw [hxpow]
    rw [smul_backwardCLM_pow_apply_coord] at hpt
    exact hpt.symm
  induction m with
  | zero => simp
  | succ m ih =>
    have h2 : n * (m + 1) = n * m + n := by ring
    have h1 : (x : ℕ → 𝕜) (k + n * m) =
        μ ^ n * (x : ℕ → 𝕜) (k + n * m + n) := step _
    rw [h2, ← Nat.add_assoc, ih, h1, ← mul_assoc, ← pow_add]

/-- The coordinates of an `ℓ²` vector tend to `0`. -/
theorem tendsto_norm_coord (x : ℓ²(ℕ, 𝕜)) :
    Tendsto (fun j => ‖(x : ℕ → 𝕜) j‖) atTop (𝓝 0) := by
  have hsum := summable_norm_sq x
  have h0 : Tendsto (fun j => ‖(x : ℕ → 𝕜) j‖ ^ 2) atTop (𝓝 0) := hsum.tendsto_atTop_zero
  have hsqrt : Tendsto (fun j => Real.sqrt (‖(x : ℕ → 𝕜) j‖ ^ 2)) atTop
      (𝓝 (Real.sqrt 0)) := h0.sqrt
  rw [Real.sqrt_zero] at hsqrt
  exact hsqrt.congr (fun j => Real.sqrt_sq (norm_nonneg _))

/-- The only periodic point of `μ • B` is `0` when `‖μ‖ ≤ 1`. -/
theorem eq_zero_of_isPeriodicPoint_of_norm_le_one {μ : 𝕜} (hμ : ‖μ‖ ≤ 1) {n : ℕ} (hn : 0 < n)
    {x : ℓ²(ℕ, 𝕜)} (hx : Function.IsPeriodicPt (⇑(μ • backwardCLM)) n x) : x = 0 := by
  apply lp.ext
  funext k
  simp only [lp.coeFn_zero, Pi.zero_apply]
  have hseq : Tendsto (fun m => ‖(x : ℕ → 𝕜) (k + n * m)‖) atTop (𝓝 0) := by
    apply (tendsto_norm_coord x).comp
    apply Filter.tendsto_atTop.2
    intro b
    exact Filter.eventually_atTop.2 ⟨b, fun m hm => le_trans hm (by
      calc m ≤ n * m := Nat.le_mul_of_pos_left m hn
      _ ≤ k + n * m := Nat.le_add_left _ _)⟩
  have hle : ∀ m, ‖(x : ℕ → 𝕜) k‖ ≤ ‖(x : ℕ → 𝕜) (k + n * m)‖ := by
    intro m
    have h := congrArg (‖·‖) (periodic_coord_iterate hx k m)
    rw [norm_mul, norm_pow] at h
    rw [h]
    have hpow : ‖μ‖ ^ (n * m) ≤ 1 := pow_le_one₀ (norm_nonneg _) hμ
    exact mul_le_of_le_one_left (norm_nonneg _) hpow
  have hzero : ‖(x : ℕ → 𝕜) k‖ ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hseq (Filter.Eventually.of_forall hle)
  exact norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _))

/-! ### The dichotomy -/

/-- The periodic points of `μ • B` are dense if and only if `‖μ‖ > 1`. -/
theorem dense_periodicPoints_iff (μ : 𝕜) :
    Dense (Function.periodicPts (⇑(μ • backwardCLM (𝕜 := 𝕜)))) ↔
      1 < ‖μ‖ := by
  constructor
  · intro h
    by_contra hle
    rw [not_lt] at hle
    have hset : (Function.periodicPts (⇑(μ • backwardCLM (𝕜 := 𝕜)))) = {0} := by
      ext x
      rw [Function.mem_periodicPts, Set.mem_singleton_iff]
      constructor
      · rintro ⟨n, hn, hx⟩
        exact eq_zero_of_isPeriodicPoint_of_norm_le_one hle hn hx
      · intro hx
        exact ⟨1, one_pos, by rw [hx]; exact isPeriodicPoint_zero _ _⟩
    have hmem : (lp.single 2 0 (1 : 𝕜) : ℓ²(ℕ, 𝕜)) ∈
        closure ({0} : Set (ℓ²(ℕ, 𝕜))) := by
      have hc : closure ({0} : Set (ℓ²(ℕ, 𝕜))) = Set.univ := by
        have hd := h
        rw [hset] at hd
        exact Dense.closure_eq hd
      rw [hc]
      exact Set.mem_univ _
    rw [isClosed_singleton.closure_eq] at hmem
    have hsingle : (lp.single 2 0 (1 : 𝕜) : ℓ²(ℕ, 𝕜)) = 0 := Set.mem_singleton_iff.mp hmem
    have hnorm : ‖(lp.single 2 0 (1 : 𝕜) : ℓ²(ℕ, 𝕜))‖ = 1 := by
      rw [lp.norm_single (by simp : (0 : ℝ≥0∞) < 2), norm_one]
    rw [hsingle, norm_zero] at hnorm
    norm_num at hnorm
  · intro h
    exact dense_periodicPoints_of_one_lt_norm h

end MathlibExt.Analysis.FunctionalAnalysis.RolewiczPeriodic
