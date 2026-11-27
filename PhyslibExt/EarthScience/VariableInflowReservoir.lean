/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.ODE.ScalarRelaxation
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ProjIcc

/-!
# Linear reservoir with variable inflow

The scalar relaxation convolution gives the storage of a linear reservoir on a finite interval.

## i. Overview

With inflow `I` and outflow `Q = k S`, storage solves `S' = I - k S`. Only the values of `I`
on `[0,T]` enter the solution there. To use the scalar relaxation derivative, extend the inflow
by its endpoint values and restrict the resulting convolution back to `[0,T]`. Uniqueness is
local: for two solutions the integrating factor times their difference has zero derivative on
`(0,T)`. Continuity, not differentiability, is needed at the endpoints.

## ii. Key results

* `EarthScience.IsReservoirStorageOn.eqOn`: two storage histories with the same data agree on
  the whole closed interval.
* `EarthScience.linearReservoirWithVariableInflow`: the storage and outflow convolutions, the
  closed water budget, and preservation of nonnegativity.

## iii. Table of contents

* A. The storage equation and uniqueness
* B. The variable-inflow solution and budget

## iv. References

* J. Lebl, [*Notes on Diffy Qs: Differential Equations for Engineers*](https://www.jirka.org/diffyqs/),
  version 6.11, §1.4, pp. 40–41: integrating factors and the definite-integral formula (1.4).
-/

@[expose] public section

open Set Real
open MathlibExt.Biology.Dynamics.FeedForwardLoop (relaxation hasDerivAt_relaxation)

namespace EarthScience

/-! ## A. The storage equation and uniqueness -/

/-- A storage history has initial storage `S₀`, is continuous on `[0,T]`, and has derivative
`I(t) - k S(t)` on `(0,T)`. For `0 ≤ T` there is no condition outside `[0,T]`. -/
structure IsReservoirStorageOn (T k : ℝ) (I : ℝ → ℝ) (S₀ : ℝ) (S : ℝ → ℝ) : Prop where
  /-- Initial storage. -/
  initial : S 0 = S₀
  /-- Storage is continuous up to both endpoints. -/
  continuousOn : ContinuousOn S (Icc 0 T)
  /-- In the interior, the storage rate is inflow minus outflow. -/
  rate : ∀ t ∈ Ioo 0 T, HasDerivAt S (I t - k * S t) t

/-- Two storage histories satisfying the same initial-value problem agree on `[0,T]`,
regardless of their values outside that interval. -/
lemma IsReservoirStorageOn.eqOn {T k S₀ : ℝ} {I X Y : ℝ → ℝ}
    (hX : IsReservoirStorageOn T k I S₀ X) (hY : IsReservoirStorageOn T k I S₀ Y) :
    EqOn X Y (Icc 0 T) := by
  let d := fun t ↦ exp (k * t) * (X t - Y t)
  have hc : ContinuousOn d (Icc 0 T) :=
    (by fun_prop : Continuous fun t : ℝ ↦ exp (k * t)).continuousOn.mul
      (hX.continuousOn.sub hY.continuousOn)
  have hd (t) (ht : t ∈ Ioo 0 T) : HasDerivAt d 0 t := by
    have h := (((hasDerivAt_id' t).const_mul k).exp).mul ((hX.rate t ht).sub (hY.rate t ht))
    apply h.congr_deriv
    simp only [Pi.sub_apply]
    ring
  intro t ht
  have hz := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f' := fun _ ↦ (0 : ℝ)) ht.1
    (hc.mono (Icc_subset_Icc_right ht.2))
    (fun u hu ↦ hd u ⟨hu.1, hu.2.trans_le ht.2⟩) intervalIntegrable_const
  have heq : d t = d 0 := sub_eq_zero.mp (by
    simpa only [intervalIntegral.integral_zero] using hz.symm)
  simpa [d, hX.initial, hY.initial, sub_eq_zero] using heq

/-! ## B. The variable-inflow solution and budget -/

private lemma relaxation_isStorageOn {T : ℝ} (hT : 0 ≤ T) (k S₀ : ℝ) {I : ℝ → ℝ}
    (hI : ContinuousOn I (Icc 0 T)) : IsReservoirStorageOn T k I S₀ (relaxation k I S₀) := by
  let J := IccExtend hT (fun t : Icc 0 T ↦ I t)
  have hc : Continuous J :=
    continuous_IccExtend_iff.mpr (continuousOn_iff_continuous_domRestrict.mp hI)
  have hJ : EqOn J I (Icc 0 T) := fun _ ht ↦ IccExtend_of_mem hT _ ht
  have hS : EqOn (relaxation k I S₀) (relaxation k J S₀) (Icc 0 T) := by
    intro t ht
    simp only [relaxation, add_right_inj]
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' := uIcc_subset_Icc (left_mem_Icc.mpr hT) ht hu
    exact congrArg (exp (-k * (t - u)) * ·) (hJ hu').symm
  have hd (t : ℝ) := hasDerivAt_relaxation (α := k) S₀ hc.intervalIntegrable
    (hc.continuousAt (x := t))
  refine ⟨by simp [relaxation], (continuous_iff_continuousAt.mpr fun t ↦
    (hd t).continuousAt).continuousOn.congr hS, ?_⟩
  intro t ht
  have hnear := hS.eventuallyEq_of_mem (Icc_mem_nhds ht.1 ht.2)
  simpa only [hJ (mem_Icc_of_Ioo ht), ← hS (mem_Icc_of_Ioo ht)] using
    (hd t).congr_of_eventuallyEq hnear

/-- Let `T ≥ 0`, let `k` and the initial storage `S₀` be real, and let the inflow `I` be
continuous on `[0,T]`. For `0 ≤ t ≤ T`, the storage is
`S(t) = S₀ exp(-kt) + ∫₀ᵗ exp(-k(t-u)) I(u) du`.
It is continuous on `[0,T]`, starts at `S(0) = S₀`, and satisfies `S′(t) = I(t) - k S(t)`
for `0 < t < T`. If `Y` is continuous on `[0,T]`, has `Y(0) = S₀`, and satisfies the same
ODE on `(0,T)`, then `Y(t) = S(t)` for every `t ∈ [0,T]`. No endpoint derivatives or conditions
outside `[0,T]` are required.

The outflow `Q(t) = k S(t)` satisfies `Q(t) = k S₀ exp(-kt) + ∫₀ᵗ k exp(-k(t-u)) I(u) du` for
`0 ≤ t ≤ T`, and the terminal water budget is `S(T) - S₀ = ∫₀ᵀ (I(u) - Q(u)) du`.
If `S₀ ≥ 0` and `I(u) ≥ 0` for every `u ∈ [0,T]`, then `S(t) ≥ 0` for every `t ∈ [0,T]`. -/
theorem linearReservoirWithVariableInflow {T : ℝ} (hT : 0 ≤ T) (k S₀ : ℝ) {I : ℝ → ℝ}
    (hI : ContinuousOn I (Icc 0 T)) :
    let S := relaxation k I S₀
    let Q := fun t ↦ k * S t
    IsReservoirStorageOn T k I S₀ S ∧
      (∀ Y, IsReservoirStorageOn T k I S₀ Y → EqOn Y S (Icc 0 T)) ∧
      (∀ t ∈ Icc 0 T, Q t = k * S₀ * exp (-k * t) +
        ∫ u in (0 : ℝ)..t, k * exp (-k * (t - u)) * I u) ∧
      S T - S₀ = (∫ t in (0 : ℝ)..T, I t - Q t) ∧
      (0 ≤ S₀ → (∀ u ∈ Icc 0 T, 0 ≤ I u) → ∀ t ∈ Icc 0 T, 0 ≤ S t) := by
  dsimp only
  have hS := relaxation_isStorageOn hT k S₀ hI
  refine ⟨hS, fun _ hY ↦ hY.eqOn hS, ?_, ?_, ?_⟩
  · intro t _
    simp only [relaxation, mul_add, mul_assoc, intervalIntegral.integral_const_mul]
  · simpa only [hS.initial] using (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      hT hS.continuousOn hS.rate
      ((hI.sub (continuousOn_const.mul hS.continuousOn)).intervalIntegrable_of_Icc hT)).symm
  · intro h₀ hpos t ht
    exact add_nonneg (mul_nonneg h₀ (exp_pos _).le) (intervalIntegral.integral_nonneg ht.1
      fun u hu ↦ mul_nonneg (exp_pos _).le (hpos u ⟨hu.1, hu.2.trans ht.2⟩))

end EarthScience
