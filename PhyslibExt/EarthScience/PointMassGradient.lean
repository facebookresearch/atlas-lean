/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Basic

import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Gradient of the point-mass potential is inward

## i. Overview

Outside the origin, the point-mass potential `Φ(x) = -G * M / ‖x‖`
has the full vector gradient `(G * M / ‖x‖ ^ 3) • x`. The acceleration
`-∇Φ` is therefore `-(G * M / ‖x‖ ^ 3) • x`, and it points inward:
its inner product with the outward position vector `x` is
`-(G * M / ‖x‖) < 0` for `G, M > 0`. This is the three-dimensional
gradient, not only the radial derivative proved for the one-dimensional
profile in the gravity-potential module. The derivative of the norm is
obtained from the derivative of `‖x‖ ^ 2` via the square root.

## ii. Key results

- `EarthScience.pointMass_gradient_inward`: gradient of `-G * M / ‖x‖`
  and inwardness of `-∇Φ`.

## iii. Table of contents

- A. Point-mass gradient

## iv. References

- `hasStrictFDerivAt_norm_sq` in Mathlib (derivative of the squared norm).
- `HasFDerivAt.sqrt`, `HasFDerivAt.inv`, `HasFDerivAt.const_mul` in Mathlib.
- `InnerProductSpace.toDual_apply_apply` in Mathlib.
-/

@[expose] public section

open InnerProductSpace Real Filter Topology

namespace EarthScience

/-! ## A. Point-mass gradient -/

/-- Outside the origin, the gradient of the point-mass potential
`Φ(x) = -G*M/‖x‖` is `(G*M/‖x‖^3) • x`, so the acceleration `-∇Φ`
is `-(G*M/‖x‖^3) • x` and points inward: its inner product with the
outward position vector `x` is negative for `G, M > 0`. This is the
full vector gradient, not only the radial derivative. -/
theorem pointMass_gradient_inward
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {G M : ℝ} {x : E} (hx : x ≠ 0) (hG : 0 < G) (hM : 0 < M) :
    HasFDerivAt (fun y => -G * M / ‖y‖)
      (InnerProductSpace.toDual ℝ E ((G * M / ‖x‖ ^ 3) • x)) x ∧
    inner ℝ (-((G * M / ‖x‖ ^ 3) • x)) x < 0 := by
  have hnorm_ne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hsq_ne : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 hnorm_ne
  have hsq : HasFDerivAt (fun y : E => ‖y‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hsqrt : HasFDerivAt (fun y : E => √(‖y‖ ^ 2))
      ((1 / (2 * √(‖x‖ ^ 2))) • (2 • innerSL ℝ x)) x :=
    hsq.sqrt hsq_ne
  have h_eq : (fun y : E => ‖y‖) =ᶠ[nhds x] (fun y : E => √(‖y‖ ^ 2)) := by
    apply Eventually.of_forall
    intro y
    exact (Real.sqrt_sq (norm_nonneg y)).symm
  have hnorm : HasFDerivAt (fun y : E => ‖y‖) ((1 / (2 * √(‖x‖ ^ 2))) • (2 • innerSL ℝ x)) x :=
    hsqrt.congr_of_eventuallyEq h_eq
  have hsqrt_eq : √(‖x‖ ^ 2) = ‖x‖ := Real.sqrt_sq (norm_nonneg x)
  have h_simpl : ((1 / (2 * √(‖x‖ ^ 2))) • (2 • innerSL ℝ x)) = ((‖x‖⁻¹) • innerSL ℝ x) := by
    rw [hsqrt_eq]
    ext v
    simp [innerSL_apply_apply]
    field
  have hnorm' : HasFDerivAt (fun y : E => ‖y‖) ((‖x‖⁻¹) • innerSL ℝ x) x :=
    hnorm.congr_fderiv h_simpl
  have h_inv_base : HasFDerivAt (fun t : ℝ => t⁻¹)
      (ContinuousLinearMap.toSpanSingleton ℝ (-(‖x‖ ^ 2)⁻¹)) ‖x‖ :=
    hasFDerivAt_inv hnorm_ne
  have h_inv : HasFDerivAt ((fun t : ℝ => t⁻¹) ∘ (fun y : E => ‖y‖))
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(‖x‖ ^ 2)⁻¹)).comp ((‖x‖⁻¹) • innerSL ℝ x)) x :=
    h_inv_base.comp x hnorm'
  have h_inv' : HasFDerivAt (fun y : E => (‖y‖)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(‖x‖ ^ 2)⁻¹)).comp
        ((‖x‖⁻¹) • innerSL ℝ x)) x := h_inv
  have h_const : HasFDerivAt (fun y : E => (-G * M) * (‖y‖)⁻¹)
      ((-G * M) • ((ContinuousLinearMap.toSpanSingleton ℝ (-(‖x‖ ^ 2)⁻¹)).comp
        ((‖x‖⁻¹) • innerSL ℝ x))) x :=
    h_inv'.const_mul (-G * M)
  have h_eq2 : (fun y : E => -G * M / ‖y‖) =ᶠ[nhds x] (fun y : E => (-G * M) * (‖y‖)⁻¹) := by
    apply Eventually.of_forall
    intro y
    exact div_eq_mul_inv _ _
  have h_final_unsimpl : HasFDerivAt (fun y : E => -G * M / ‖y‖)
      ((-G * M) • ((ContinuousLinearMap.toSpanSingleton ℝ (-(‖x‖ ^ 2)⁻¹)).comp
        ((‖x‖⁻¹) • innerSL ℝ x))) x :=
    h_const.congr_of_eventuallyEq h_eq2
  have h_clm : ((-G * M) •
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(‖x‖ ^ 2)⁻¹)).comp
        ((‖x‖⁻¹) • innerSL ℝ x)))
      = InnerProductSpace.toDual ℝ E ((G * M / ‖x‖ ^ 3) • x) := by
    ext v
    simp [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply,
      ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.comp_apply]
    field
  have h_first : HasFDerivAt (fun y : E => -G * M / ‖y‖)
      (InnerProductSpace.toDual ℝ E ((G * M / ‖x‖ ^ 3) • x)) x :=
    h_final_unsimpl.congr_fderiv h_clm
  have h_inner : inner ℝ (-((G * M / ‖x‖ ^ 3) • x)) x = -(G * M / ‖x‖) := by
    rw [inner_neg_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field
  have h_pos : 0 < G * M / ‖x‖ := by
    apply div_pos (mul_pos hG hM)
    exact lt_of_le_of_ne (norm_nonneg x) (Ne.symm hnorm_ne)
  have h_second : inner ℝ (-((G * M / ‖x‖ ^ 3) • x)) x < 0 := by
    rw [h_inner]
    linarith
  exact ⟨h_first, h_second⟩

end EarthScience
