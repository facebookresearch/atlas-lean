/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic

import MathlibExt.Analysis.InnerProductSpace.NormDerivative
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Gradient of the point-mass potential is inward

## i. Overview

Outside the origin, the point-mass potential `Φ(x) = -G * M / ‖x‖`
has the full vector gradient `(G * M / ‖x‖ ^ 3) • x`, for any real
coefficients `G` and `M`. The acceleration `-∇Φ` is therefore
`-(G * M / ‖x‖ ^ 3) • x`, and for `G, M > 0` it points inward:
its inner product with the outward position vector `x` is
`-(G * M / ‖x‖) < 0`. This is the full vector gradient, not only the
radial derivative proved for the one-dimensional profile in the
gravity-potential module. The derivative of the norm comes from
`MathlibExt.Analysis.InnerProductSpace.NormDerivative.hasFDerivAt_norm`.

## ii. Key results

- `EarthScience.hasGradientAt_pointMass_potential`: the gradient of
  `-G * M / ‖x‖` away from the origin, with no sign condition on `G`, `M`.
- `EarthScience.pointMass_gradient_inward`: that gradient and the
  inwardness of `-∇Φ` for `G, M > 0`.

## iii. Table of contents

- A. Point-mass gradient

## iv. References

- `MathlibExt.Analysis.InnerProductSpace.NormDerivative.hasFDerivAt_norm`
  (derivative of the norm away from the origin).
- `hasFDerivAt_inv`, `HasFDerivAt.comp`, `HasFDerivAt.const_mul`,
  `hasGradientAt_iff_hasFDerivAt` in Mathlib.
- `InnerProductSpace.toDual_apply_apply` in Mathlib.
-/

@[expose] public section

open InnerProductSpace Real Filter Topology

namespace EarthScience

/-! ## A. Point-mass gradient -/

/-- Outside the origin, the gradient of the point-mass potential
`Φ(x) = -G*M/‖x‖` is `(G*M/‖x‖^3) • x`. The formula holds for all real
`G` and `M`, including zero and negative values. -/
theorem hasGradientAt_pointMass_potential
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {G M : ℝ} {x : E} (hx : x ≠ 0) :
    HasGradientAt (fun y => -G * M / ‖y‖) ((G * M / ‖x‖ ^ 3) • x) x := by
  have hnorm_ne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hnorm : HasFDerivAt (fun y : E => ‖y‖)
      ((‖x‖⁻¹ : ℝ) • MathlibExt.Analysis.InnerProductSpace.NormDerivative.reInnerSL ℝ x) x :=
    MathlibExt.Analysis.InnerProductSpace.NormDerivative.hasFDerivAt_norm (K := ℝ) hx
  have h := ((hasFDerivAt_inv hnorm_ne).comp x hnorm).const_mul (-G * M)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  · funext y
    simp [div_eq_mul_inv]
  · ext v
    simp [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.comp_apply]
    field

/-- Outside the origin, the gradient of the point-mass potential
`Φ(x) = -G*M/‖x‖` is `(G*M/‖x‖^3) • x` (`hasGradientAt_pointMass_potential`,
stated here through `toDual`), so the acceleration `-∇Φ` is
`-(G*M/‖x‖^3) • x`; for `G, M > 0` it points inward: its inner product with
the outward position vector `x` is negative. This is the full vector
gradient, not only the radial derivative. -/
theorem pointMass_gradient_inward
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {G M : ℝ} {x : E} (hx : x ≠ 0) (hG : 0 < G) (hM : 0 < M) :
    HasFDerivAt (fun y => -G * M / ‖y‖)
      (InnerProductSpace.toDual ℝ E ((G * M / ‖x‖ ^ 3) • x)) x ∧
    inner ℝ (-((G * M / ‖x‖ ^ 3) • x)) x < 0 := by
  refine ⟨(hasGradientAt_pointMass_potential hx).hasFDerivAt, ?_⟩
  have hnorm_ne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h_inner : inner ℝ (-((G * M / ‖x‖ ^ 3) • x)) x = -(G * M / ‖x‖) := by
    rw [inner_neg_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field
  have h_pos : 0 < G * M / ‖x‖ := div_pos (mul_pos hG hM) (norm_pos_iff.mpr hx)
  rw [h_inner]
  linarith

end EarthScience
