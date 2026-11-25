/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Electromagnetism.SkinDepthApproximation

/-!
# Tests for `PhyslibExt.Electromagnetism.SkinDepthApproximation`

Concrete consumers of the good-conductor skin-depth error bounds, at a
good-conductor point, a poor-conductor point, the unit-ratio boundary
and zero conductivity.

## i. Overview

These are elaboration and non-vacuity checks at concrete values, not
new results. At `epsilon = mu = omega = 1` and `sigma = 2` the current
ratio is `1 / 2`, the good-conductor attenuation and skin depth are
both `1`, and the headline bounds pin the exact skin depth to `[1, 2]`.
At `sigma = 1 / 2` the ratio is `2`, so only the lower skin-depth
bound applies. The excluded cases are the opposite root of the squared
equation, the unit ratio, where the upper skin-depth bound has no
premise, and zero conductivity, where the error bound fails.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Good conductor with `epsilon = mu = omega = 1`, `sigma = 2`
- B. Forward and opposite roots at `sigma = 2`
- C. Poor conductor and unit ratio
- D. Zero conductivity
- E. Axiom audit

## iv. References

- `PhyslibExt.Electromagnetism.SkinDepthApproximation`
- `PhyslibExt.Electromagnetism.ConductingPlaneWave`

## A. Good conductor with `epsilon = mu = omega = 1`, `sigma = 2`
-/

@[expose] public section

open PhyslibExt.Electromagnetism.ConductingPlaneWave
open PhyslibExt.Electromagnetism.SkinDepthApproximation

namespace PhyslibExtTest.Electromagnetism.SkinDepthApproximation

/-- The current ratio at `sigma = 2` is `1 / 2`. -/
example : conductionRatio 1 1 2 = 1 / 2 := by
  unfold conductionRatio
  norm_num

/-- The current ratio at `sigma = 2` is positive. -/
example : 0 < conductionRatio 1 1 2 :=
  conductionRatio_pos 1 1 2 (by norm_num) (by norm_num) (by norm_num)

/-- The good-conductor attenuation at `sigma = 2` is `1`. -/
example : goodConductorAttenuation 1 1 2 = 1 := by
  unfold goodConductorAttenuation
  norm_num

/-- The good-conductor attenuation at `sigma = 2` is positive. -/
example : 0 < goodConductorAttenuation 1 1 2 :=
  goodConductorAttenuation_pos 1 1 2 (by norm_num) (by norm_num) (by norm_num)

/-- The good-conductor skin depth at `sigma = 2` is `sqrt (2 / 2) = 1`. -/
example : goodConductorSkinDepth 1 1 2 = 1 := by
  rw [goodConductorSkinDepth_eq_sqrt 1 1 2 (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- The normalized exact attenuation at `rho = 1 / 2`. -/
example : attenuationConstant 1 1 1 2 / goodConductorAttenuation 1 1 2 =
    Real.sqrt (Real.sqrt (5 / 4) - 1 / 2) := by
  have hr : conductionRatio 1 1 2 = 1 / 2 := by
    unfold conductionRatio
    norm_num
  rw [attenuationConstant_div_goodConductorAttenuation 1 1 1 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num), hr]
  norm_num

/-- The headline at `rho = 1 / 2`: the relative error lies in
`[0, 1 / 2]` and the exact skin depth lies in `[1, 2]`. -/
example : 0 ≤ relativeAttenuationError 1 1 1 2 ∧
    relativeAttenuationError 1 1 1 2 ≤ 1 / 2 ∧
    1 ≤ skinDepth 1 1 1 2 ∧ skinDepth 1 1 1 2 ≤ 2 := by
  have hr : conductionRatio 1 1 2 = 1 / 2 := by
    unfold conductionRatio
    norm_num
  have hd : goodConductorSkinDepth 1 1 2 = 1 := by
    rw [goodConductorSkinDepth_eq_sqrt 1 1 2 (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  obtain ⟨h0, h1, h2, -⟩ := skinDepthApproximation_error 1 1 1 2 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  rw [hr] at h1 h2
  obtain ⟨h3, h4⟩ := h2 (by norm_num) (by norm_num)
  rw [hd] at h3 h4
  have h5 : (1 : ℝ) / (1 - 1 / 2) = 2 := by norm_num
  rw [h5] at h4
  exact ⟨h0, h1, h3, h4⟩

/-- The error bound at `rho = 1 / 2` is strict. -/
example : relativeAttenuationError 1 1 1 2 < 1 / 2 := by
  have hr : conductionRatio 1 1 2 = 1 / 2 := by
    unfold conductionRatio
    norm_num
  have h := relativeAttenuationError_lt_conductionRatio 1 1 1 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  rwa [hr] at h

/-! ## B. Forward and opposite roots at `sigma = 2` -/

/-- The forward root at `sigma = 2` has real part equal to the
attenuation constant. -/
example : (propagationConstant 1 1 1 2).re = attenuationConstant 1 1 1 2 := by
  have hβ := phaseConstant_pos 1 1 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have him : 0 < (propagationConstant 1 1 1 2).im := by
    simpa [propagationConstant] using hβ
  exact forwardRoot_re_eq_attenuationConstant 1 1 1 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) _
    (propagationConstant_sq 1 1 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    him

/-- The root-generic bounds at `sigma = 2` for the forward root. -/
example : 0 ≤ 1 - (propagationConstant 1 1 1 2).re / goodConductorAttenuation 1 1 2 ∧
    1 - (propagationConstant 1 1 1 2).re / goodConductorAttenuation 1 1 2 ≤ 1 / 2 := by
  have hr : conductionRatio 1 1 2 = 1 / 2 := by
    unfold conductionRatio
    norm_num
  have hβ := phaseConstant_pos 1 1 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have him : 0 < (propagationConstant 1 1 1 2).im := by
    simpa [propagationConstant] using hβ
  obtain ⟨h0, h1, -⟩ := forwardRoot_skinDepthApproximation_error 1 1 1 2 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) _
    (propagationConstant_sq 1 1 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    him
  rw [hr] at h1
  exact ⟨h0, h1⟩

/-- Excluded case: the opposite root solves the same squared equation
but has negative imaginary part and real part different from the
attenuation constant, so the positive-imaginary-part guard is needed. -/
example : satisfiesDispersionEquation 1 1 1 2 (-propagationConstant 1 1 1 2) ∧
    (-propagationConstant 1 1 1 2).im < 0 ∧
    (-propagationConstant 1 1 1 2).re ≠ attenuationConstant 1 1 1 2 := by
  have hsq :=
    propagationConstant_sq 1 1 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hα := attenuationConstant_pos_of_sigma_pos 1 1 1 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨-, him⟩ := neg_propagationConstant_not_forward 1 1 1 2 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, him, ?_⟩
  · unfold satisfiesDispersionEquation at hsq ⊢
    rw [neg_sq]
    exact hsq
  · have hre : (-propagationConstant 1 1 1 2).re = -attenuationConstant 1 1 1 2 := by
      simp [propagationConstant]
    rw [hre]
    intro h
    linarith

/-! ## C. Poor conductor and unit ratio -/

/-- At `sigma = 1 / 2` the ratio is `2`; the error bound and the lower
skin-depth bound still hold. -/
example : conductionRatio 1 1 (1 / 2) = 2 ∧
    relativeAttenuationError 1 1 1 (1 / 2) ≤ 2 ∧
    goodConductorSkinDepth 1 1 (1 / 2) ≤ skinDepth 1 1 1 (1 / 2) := by
  have hr : conductionRatio 1 1 (1 / 2) = 2 := by
    unfold conductionRatio
    norm_num
  have h := relativeAttenuationError_le_conductionRatio 1 1 1 (1 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  rw [hr] at h
  exact ⟨hr, h, goodConductorSkinDepth_le_skinDepth 1 1 1 (1 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)⟩

/-- Excluded case: at `sigma = omega * epsilon = 1` the ratio is `1`,
so the upper skin-depth bound has no premise, and the exact ratio is
`sqrt (sqrt 2 - 1)`, not the good-conductor value `1`. -/
example : ¬ conductionRatio 1 1 1 < 1 ∧
    attenuationConstant 1 1 1 1 / goodConductorAttenuation 1 1 1 =
      Real.sqrt (Real.sqrt 2 - 1) := by
  have hr : conductionRatio 1 1 1 = 1 := by
    unfold conductionRatio
    norm_num
  have h := attenuation_ratio_at_unit_conductionRatio 1 1 1 (by norm_num) (by norm_num)
    (by norm_num)
  rw [mul_one] at h
  exact ⟨by rw [hr]; exact lt_irrefl 1, h⟩

/-! ## D. Zero conductivity -/

/-- Excluded case: at `sigma = 0` there is no finite skin depth. -/
example : attenuationConstant 1 1 1 0 * skinDepth 1 1 1 0 ≠ 1 :=
  attenuationConstant_mul_skinDepth_zero_sigma 1 1 1 (by norm_num) (by norm_num) (by norm_num)

/-- Excluded case: at `sigma = 0` the ratio is `0` and the relative
error is `1`. -/
example : conductionRatio 1 1 0 = 0 ∧ relativeAttenuationError 1 1 1 0 = 1 := by
  have h0 := attenuationConstant_zero_sigma 1 1 1 (by norm_num) (by norm_num) (by norm_num)
  unfold conductionRatio relativeAttenuationError
  rw [h0]
  norm_num

/-- Excluded case: at `sigma = 0` the error bound fails. -/
example : ¬ relativeAttenuationError 1 1 1 0 ≤ conductionRatio 1 1 0 :=
  not_le.mpr (conductionRatio_lt_relativeAttenuationError_zero_sigma 1 1 1 (by norm_num)
    (by norm_num) (by norm_num))

end PhyslibExtTest.Electromagnetism.SkinDepthApproximation

/-! ## E. Axiom audit -/

open PhyslibExt.Electromagnetism.SkinDepthApproximation

#print axioms conductionRatio_pos
#print axioms goodConductorAttenuation_pos
#print axioms goodConductorSkinDepth_eq_sqrt
#print axioms attenuationConstant_div_goodConductorAttenuation
#print axioms relativeAttenuationError_nonneg
#print axioms relativeAttenuationError_le_conductionRatio
#print axioms relativeAttenuationError_lt_conductionRatio
#print axioms goodConductorSkinDepth_le_skinDepth
#print axioms skinDepth_le_goodConductorSkinDepth_div
#print axioms skinDepthApproximation_error
#print axioms forwardRoot_re_eq_attenuationConstant
#print axioms forwardRoot_skinDepthApproximation_error
#print axioms attenuation_ratio_at_unit_conductionRatio
#print axioms attenuationConstant_mul_skinDepth_zero_sigma
#print axioms conductionRatio_lt_relativeAttenuationError_zero_sigma
