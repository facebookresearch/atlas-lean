/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.BorderedRealSpaceModels

/-!
# The two-point compactified real line as a bordered space

Its ambient space, and that of its square, is Hausdorff, locally compact and σ-compact; addition and
negation act on the finite real coordinates.
-/

namespace MathlibExtTest.AlgebraicGeometry.BorderedRealSpaceModels

open MathlibExt.AlgebraicGeometry.BorderedRealSpaceModels

example : infiniteReal.HasLocallyCompactAmbient := inferInstance

example : (product infiniteReal infiniteReal).HasLocallyCompactAmbient := inferInstance

/-- The finite point `x` of the extended line. -/
noncomputable def finitePoint (x : ℝ) : infiniteReal.interior := realHomeomorph x

/-- Addition is real addition on the finite coordinates: `1 + 2 = 3`. -/
example : realAddition ⟨((finitePoint 1).val, (finitePoint 2).val),
    (finitePoint 1).property, (finitePoint 2).property⟩ = finitePoint 3 := by
  change realHomeomorph
    (realHomeomorph.symm (finitePoint 1) + realHomeomorph.symm (finitePoint 2)) = realHomeomorph 3
  simp only [finitePoint, Homeomorph.symm_apply_apply]
  norm_num

/-- Negation is real negation on the finite coordinates. -/
example (x : ℝ) : realNegation (finitePoint x) = finitePoint (-x) := by
  change realHomeomorph (-realHomeomorph.symm (finitePoint x)) = realHomeomorph (-x)
  simp only [finitePoint, Homeomorph.symm_apply_apply]

end MathlibExtTest.AlgebraicGeometry.BorderedRealSpaceModels
