/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Calculus.ConservativeCurveIntegral

@[expose] public section

open MetaMathlibExt
open scoped Gradient RealInnerProductSpace

namespace MathlibExtTest.Analysis.Calculus.ConservativeCurveIntegral

/-- The affine field on the non-axis-aligned segment integrates to `-1`. -/
example : (∫ᶜ _ in Path.segment (!₂[0, 0] : EuclideanSpace ℝ (Fin 2)) !₂[1, 2],
    innerSL ℝ (-(!₂[3, -1] : EuclideanSpace ℝ (Fin 2)))) = -1 :=
  (curveIntegral_affineField_segment 5).1

/-- The reversed affine segment integrates to `+1`. -/
example : (∫ᶜ _ in (Path.segment (!₂[0, 0] : EuclideanSpace ℝ (Fin 2)) !₂[1, 2]).symm,
    innerSL ℝ (-(!₂[3, -1] : EuclideanSpace ℝ (Fin 2)))) = 1 :=
  curveIntegral_affineField_segment_symm

/-- The rotational field has loop integral `1` around the triangle. -/
example : ∫ᶜ x in triangleLoop, innerSL ℝ (rotationalField x) = 1 :=
  curveIntegral_rotationalField_triangleLoop

/-- No C1 potential has the rotational field as its negative gradient near the loop. -/
example : ¬ ∃ (φ : EuclideanSpace ℝ (Fin 2) → ℝ) (U : Set (EuclideanSpace ℝ (Fin 2))),
    IsOpen U ∧ Set.range triangleLoop ⊆ U ∧ ContDiffOn ℝ 1 φ U ∧
      ∀ x ∈ U, rotationalField x = -∇ φ x :=
  not_exists_potential_rotationalField

end MathlibExtTest.Analysis.Calculus.ConservativeCurveIntegral
