/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryNonmixedMapsRight
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryNonmixedSum

/-!
# Cancellation of positive inserted-right Shih boundary terms

The concrete simplex-word comparison is combined with the generic additive
bridge, both pointwise and after summing over all positive right insertions.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Simplicial
open scoped MonoidalCategory

universe v u

namespace AlgebraicTopology.EilenbergZilber

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

/-- A positive inserted-right active face cancels its lower-boundary partner. -/
theorem shihRightBoundaryTerm_add_lower_eq_zero
    (X Y : SimplicialObject C) (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (b : Fin (q + 2)) (hb : 0 < b.val) :
    shihUpperBoundaryTerm X Y (p + q + m + 1)
        (ShihIndex.rightBoundaryUpperIndex p q m hm t b)
        (ShihIndex.rightBoundaryUpperFace p q m t b) +
      shihLowerBoundaryTerm X Y (p + q + m)
        (ShihIndex.rightBoundaryLowerFace p q m b hb)
        (ShihIndex.ofGap p q m hm t) = 0 :=
  shihRightBoundaryTerm_add_lower_eq_zero_of_maps X Y p q m hm t b hb
    (ShihIndex.map_rightBoundaryUpper_leftHom_comp_delta X p q m hm t b hb)
    (ShihIndex.map_rightBoundaryUpper_rightHom_comp_delta Y p q m hm t b hb)

/-- For fixed lower Shih data, all positive inserted-right active faces cancel
the corresponding lower-boundary terms. -/
theorem shihRightBoundaryPositive_sum_eq_zero
    (X Y : SimplicialObject C) (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) :
    (∑ b : {b : Fin (q + 2) // 0 < b.val},
        shihUpperBoundaryTerm X Y (p + q + m + 1)
          (ShihIndex.rightBoundaryUpperIndex p q m hm t b)
          (ShihIndex.rightBoundaryUpperFace p q m t b)) +
      ∑ b : {b : Fin (q + 2) // 0 < b.val},
        shihLowerBoundaryTerm X Y (p + q + m)
          (ShihIndex.rightBoundaryLowerFace p q m b b.2)
          (ShihIndex.ofGap p q m hm t) = 0 :=
  shihRightBoundaryPositive_sum_eq_zero_of_maps X Y p q m hm t
    (fun b => ShihIndex.map_rightBoundaryUpper_leftHom_comp_delta
      X p q m hm t b b.2)
    (fun b => ShihIndex.map_rightBoundaryUpper_rightHom_comp_delta
      Y p q m hm t b b.2)

end AlgebraicTopology.EilenbergZilber
