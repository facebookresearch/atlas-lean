/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryNonmixedMapsLeft
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryNonmixedSum

/-!
# Cancellation of interior inserted-left Shih boundary terms

The concrete simplex-word comparisons are combined with the generic additive
bridge, both pointwise and after summing over all interior left insertions.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Simplicial
open scoped MonoidalCategory

universe v u

namespace AlgebraicTopology.EilenbergZilber

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

/-- An interior inserted-left active face cancels its lower-boundary partner. -/
theorem shihLeftBoundaryTerm_add_lower_eq_zero
    (X Y : SimplicialObject C) (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) (a : Fin (p + 3))
    (ha0 : 0 < a.val) (haLast : a.val < p + 2) :
    shihUpperBoundaryTerm X Y (p + q + m + 1)
        (ShihIndex.leftBoundaryUpperIndex p q m hm t a)
        (ShihIndex.leftBoundaryUpperFace p q m t a) +
      shihLowerBoundaryTerm X Y (p + q + m)
        (ShihIndex.leftBoundaryLowerFace p q m hm a ha0)
        (ShihIndex.ofGap p q m hm t) = 0 :=
  shihLeftBoundaryTerm_add_lower_eq_zero_of_maps X Y p q m hm t a
    ha0 haLast
    (ShihIndex.map_leftBoundaryUpper_leftHom_comp_delta
      X p q m hm t a ha0)
    (ShihIndex.map_leftBoundaryUpper_rightHom_comp_delta
      Y p q m hm t a ha0 haLast)

/-- For fixed lower Shih data, all interior inserted-left active faces cancel
the corresponding lower-boundary terms. -/
theorem shihLeftBoundaryInterior_sum_eq_zero
    (X Y : SimplicialObject C) (p q m : ℕ) (hm : 0 < m)
    (t : Shuffle (p + 1) q) :
    (∑ a : {a : Fin (p + 3) // 0 < a.val ∧ a.val < p + 2},
        shihUpperBoundaryTerm X Y (p + q + m + 1)
          (ShihIndex.leftBoundaryUpperIndex p q m hm t a)
          (ShihIndex.leftBoundaryUpperFace p q m t a)) +
      ∑ a : {a : Fin (p + 3) // 0 < a.val ∧ a.val < p + 2},
        shihLowerBoundaryTerm X Y (p + q + m)
          (ShihIndex.leftBoundaryLowerFace p q m hm a a.2.1)
          (ShihIndex.ofGap p q m hm t) = 0 :=
  shihLeftBoundaryInterior_sum_eq_zero_of_maps X Y p q m hm t
    (fun a => ShihIndex.map_leftBoundaryUpper_leftHom_comp_delta
      X p q m hm t a a.2.1)
    (fun a => ShihIndex.map_leftBoundaryUpper_rightHom_comp_delta
      Y p q m hm t a a.2.1 a.2.2)

end AlgebraicTopology.EilenbergZilber
