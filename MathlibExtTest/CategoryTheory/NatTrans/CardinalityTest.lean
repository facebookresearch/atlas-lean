/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.NatTrans.Cardinality

public section
set_option autoImplicit false

noncomputable section

universe u v w r

open CategoryTheory Cardinal

namespace CategoryTheory.ElementsCardinalityTest

/-- The bound uses actual natural maps; their original point action keeps d and a. -/
theorem original_point_action {D : Type w} [Category.{v} D]
    {A X : Dᵒᵖ ⥤ Type u} (f : A ⟶ X) (d : Dᵒᵖ) (a : A.obj d) :
    f.mapElements.obj (A.elementsMk d a) = X.elementsMk d (f.app d a) := rfl

/-- The same original-map inequality survives a genuine larger cardinal universe. -/
theorem lifted_original_maps {D : Type w} [Category.{v} D]
    (A X : Dᵒᵖ ⥤ Type u) :
    Cardinal.lift.{r} (Cardinal.mk (A ⟶ X)) ≤
      Cardinal.lift.{r} (Cardinal.mk X.Elements) ^
        Cardinal.lift.{r} (Cardinal.mk A.Elements) := by
  simpa only [Cardinal.lift_power] using
    (Cardinal.lift_le.2 (mk_hom_le_elements_power A X))

/-- A fixed domain profile ξ gives a varying Hom bound γ=2^ξ, not ξ. -/
theorem fixed_profile {D : Type w} [Category.{v} D]
    (A X : Dᵒᵖ ⥤ Type u) (ξ : Cardinal.{max u w}) (hξ : ℵ₀ ≤ ξ)
    (hA : Cardinal.mk A.Elements ≤ ξ) (hX : Cardinal.mk X.Elements ≤ 2 ^ ξ) :
    Cardinal.mk (A ⟶ X) ≤ 2 ^ ξ := by
  have hγ : (2 : Cardinal.{max u w}) ^ ξ ≠ 0 :=
    ne_of_gt ((show 0 ≤ ξ from zero_le).trans_lt (Cardinal.cantor ξ))
  calc
    _ ≤ Cardinal.mk X.Elements ^ Cardinal.mk A.Elements := mk_hom_le_elements_power A X
    _ ≤ (2 ^ ξ) ^ Cardinal.mk A.Elements := Cardinal.power_le_power_right hX
    _ ≤ (2 ^ ξ) ^ ξ := Cardinal.power_le_power_left hγ hA
    _ = 2 ^ ξ := by rw [← Cardinal.power_mul, Cardinal.mul_eq_self hξ]

/-- Every original map from an empty total-point presheaf is the same map. -/
theorem empty_source_maps {D : Type w} [Category.{v} D]
    (A X : Dᵒᵖ ⥤ Type u) [IsEmpty A.Elements] :
    Cardinal.mk (A ⟶ X) ≤ 1 := by
  simpa only [Cardinal.mk_eq_zero A.Elements, Cardinal.power_zero] using
    mk_hom_le_elements_power A X

/-- A nonempty original source admits no natural map to an empty target. -/
theorem empty_target_maps {D : Type w} [Category.{v} D]
    (A X : Dᵒᵖ ⥤ Type u) [Nonempty A.Elements] [IsEmpty X.Elements] :
    Cardinal.mk (A ⟶ X) = 0 := by
  have hA : Cardinal.mk A.Elements ≠ 0 := Cardinal.mk_ne_zero_iff.2 inferInstance
  have h := mk_hom_le_elements_power A X
  simpa only [Cardinal.mk_eq_zero X.Elements, Cardinal.zero_power hA, le_zero_iff] using h

end CategoryTheory.ElementsCardinalityTest
