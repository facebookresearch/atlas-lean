/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenDerivedEquivalence

/-!
# Actual canonical derived unit and counit transport

Solve the original derived-adjunction equations using the same invertible comparison maps.
The formulas retain the canonical derived functors and the actual source adjunction maps.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u₁ u₂ v₁ v₂

open CategoryTheory MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  [CategoryTheory.Adjunction.IsQuillenAdjunction adj]

local notation "WC" => weakEquivalences C
local notation "WD" => weakEquivalences D
local notation "data" => quillenDerivedAdjunctionData adj

/-- The whole canonical unit component is determined by the original source unit and comparisons. -/
theorem quillenDerived_unit_transport
    (hL : WC ≤ (WD).inverseImage L) (X : C) :
    letI : IsIso (data).leftComparison := quillenDerived_leftComparison_isIso adj hL
    (data).adjunction.unit.app ((WC).Q.obj X) =
      ((WC).Q.map (adj.unit.app X) ≫ (data).rightComparison.app (L.obj X)) ≫
        inv ((data).rightDerived.map ((data).leftComparison.app X)) := by
  let _ : IsIso (data).leftComparison := quillenDerived_leftComparison_isIso adj hL
  calc
    (data).adjunction.unit.app ((WC).Q.obj X) =
        ((data).adjunction.unit.app ((WC).Q.obj X) ≫
          (data).rightDerived.map ((data).leftComparison.app X)) ≫
            inv ((data).rightDerived.map ((data).leftComparison.app X)) := by
      simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    _ = _ := by rw [quillenDerived_unit_fac]

/-- The whole canonical counit component keeps the original source counit and both comparisons. -/
theorem quillenDerived_counit_transport
    (hR : WD ≤ (WC).inverseImage R) (Y : D) :
    letI : IsIso (data).rightComparison := quillenDerived_rightComparison_isIso adj hR
    (data).adjunction.counit.app ((WD).Q.obj Y) =
      inv ((data).leftDerived.map ((data).rightComparison.app Y)) ≫
        ((data).leftComparison.app (R.obj Y) ≫ (WD).Q.map (adj.counit.app Y)) := by
  let _ : IsIso (data).rightComparison := quillenDerived_rightComparison_isIso adj hR
  calc
    (data).adjunction.counit.app ((WD).Q.obj Y) =
        inv ((data).leftDerived.map ((data).rightComparison.app Y)) ≫
          ((data).leftDerived.map ((data).rightComparison.app Y) ≫
            (data).adjunction.counit.app ((WD).Q.obj Y)) := by
      simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
    _ = _ := by rw [quillenDerived_counit_fac]

end HomotopicalAlgebra
