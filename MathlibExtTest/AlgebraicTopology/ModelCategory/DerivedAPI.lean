/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.DerivedAdjunctionCoherence
import MathlibExt.AlgebraicTopology.ModelCategory.DerivedFunctorNaturalIso
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalenceTotalDerived

/-!
# Integration checks for the public derived-functor API

These checks combine natural-isomorphism lifting, localization, and adjunction
transposition. They retain arbitrary localization objects and arbitrary source
arrows; replacement choices are supplied as complete records.
-/

noncomputable section

universe uC uD vC vD

open CategoryTheory
open HomotopicalAlgebra
open HomotopicalAlgebra.DerivedFunctorCoherence

namespace AtlasModelCategoryDerivedAPI

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D] [ModelCategory D]
  {L L' L'' : C ⥤ D} {R R' R'' : D ⥤ C}
  (adj : L ⊣ R) [adj.IsQuillenAdjunction]
  (adj' : L' ⊣ R') [adj'.IsQuillenAdjunction]
  (adj'' : L'' ⊣ R'') [adj''.IsQuillenAdjunction]
  (q : GeneratedFunctorialReplacements.Data (C := C))
  (r : GeneratedFunctorialReplacements.Data (C := D))

-- An identity source isomorphism acts trivially on every localized object.
example (X : (weakEquivalences C).Localization) :
    (leftNatIso adj adj q (Iso.refl L)).hom.app X = 𝟙 ((left adj q).obj X) := by
  rw [leftNatIso_hom, Iso.refl_hom, leftNat_id]
  rfl

example (Y : (weakEquivalences D).Localization) :
    (rightNatIso adj adj r (Iso.refl R)).inv.app Y = 𝟙 ((right adj r).obj Y) := by
  rw [rightNatIso_inv, Iso.refl_inv, rightNat_id]
  rfl

-- Lifting two source isomorphisms and composing their whole transformations
-- agrees with lifting their composite, beyond represented components alone.
example (e : L ≅ L') (e' : L' ≅ L'') :
    (leftNatIso adj adj' q e).hom ≫ (leftNatIso adj' adj'' q e').hom =
      (leftNatIso adj adj'' q (e.trans e')).hom := by
  rw [leftNatIso_hom, leftNatIso_hom, leftNatIso_hom, leftNat_comp]
  simp only [Iso.trans_hom]

example (e : R ≅ R') (e' : R' ≅ R'') :
    (rightNatIso adj adj' r e).hom ≫ (rightNatIso adj' adj'' r e').hom =
      (rightNatIso adj adj'' r (e.trans e')).hom := by
  rw [rightNatIso_hom, rightNatIso_hom, rightNatIso_hom, rightNat_comp]
  simp only [Iso.trans_hom]

-- The lifted inverse really is an inverse at an arbitrary localization object.
example (e : L ≅ L') (X : (weakEquivalences C).Localization) :
    (leftNat adj adj' q e.hom).app X ≫ (leftNat adj' adj q e.inv).app X =
      𝟙 ((left adj q).obj X) := by
  have h := congr_app (leftNat_comp adj adj' adj q e.hom e.inv) X
  simpa only [Iso.hom_inv_id, leftNat_id, NatTrans.comp_app, NatTrans.id_app] using h

-- Derived transposition respects postcomposition by an original target arrow.
-- The final map explicitly uses the supplied fibrant replacement functor.
example (X : (weakEquivalences C).Localization) {Y Z : D}
    (f : (left adj q).obj X ⟶ (projection D).obj Y) (g : Y ⟶ Z) :
    DerivedAdjunctionCoherence.homEquiv adj q r X ((projection D).obj Z)
        (f ≫ (projection D).map g) =
      DerivedAdjunctionCoherence.homEquiv adj q r X ((projection D).obj Y) f ≫
        (projection C).map (R.map (r.R.map g)) := by
  change (DerivedAdjunctionCoherence.chosenAdjunction adj q r).homEquiv X
      ((projection D).obj Z) (f ≫ (projection D).map g) =
    (DerivedAdjunctionCoherence.chosenAdjunction adj q r).homEquiv X
      ((projection D).obj Y) f ≫ (projection C).map (R.map (r.R.map g))
  calc
    _ = (DerivedAdjunctionCoherence.chosenAdjunction adj q r).homEquiv X
        ((projection D).obj Y) f ≫ (right adj r).map ((projection D).map g) :=
      (DerivedAdjunctionCoherence.chosenAdjunction adj q r).homEquiv_naturality_right
        f ((projection D).map g)
    _ = _ := congrArg
      (fun k : (right adj r).obj ((projection D).obj Y) ⟶
          (right adj r).obj ((projection D).obj Z) =>
        (DerivedAdjunctionCoherence.chosenAdjunction adj q r).homEquiv X
          ((projection D).obj Y) f ≫ k)
      (right_map adj r g)

-- The original adjunct, comparison maps, and derived naturality form one square.
example (X : C) {Y Z : D} (f : L.obj X ⟶ Y) (g : Y ⟶ Z) :
    DerivedAdjunctionCoherence.homEquiv adj q r ((projection C).obj X)
        ((projection D).obj Z)
        ((leftComparison adj q).app X ≫ (projection D).map (f ≫ g)) =
      (projection C).map (adj.homEquiv X Y f) ≫ (rightComparison adj r).app Y ≫
        (projection C).map (R.map (r.R.map g)) := by
  rw [Functor.map_comp, ← Category.assoc]
  rw [(DerivedAdjunctionCoherence.chosenAdjunction adj q r).homEquiv_naturality_right]
  rw [DerivedAdjunctionCoherence.homEquiv_source_map, right_map]
  exact Category.assoc _ _ _

-- The inverse square includes every source arrow and the complete original
-- inverse adjunct, rather than a chosen image object or a fixed test arrow.
example {X' X : C} (f : X' ⟶ X) (Y : D) (g : X ⟶ R.obj Y) :
    (DerivedAdjunctionCoherence.homEquiv adj q r ((projection C).obj X')
        ((projection D).obj Y)).symm
        ((projection C).map (f ≫ g) ≫ (rightComparison adj r).app Y) =
      (leftComparison adj q).app X' ≫
        (projection D).map (L.map f ≫ (adj.homEquiv X Y).symm g) := by
  rw [DerivedAdjunctionCoherence.homEquiv_source_map_symm,
    adj.homEquiv_naturality_left_symm]

section CanonicalTotalEquivalence

variable [adj.IsQuillenEquivalence]

-- Both canonical total-derived unit and counit are invertible on the entire
-- localization, including objects not presented by an explicitly chosen Q/R.
omit [adj.IsQuillenAdjunction] in
example : IsIso (quillenDerivedAdjunctionData adj).adjunction.unit :=
  quillenEquivalenceDerived_unit_isIso adj

omit [adj.IsQuillenAdjunction] in
example : IsIso (quillenDerivedAdjunctionData adj).adjunction.counit :=
  quillenEquivalenceDerived_counit_isIso adj

-- Equivalence transposition keeps the actual canonical total-derived adjunct
-- while composing with an arbitrary target-localization arrow.
omit [adj.IsQuillenAdjunction] in
example (X : (weakEquivalences C).Localization)
    {Y Z : (weakEquivalences D).Localization}
    (f : (quillenDerivedAdjunctionData adj).leftDerived.obj X ⟶ Y) (g : Y ⟶ Z) :
    (quillenEquivalenceDerivedEquivalence adj).toAdjunction.homEquiv X Z (f ≫ g) =
      (quillenDerivedAdjunctionData adj).adjunction.homEquiv X Y f ≫
        (quillenDerivedAdjunctionData adj).rightDerived.map g := by
  exact (quillenEquivalenceDerivedEquivalence_homEquiv adj X Z (f ≫ g)).trans
    ((quillenDerivedAdjunctionData adj).adjunction.homEquiv_naturality_right f g)

end CanonicalTotalEquivalence

end AtlasModelCategoryDerivedAPI
