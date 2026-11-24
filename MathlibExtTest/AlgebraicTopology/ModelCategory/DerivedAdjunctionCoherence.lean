/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedAdjunctionCoherence

/-! # Complete chosen derived Hom and compositor-mate clients -/

public section
noncomputable section
universe u₁ u₂ u₃ v₁ v₂ v₃
open CategoryTheory Functor HomotopicalAlgebra
open HomotopicalAlgebra.DerivedFunctorCoherence
open HomotopicalAlgebra.DerivedAdjunctionCoherence

namespace DerivedAdjunctionFullClients

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
  {E : Type u₃} [Category.{v₃} E] [ModelCategory E]
  {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) [a.IsQuillenAdjunction]
  {M : D ⥤ E} {S : E ⥤ D} (b : M ⊣ S) [b.IsQuillenAdjunction]
  (q : GeneratedFunctorialReplacements.Data (C := C))
  (r : GeneratedFunctorialReplacements.Data (C := D))
  (s : GeneratedFunctorialReplacements.Data (C := E))

/-- The source Quillen pair constructs the entire actual chosen derived adjunction. -/
def actualDerivedAdjunction : left a q ⊣ right a r := chosenAdjunction a q r

/-- Every original source-unit map is kept with both original replacement comparisons. -/
theorem actualUnitMap (X : C) :
    (chosenAdjunction a q r).unit.app ((projection C).obj X) ≫ (right a r).map ((leftComparison a q).app X) =
      (projection C).map (a.unit.app X) ≫ (rightComparison a r).app (L.obj X) := unit_fac a q r X

/-- Every original counit and both chosen replacement maps are retained. -/
theorem actualCounitMap (Y : D) :
    (left a q).map ((rightComparison a r).app Y) ≫ (chosenAdjunction a q r).counit.app ((projection D).obj Y) =
      (leftComparison a q).app (R.obj Y) ≫ (projection D).map (a.counit.app Y) := counit_fac a q r Y

/-- The chosen derived forward map uses its actual unit and original right functor. -/
theorem fullForwardHom (X : (weakEquivalences C).Localization) (Y : (weakEquivalences D).Localization)
    (f : (left a q).obj X ⟶ Y) :
    homEquiv a q r X Y f = (chosenAdjunction a q r).unit.app X ≫ (right a r).map f :=
  (chosenAdjunction a q r).homEquiv_unit X Y f

/-- The chosen derived inverse map uses its actual counit and original left functor. -/
theorem fullInverseHom (X : (weakEquivalences C).Localization) (Y : (weakEquivalences D).Localization)
    (g : X ⟶ (right a r).obj Y) :
    (homEquiv a q r X Y).symm g = (left a q).map g ≫ (chosenAdjunction a q r).counit.app Y :=
  (chosenAdjunction a q r).homEquiv_counit X Y g

/-- Both inverse functions act on all original Hom maps of the localized categories. -/
theorem fullHomBothInverse (X : (weakEquivalences C).Localization) (Y : (weakEquivalences D).Localization)
    (f : (left a q).obj X ⟶ Y) (g : X ⟶ (right a r).obj Y) :
    (homEquiv a q r X Y).symm (homEquiv a q r X Y f) = f ∧
      homEquiv a q r X Y ((homEquiv a q r X Y).symm g) = g :=
  ⟨((chosenAdjunction a q r).homEquiv X Y).symm_apply_apply f,
    ((chosenAdjunction a q r).homEquiv X Y).apply_symm_apply g⟩

/-- The full forward map is natural under arbitrary source localization maps. -/
theorem everySourceHoMap {X X' : (weakEquivalences C).Localization}
    (Y : (weakEquivalences D).Localization) (u : X' ⟶ X) (f : (left a q).obj X ⟶ Y) :
    homEquiv a q r X' Y ((left a q).map u ≫ f) = u ≫ homEquiv a q r X Y f :=
  (chosenAdjunction a q r).homEquiv_naturality_left u f

/-- Arbitrary target Ho maps retain the actual full derived right map. -/
theorem everyTargetHoMap (X : (weakEquivalences C).Localization) {Y Y' : (weakEquivalences D).Localization}
    (f : (left a q).obj X ⟶ Y) (v : Y ⟶ Y') :
    homEquiv a q r X Y' (f ≫ v) = homEquiv a q r X Y f ≫ (right a r).map v :=
  (chosenAdjunction a q r).homEquiv_naturality_right f v

/-- The forward function preserves the two actual weak replacements and original ordinary-Ho adjunct. -/
theorem originalForwardHom (X : C) (Y : D) (f : (left a q).obj ((projection C).obj X) ⟶ (projection D).obj Y) :
    (projection C).map (q.q.app X) ≫ homEquiv a q r ((projection C).obj X) ((projection D).obj Y) f =
      originalHomEquiv a q r X Y (f ≫ (projection D).map (r.r.app Y)) := homEquiv_original a q r X Y f

/-- The full inverse function keeps the same original q, r and inverse ordinary adjunction functions. -/
theorem originalInverseHom (X : C) (Y : D) (g : (projection C).obj X ⟶ (right a r).obj ((projection D).obj Y)) :
    (homEquiv a q r ((projection C).obj X) ((projection D).obj Y)).symm g ≫ (projection D).map (r.r.app Y) =
      (originalHomEquiv a q r X Y).symm ((projection C).map (q.q.app X) ≫ g) :=
  homEquiv_original_symm a q r X Y g

/-- The entire original left derived triangle is an equality of complete natural transformations. -/
theorem fullLeftTriangle : whiskerRight (chosenAdjunction a q r).unit (left a q) ≫
      (Functor.associator (left a q) (right a r) (left a q)).hom ≫
        whiskerLeft (left a q) (chosenAdjunction a q r).counit =
    (Functor.leftUnitor (left a q)).hom ≫ (Functor.rightUnitor (left a q)).inv :=
  (chosenAdjunction a q r).left_triangle

/-- The entire right derived triangle retains every original comparison leg. -/
theorem fullRightTriangle : whiskerLeft (right a r) (chosenAdjunction a q r).unit ≫
      (Functor.associator (right a r) (left a q) (right a r)).inv ≫
        whiskerRight (chosenAdjunction a q r).counit (right a r) =
    (Functor.rightUnitor (right a r)).hom ≫ (Functor.leftUnitor (right a r)).inv :=
  (chosenAdjunction a q r).right_triangle

/-- The original composition comparisons preserve the full derived unit. -/
theorem fullUnitMate : ((chosenAdjunction a q r).comp (chosenAdjunction b r s)).unit ≫
      whiskerRight (leftCompositionIso a b q r).hom (right b s ⋙ right a r) =
    (chosenAdjunction (a.comp b) q s).unit ≫ whiskerLeft (left (a.comp b) q) (rightCompositionIso a b r s).hom :=
  composition_unit_mate a q r b s

/-- All compositor maps preserve the complete derived counit on the same actual localized category. -/
theorem fullCounitMate : whiskerRight (rightCompositionIso a b r s).hom (left a q ⋙ left b r) ≫
      ((chosenAdjunction a q r).comp (chosenAdjunction b r s)).counit =
    whiskerLeft (right (a.comp b) s) (leftCompositionIso a b q r).hom ≫ (chosenAdjunction (a.comp b) q s).counit :=
  composition_counit_mate a q r b s

/-- Composition coherence commutes with both full original Hom functions on arbitrary localizations. -/
theorem fullHomMate (X : (weakEquivalences C).Localization) (Y : (weakEquivalences E).Localization)
    (f : (left (a.comp b) q).obj X ⟶ Y) :
    (((chosenAdjunction a q r).comp (chosenAdjunction b r s)).homEquiv X Y)
        ((leftCompositionIso a b q r).hom.app X ≫ f) =
      homEquiv (a.comp b) q s X Y f ≫ (rightCompositionIso a b r s).hom.app Y :=
  composition_hom_mate a q r b s X Y f

end DerivedAdjunctionFullClients
