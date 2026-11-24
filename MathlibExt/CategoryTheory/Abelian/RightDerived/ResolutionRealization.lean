/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Authors: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Abelian.RightDerived.Precomposition
public import MathlibExt.CategoryTheory.Abelian.DeltaFunctor.Transport
public import MathlibExt.CategoryTheory.Abelian.RightDerived.DeltaComparison

/-!
# Canonical realization of right-derived maps on original resolutions
-/

@[expose] public section

noncomputable section

set_option autoImplicit false


section

open CategoryTheory

namespace CategoryTheory

/-- Realize a proved map square through the source/target resolution isomorphisms. -/
theorem resolution_realization_square {C : Type*} [Category C]
    {X Y I J A B : C} (i : X ≅ I) (j : Y ≅ J) (a : X ⟶ Y)
    (c : X ≅ A) (d : Y ≅ B) (b : A ⟶ B) (h : a ≫ d.hom = c.hom ≫ b) :
    (i.inv ≫ a ≫ j.hom) ≫ (j.symm ≪≫ d).hom = (i.symm ≪≫ c).hom ≫ b := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  exact congrArg (fun t => i.inv ≫ t) h

/-- Canonical source and target changes of resolution commute with the same realized map. -/
theorem resolution_realization_choice {C : Type*} [Category C]
    {X Y I I' J J' : C} (i : X ≅ I) (i' : X ≅ I') (j : Y ≅ J) (j' : Y ≅ J')
    (a : X ⟶ Y) :
    (i.symm ≪≫ i').hom ≫ (i'.inv ≫ a ≫ j'.hom) =
      (i.inv ≫ a ≫ j.hom) ≫ (j.symm ≪≫ j').hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]

end CategoryTheory

end


section

universe uC vC uD vD uA vA
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor
variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type uD} [Category.{vD} D] [Abelian D] [HasInjectiveResolutions D]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (F : C ⥤ D) [F.Additive] [F.PreservesInjectiveObjects] [F.PreservesHomology]
variable (B : D ⥤ A) [B.Additive]
variable {P : C ⥤ A} [P.Additive]

/-- The SAME fixed precomposition family, realized in an arbitrary mapped resolution. -/
theorem precomp_native_resolution_formula (α : P ≅ F ⋙ B) (q : ℕ)
    {X : C} (I : InjectiveResolution X) {N : A}
    (c : N ≅ (B.rightDerived q).obj (F.obj X)) :
    ((I.isoRightDerivedObj P q).symm ≪≫
      ((rightDerivedPrecompIsoOfIso F B α q).app X ≪≫ c.symm)).hom =
    (rightDerivedPrecompHomologyIsoOfIso F B α q I).hom ≫
      (c ≪≫ (F.mapInjectiveResolution I).isoRightDerivedObj B q).inv := by
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv]
  have h := rightDerivedPrecompIsoOfIso_resolution_iso F B α q I
  change ((rightDerivedPrecompIsoOfIso F B α q).app X).hom =
    (I.isoRightDerivedObj P q).hom ≫
      (rightDerivedPrecompHomologyIsoOfIso F B α q I).hom ≫
        ((F.mapInjectiveResolution I).isoRightDerivedObj B q).inv at h
  have h' := congrArg (fun a => (I.isoRightDerivedObj P q).inv ≫ a ≫ c.inv) h
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h'


end CategoryTheory.Functor

end


section

universe uC vC uD vD uA vA
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor
variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type uD} [Category.{vD} D] [Abelian D] [HasInjectiveResolutions D]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (F : C ⥤ D) [F.Additive] [F.PreservesInjectiveObjects] [F.PreservesHomology]
variable (B : D ⥤ A) [B.Additive]
variable {P : C ⥤ A} [P.Additive]

/-- Complete iso formulation of the SAME mapped-resolution formula. -/
theorem precomp_native_resolution_iso (α : P ≅ F ⋙ B) (q : ℕ)
    {X : C} (I : InjectiveResolution X) {N : A}
    (c : N ≅ (B.rightDerived q).obj (F.obj X)) :
    (I.isoRightDerivedObj P q).symm ≪≫
      ((rightDerivedPrecompIsoOfIso F B α q).app X ≪≫ c.symm) =
    rightDerivedPrecompHomologyIsoOfIso F B α q I ≪≫
      (c ≪≫ (F.mapInjectiveResolution I).isoRightDerivedObj B q).symm := by
  apply Iso.ext
  exact precomp_native_resolution_formula F B α q I c

end CategoryTheory.Functor

end


section

open CategoryTheory CategoryTheory.Limits
universe uC vC uD vD uA vA

namespace CategoryTheory
/-- Evaluate the same natural-iso composition and whisker before instantiating field functors. -/
theorem resolution_natIso_app {C D A : Type*} [Category C] [Category D] [Category A]
    {P : C ⥤ A} (T : C ⥤ D) {F G : D ⥤ A} (a : P ≅ T ⋙ F) (b : G ≅ F)
    (Q : C) {X : A} (i : P.obj Q ≅ X) :
    i.symm ≪≫ (a ≪≫ Functor.isoWhiskerLeft T b.symm).app Q =
      i.symm ≪≫ (a.app Q ≪≫ (b.app (T.obj Q)).symm) := by
  rfl

/-- The equality of two named resolutions transports the same canonical RD isomorphism. -/
theorem resolution_native_eq
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasInjectiveResolutions C]
    {D : Type uD} [Category.{vD} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (q : ℕ) {X : C}
    (I J : InjectiveResolution X) (h : I = J) {N : D}
    (b : N ≅ (F.rightDerived q).obj X) :
    HEq (b ≪≫ I.isoRightDerivedObj F q) (b ≪≫ J.isoRightDerivedObj F q) := by
  cases h
  rfl
end CategoryTheory

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory
/-- The homology functor's object is the homology object with its fixed category choice. -/
theorem homology_object_presentation {C : Type*} [Category C] [HasZeroMorphisms C]
    [CategoryWithHomology C]
    (K : CochainComplex C ℕ) (q : ℕ) :
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) q).obj K = K.homology q := rfl
end CategoryTheory

end


section

universe uC vC uD vD
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.InjectiveResolution
variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type uD} [Category.{vD} D] [Abelian D]
variable (F : C ⥤ D) [F.Additive]

/-- The resolution comparison keeps its literal homology codomain. -/
def actualHomologyResolutionIso (q : ℕ) {X : C} (I : InjectiveResolution X)
    {N : D} (c : N ≅ (F.rightDerived q).obj X) :
    N ≅ (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homology q) :=
  c ≪≫ I.isoRightDerivedObj F q

/-- Canonical presentation transport is computed solely from homology and resolution equality. -/
def homologyResolutionPresentationIso (q : ℕ) {X : C}
    (I J : InjectiveResolution X) (h : I = J) :
    (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homology q) ≅
      (HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) q).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex) :=
  eqToIso (homology_object_presentation
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) q).symm ≪≫
    eqToIso (congrArg (fun R : InjectiveResolution X =>
      (HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) q).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex)) h)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- V4 homologyFunctor.obj versus homology object was not visible under implicit transparency.
/-- The canonical presentation transports the SAME comparison, never an arbitrary supplied iso. -/
theorem actualHomologyResolutionIso_presentation (q : ℕ) {X : C}
    (I J : InjectiveResolution X) (h : I = J) {N : D}
    (c : N ≅ (F.rightDerived q).obj X) :
    actualHomologyResolutionIso F q I c ≪≫ homologyResolutionPresentationIso F q I J h =
      c ≪≫ J.isoRightDerivedObj F q := by
  cases h
  have hp : homologyResolutionPresentationIso F q I I rfl = Iso.refl _ := by
    apply Iso.ext
    simp only [homologyResolutionPresentationIso, Iso.trans_hom, eqToIso.hom]
    change eqToHom (show (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homology q) =
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homology q) from rfl) ≫
      eqToHom (show (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homology q) =
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homology q) from rfl) = 𝟙 _
    simp only [eqToHom_refl, Category.id_comp]
  rw [hp]
  apply Iso.ext
  change (c.hom ≫ (I.isoRightDerivedObj F q).hom) ≫ 𝟙 _ =
    c.hom ≫ (I.isoRightDerivedObj F q).hom
  exact Category.comp_id _

end CategoryTheory.InjectiveResolution

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory
/-- The original augmentation-map squares transport naturality to the realized maps. -/
theorem resolution_realization_naturality {C : Type*} [Category C]
    {X X' Y Y' I I' J J' : C}
    (i : X ≅ I) (i' : X' ≅ I') (j : Y ≅ J) (j' : Y' ≅ J')
    (f : X ⟶ X') (g : Y ⟶ Y') (φ : I ⟶ I') (ψ : J ⟶ J')
    (a : X ⟶ Y) (a' : X' ⟶ Y')
    (hi : f ≫ i'.hom = i.hom ≫ φ)
    (hj : g ≫ j'.hom = j.hom ≫ ψ) (ha : f ≫ a' = a ≫ g) :
    φ ≫ (i'.inv ≫ a' ≫ j'.hom) = (i.inv ≫ a ≫ j.hom) ≫ ψ := by
  have hφ : φ ≫ i'.inv = i.inv ≫ f := CohomologicalDeltaFunctor.isoInvSquare i i' f φ hi
  have hψ : g ≫ j'.hom = j.hom ≫ ψ := hj
  calc
    _ = (i.inv ≫ f) ≫ a' ≫ j'.hom := by rw [← Category.assoc, hφ]
    _ = i.inv ≫ a ≫ g ≫ j'.hom := by
      simpa only [Category.assoc] using congrArg (fun z => i.inv ≫ z ≫ j'.hom) ha
    _ = _ := by rw [hψ]; simp only [Category.assoc]
end CategoryTheory

end
