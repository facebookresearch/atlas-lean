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
# Realizing right-derived maps through resolution cohomology

Canonical injective-resolution comparisons identify derived objects
with cohomology of mapped resolutions. A derived precomposition map
can therefore be expressed on any supplied resolution and any chosen
presentation of its target. Changes of resolution or presentation
commute with the same map. General isomorphism transport formulas
record the associated commuting and naturality squares.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false


section

open CategoryTheory

namespace CategoryTheory

/-- In a category `C`, suppose `a : X → Y` and `b : A → B`
commute with isomorphisms `c : X ≅ A`, `d : Y ≅ B`.
For further isomorphisms `i : X ≅ I`, `j : Y ≅ J`, transporting `a`
to `I → J` gives the commuting square with the induced isomorphisms
`I ≅ A` and `J ≅ B`. -/
theorem resolution_realization_square {C : Type*} [Category C]
    {X Y I J A B : C} (i : X ≅ I) (j : Y ≅ J) (a : X ⟶ Y)
    (c : X ≅ A) (d : Y ≅ B) (b : A ⟶ B) (h : a ≫ d.hom = c.hom ≫ b) :
    (i.inv ≫ a ≫ j.hom) ≫ (j.symm ≪≫ d).hom = (i.symm ≪≫ c).hom ≫ b := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  exact congrArg (fun t => i.inv ≫ t) h

/-- In a category `C`, let `a : X → Y` and choose presentations
`X ≅ I`, `X ≅ I′`, `Y ≅ J`, `Y ≅ J′`. The maps obtained by
transporting `a` to `I → J` and `I′ → J′` commute with the canonical
changes between these presentations. -/
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

/-- Let `C,D,A` be abelian, with injective resolutions in `C,D`,
`F : C → D` additive and preserving injectives and homology,
`B : D → A`, `P : C → A` additive, and `α : P ≅ F ⋙ B`. For an injective resolution `I` of `X` and a presentation
`N ≅ R^qB(F(X))`, realizing the derived precomposition map on
`H^q(P(I)) → N` equals the cohomology comparison with `B(F(I))`
followed by its inverse presented resolution comparison. -/
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

/-- Let `C,D,A` be abelian, with injective resolutions in `C,D`,
`F : C → D` additive and preserving injectives and homology,
`B : D → A`, `P : C → A` additive, and `α : P ≅ F ⋙ B`. For an injective resolution `I` of `X` and a presentation
`N ≅ R^qB(F(X))`, the complete isomorphism `H^q(P(I)) ≅ N` factors
through the termwise comparison `H^q(P(I)) ≅ H^q(B(F(I)))` and the
inverse resolution comparison for the presented target. -/
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
/-- Let `C,D,A` be categories, `T : C → D`, `P : C → A`,
`F,G : D → A`, and natural isomorphisms `a : P ≅ T ⋙ F`,
`b : G ≅ F`. At `Q : C`, composing `a` with the whiskered inverse
of `b` gives `a_Q ≪≫ b_(T(Q))⁻¹`, also after any presentation
isomorphism `P(Q) ≅ X`. -/
theorem resolution_natIso_app {C D A : Type*} [Category C] [Category D] [Category A]
    {P : C ⥤ A} (T : C ⥤ D) {F G : D ⥤ A} (a : P ≅ T ⋙ F) (b : G ≅ F)
    (Q : C) {X : A} (i : P.obj Q ≅ X) :
    i.symm ≪≫ (a ≪≫ Functor.isoWhiskerLeft T b.symm).app Q =
      i.symm ≪≫ (a.app Q ≪≫ (b.app (T.obj Q)).symm) := by
  rfl

/-- Let `C,D` be abelian, with injective resolutions in `C`,
and `F : C → D` additive. If injective resolutions `I,J` of `X` are equal, the canonical
comparison from any presentation `N ≅ R^qF(X)` to their mapped
cohomology gives the same isomorphism for `I` and `J`. -/
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
/-- Let `C` be a category with zero morphisms and chosen homology
objects, `K` a nonnegative cochain complex, and `q ∈ ℕ`.
Evaluating the degree-`q` homology functor at `K` gives the chosen
homology object `H^q(K)`. -/
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

/-- Let `C,D` be abelian, with injective resolutions in `C`,
and `F : C → D` additive. For an injective resolution `I` of `X` and a presentation
`c : N ≅ R^qF(X)`, composing `c` with the resolution comparison
gives `N ≅ H^q(F(I))`. -/
def actualHomologyResolutionIso (q : ℕ) {X : C} (I : InjectiveResolution X)
    {N : D} (c : N ≅ (F.rightDerived q).obj X) :
    N ≅ (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homology q) :=
  c ≪≫ I.isoRightDerivedObj F q

/-- Let `C,D` be abelian, with injective resolutions in `C`,
and `F : C → D` additive. Equality of injective resolutions `I=J` of `X` identifies
the actual cohomology object `H^q(F(I))` with the evaluation of the
homology functor on `F(J)`. -/
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
/-- Let `C,D` be abelian, with injective resolutions in `C`,
and `F : C → D` additive. For equal resolutions `I=J` and `c : N ≅ R^qF(X)`, the
comparison to actual `H^q(F(I))` followed by the equality-induced
presentation isomorphism is `c` followed by the resolution comparison
for `J`. -/
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
/-- In a category `C`, let maps `a : X → Y`, `a′ : X′ → Y′`
commute with `f : X → X′`, `g : Y → Y′`. Suppose presentations
`i : X ≅ I`, `i′ : X′ ≅ I′`, `j : Y ≅ J`, `j′ : Y′ ≅ J′`
intertwine `f,g` with `φ : I → I′`, `ψ : J → J′`.
Then the transported maps `I → J`, `I′ → J′` commute with `φ,ψ`. -/
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
