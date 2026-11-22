/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.SourceMappingPre
import MathlibExt.CategoryTheory.Equivalence.FunctorFamily
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.NativePreTransport

/-!
# Transport of module internal Hom to orthogonal spectra

A selected enriched Day module source and a supplied carrier equivalence transport the
entire module internal Hom bifunctor. Its object and contravariant map formulas agree
with the selected native closed structure, giving a natural isomorphism of bifunctors.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
noncomputable section
universe uV vV uI vI uD vD
open CategoryTheory MonoidalCategory Limits Opposite
open CategoryTheory.Enriched CategoryTheory.EnrichedFunctorCat
open PointedCGWH.Spectra.Orthogonal
open scoped MonoidalClosed CategoryTheory.MonObj

universe uMapA vMapA uMapB vMapB

private def conjugateEnd {C : Type uMapA} [Category.{vMapA} C]
    {D : Type uMapB} [Category.{vMapB} D] (E : C ≌ D) : (C ⥤ C) ⥤ (D ⥤ D) where
  obj R := E.inverse ⋙ R ⋙ E.functor
  map p := Functor.whiskerLeft E.inverse (Functor.whiskerRight p E.functor)
  map_id R := by ext X; simp
  map_comp p q := by ext X; simp

private theorem conjugateEnd_eq {C : Type uMapA} [Category.{vMapA} C]
    {D : Type uMapB} [Category.{vMapB} D] (E : C ≌ D) :
    conjugateEnd E = ((E.congrLeft (E := C)).trans (E.congrRight (E := D))).functor := rfl

private theorem functorMapHEq {A : Type uMapA} [Category.{vMapA} A]
    {B : Type uMapB} [Category.{vMapB} B] {F G : A ⥤ B} (h : F = G)
    {X Y : A} (f : X ⟶ Y) : HEq (F.map f) (G.map f) := by
  cases h
  exact HEq.refl _

private theorem mapHEq {A : Type uMapA} [Category.{vMapA} A]
    {B : Type uMapB} [Category.{vMapB} B] (F : A ⥤ B) {X X' Y Y' : A}
    (hX : X = X') (hY : Y = Y') (f : X ⟶ Y) (g : X' ⟶ Y') (h : HEq f g) :
    HEq (F.map f) (F.map g) := by
  cases hX
  cases hY
  cases eq_of_heq h
  exact HEq.refl _

private theorem squareOfHEq {A : Type uMapA} [Category.{vMapA} A]
    {X X' Y Y' : A} (hX : X = X') (hY : Y = Y')
    (f : X ⟶ Y) (g : X' ⟶ Y') (h : HEq f g) :
    f ≫ eqToHom hY = eqToHom hX ≫ g := by
  cases hX
  cases hY
  simpa using eq_of_heq h

namespace OrthogonalIGeneratorProbe.SelectedNativeBif

attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
  EnrichedDayKernel.ColimitMonoidal.smallestColimits SphereModuleMappingEnd.moduleCategory
attribute [local irreducible] EnrichedDayKernel.Closed.monoidalClosed

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  [HasProducts.{uI} V] [HasEqualizers V]
  (q : ModuleMappingR.SelectedSource V I)
  {D : Type uD} [Category.{vD} D]

/-- The module internal Hom bifunctor built from the selected source Day and sphere-coefficient
data. -/
def sourceBif : q.Moduleᵒᵖ ⥤ (q.Module ⥤ q.Module) :=
  ModuleMappingR.moduleBifunctor q.monoidalData q.braidedData q.coefficientFunctor
    q.coefficientMonoidal q.coefficientBraided

private def normalizedNativeBif (c : CanonicalSourceSmash.SourceContext q D) : Dᵒᵖ ⥤ (D ⥤ D) :=
  c.equivalence.inverse.op ⋙ sourceBif q ⋙ conjugateEnd c.equivalence

/-- The source module-Hom bifunctor transported to native objects and native endofunctors by the
source equivalence. -/
def nativeBif (c : CanonicalSourceSmash.SourceContext q D) : Dᵒᵖ ⥤ (D ⥤ D) :=
  c.equivalence.inverse.op ⋙ sourceBif q ⋙
    (c.equivalence.congrLeft.trans c.equivalence.congrRight).functor

private theorem normalizedNativeBif_eq (c : CanonicalSourceSmash.SourceContext q D) :
    normalizedNativeBif q c = nativeBif q c :=
  congrArg (fun F => c.equivalence.inverse.op ⋙ sourceBif q ⋙ F)
    (conjugateEnd_eq c.equivalence)

/-- The selected native internal Hom at `X` equals the transported source bifunctor at the same
opposite object. -/
def ObjectEquation (c : CanonicalSourceSmash.SourceContext q D) (X : D) : Prop :=
  letI := c.monoidalCategory
  letI := CanonicalSourceSmashClosed.Selected.monoidalClosed c
  ihom X = (nativeBif q c).obj (op X)

theorem object_eq (c : CanonicalSourceSmash.SourceContext q D) (X : D) :
    ObjectEquation q c X := by
  let := q.moduleMonoidal
  let := q.moduleClosed
  let := c.monoidalCategory
  let := CanonicalSourceSmashClosed.Selected.monoidalClosed c
  unfold ObjectEquation
  have h := CanonicalSourceSmashClosed.Selected.ihom c X
  have h0 : ihom X = (normalizedNativeBif q c).obj (op X) :=
    h.trans (congrArg (fun R => c.equivalence.inverse ⋙ R ⋙ c.equivalence.functor)
      (ModuleMappingR.functor_eq_source q.monoidalData q.braidedData q.coefficientFunctor
        q.coefficientMonoidal q.coefficientBraided (c.equivalence.inverse.obj X)))
  exact h0.trans (CategoryTheory.Functor.congr_obj (normalizedNativeBif_eq q c) (op X))

/-- Native closed precomposition is heterogeneously equal to the transported source bifunctor map. -/
def MapEquation (c : CanonicalSourceSmash.SourceContext q D) {X X' : D} (f : X' ⟶ X) : Prop :=
  letI := c.monoidalCategory
  letI := CanonicalSourceSmashClosed.Selected.monoidalClosed c
  HEq (MonoidalClosed.pre f) ((nativeBif q c).map f.op)

theorem map_heq (c : CanonicalSourceSmash.SourceContext q D) {X X' : D} (f : X' ⟶ X) :
    MapEquation q c f := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let := q.moduleMonoidal
  let := q.moduleClosed
  let := c.monoidalCategory
  let := CanonicalSourceSmashClosed.Selected.monoidalClosed c
  unfold MapEquation
  have hn := Transport.nativePre c.equivalence (fun M : q.Module => ihom M)
    (fun M : q.Module => ihom.adjunction M) f
  have hs := ChosenPre.sourcePre_heq q (c.equivalence.inverse.map f)
  have hA := (q.moduleClosed_ihom (c.equivalence.inverse.obj X)).trans
    (ModuleMappingR.functor_eq_source q.monoidalData q.braidedData q.coefficientFunctor
      q.coefficientMonoidal q.coefficientBraided (c.equivalence.inverse.obj X))
  have hB := (q.moduleClosed_ihom (c.equivalence.inverse.obj X')).trans
    (ModuleMappingR.functor_eq_source q.monoidalData q.braidedData q.coefficientFunctor
      q.coefficientMonoidal q.coefficientBraided (c.equivalence.inverse.obj X'))
  have ht := mapHEq (conjugateEnd c.equivalence) hA hB
    (MonoidalClosed.pre (c.equivalence.inverse.map f))
    (RightModuleMappingEnd.sourceNatTrans q.coefficient (c.equivalence.inverse.map f)) hs
  have h0 : HEq (MonoidalClosed.pre f) ((normalizedNativeBif q c).map f.op) :=
    (heq_of_eq hn).trans ht
  exact h0.trans (functorMapHEq (normalizedNativeBif_eq q c) f.op)

attribute [local irreducible] nativeBif

private theorem whole_eq (c : CanonicalSourceSmash.SourceContext q D) :
    letI := c.monoidalCategory
    letI := CanonicalSourceSmashClosed.Selected.monoidalClosed c
    MonoidalClosed.internalHom = nativeBif q c := by
  let := c.monoidalCategory
  let := CanonicalSourceSmashClosed.Selected.monoidalClosed c
  exact CategoryTheory.Functor.hext
    (F := MonoidalClosed.internalHom) (G := nativeBif q c)
    (fun X => object_eq q c X.unop) (fun _ _ f => map_heq q c f.unop)

/-- The selected native internal Hom bifunctor is naturally isomorphic to the transported source
module-Hom bifunctor. -/
def comparison (c : CanonicalSourceSmash.SourceContext q D) :
    letI := c.monoidalCategory
    letI := CanonicalSourceSmashClosed.Selected.monoidalClosed c
    MonoidalClosed.internalHom ≅ nativeBif q c := by
  let := c.monoidalCategory
  let := CanonicalSourceSmashClosed.Selected.monoidalClosed c
  exact eqToIso (whole_eq q c)







end OrthogonalIGeneratorProbe.SelectedNativeBif
