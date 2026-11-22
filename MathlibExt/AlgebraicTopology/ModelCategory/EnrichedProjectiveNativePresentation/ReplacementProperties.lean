/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.Replacement

/-!
# Whole original source replacement maps and bifibrant properties

These are the original transported I/J data at the caller's cardinal and
bottom. The four natural arrows retain their actual unit components, and
their comparison squares use the original native zero and counit.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v uC vC

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra HomotopicalAlgebra.EnrichedProjective
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
variable {C : Type uC} [Category.{vC} C]

attribute [local instance] Native.modelCategory

/-- Retain the original source unit and complete native I first arrow. -/
theorem initialToCofibrantReplacement_original_i
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    (initialToCofibrantReplacement e).app X =
      e.unitIso.hom.app (Zero.object e) ≫ e.inverse.map
        ((Native.cofibrantFactorizationData (B := B) (A := A)).i.app
          (e.functor.mapArrow.obj ((Zero.fromZeroArrow e).obj X))) := rfl

/-- Retain the complete native I second arrow and actual original source unit inverse. -/
theorem cofibrantReplacementCounit_original_p
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    (cofibrantReplacementCounit e).app X =
      e.inverse.map ((Native.cofibrantFactorizationData (B := B) (A := A)).p.app
        (e.functor.mapArrow.obj ((Zero.fromZeroArrow e).obj X))) ≫ e.unitIso.inv.app X := rfl

/-- Retain the original source unit and complete native J first arrow. -/
theorem fibrantReplacementUnit_original_i
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    (fibrantReplacementUnit e).app X = e.unitIso.hom.app X ≫ e.inverse.map
      ((Native.fibrantFactorizationData (B := B) (A := A)).i.app
        (e.functor.mapArrow.obj ((Zero.toZeroArrow e).obj X))) := rfl

/-- Retain the native J second arrow and actual original source unit inverse at zero. -/
theorem fibrantReplacementToZero_original_p
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    (fibrantReplacementToZero e).app X = e.inverse.map
      ((Native.fibrantFactorizationData (B := B) (A := A)).p.app
        (e.functor.mapArrow.obj ((Zero.toZeroArrow e).obj X))) ≫
          e.unitIso.inv.app (Zero.object e) := rfl

/-- The I first-arrow square uses the original whole zero comparison. -/
theorem cofibrantReplacementComparisonIso_i
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    e.functor.map ((initialToCofibrantReplacement e).app X) ≫
      (cofibrantReplacementComparisonIso e).hom.app X =
        (Zero.comparisonIso e).hom ≫
          Native.Replacement.initialToCofibrantReplacement.app (e.functor.obj X) := by
  change e.functor.map ((NativePresentation.cofibrantFactorizationData e).i.app
      ((Zero.fromZeroArrow e).obj X)) ≫
    ((NativePresentation.cofibrantFactorizationDataZComparisonIso e).hom.app
      ((Zero.fromZeroArrow e).obj X) ≫ (Native.cofibrantFactorizationData (A := A)).Z.map
        ((Zero.fromZeroArrowObjIso e X).hom)) = _
  rw [← Category.assoc, NativePresentation.cofibrantFactorizationData_mapped_i]
  exact ((Native.cofibrantFactorizationData (A := A)).i.naturality
    (Zero.fromZeroArrowObjIso e X).hom).symm

/-- The J second-arrow square retains the same original zero comparison. -/
theorem fibrantReplacementComparisonIso_p
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    (fibrantReplacementComparisonIso e).hom.app X ≫
      Native.Replacement.fibrantReplacementToZero.app (e.functor.obj X) =
        e.functor.map ((fibrantReplacementToZero e).app X) ≫ (Zero.comparisonIso e).hom := by
  change ((NativePresentation.fibrantFactorizationDataZComparisonIso e).hom.app
      ((Zero.toZeroArrow e).obj X) ≫ (Native.fibrantFactorizationData (A := A)).Z.map
        ((Zero.toZeroArrowObjIso e X).hom)) ≫
      (Native.fibrantFactorizationData (A := A)).p.app
        (Native.Diagrams.toZeroArrow.obj (e.functor.obj X)) = _
  rw [Category.assoc]
  have h := (Native.fibrantFactorizationData (A := A)).p.naturality
    (Zero.toZeroArrowObjIso e X).hom
  rw [h, ← Category.assoc, NativePresentation.fibrantFactorizationData_mapped_p]
  rfl

theorem initialToCofibrantReplacement_naturality
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) {X Y : C} (f : X ⟶ Y) :
    (initialToCofibrantReplacement e).app Y =
      (initialToCofibrantReplacement e).app X ≫ (cofibrantReplacement e).map f := by
  exact (Category.id_comp _).symm.trans ((initialToCofibrantReplacement e).naturality f)

theorem fibrantReplacementToZero_naturality
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) {X Y : C} (f : X ⟶ Y) :
    (fibrantReplacement e).map f ≫ (fibrantReplacementToZero e).app Y =
      (fibrantReplacementToZero e).app X :=
  ((fibrantReplacementToZero e).naturality f).trans (Category.comp_id _)

theorem initialToCofibrantReplacement_mem_cofibrations
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    letI : ModelCategory C := NativePresentation.modelCategory e
    cofibrations C ((initialToCofibrantReplacement e).app X) :=
  (cofibrantReplacement_classes e X).1

theorem cofibrantReplacementCounit_mem_trivialFibrations
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    letI : ModelCategory C := NativePresentation.modelCategory e
    trivialFibrations C ((cofibrantReplacementCounit e).app X) :=
  (cofibrantReplacement_classes e X).2

theorem cofibrantReplacementCounit_mem_fibrations
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    letI : ModelCategory C := NativePresentation.modelCategory e
    fibrations C ((cofibrantReplacementCounit e).app X) :=
  (cofibrantReplacement_classes e X).2.1

theorem cofibrantReplacementCounit_mem_weakEquivalences
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    NativePresentation.weakProperty e ((cofibrantReplacementCounit e).app X) :=
  (cofibrantReplacement_classes e X).2.2

theorem fibrantReplacementUnit_mem_trivialCofibrations
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    letI : ModelCategory C := NativePresentation.modelCategory e
    trivialCofibrations C ((fibrantReplacementUnit e).app X) :=
  (fibrantReplacement_classes e X).1

theorem fibrantReplacementUnit_mem_cofibrations
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    letI : ModelCategory C := NativePresentation.modelCategory e
    cofibrations C ((fibrantReplacementUnit e).app X) :=
  (fibrantReplacement_classes e X).1.1

theorem fibrantReplacementUnit_mem_weakEquivalences
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    NativePresentation.weakProperty e ((fibrantReplacementUnit e).app X) :=
  (fibrantReplacement_classes e X).1.2

theorem fibrantReplacementToZero_mem_fibrations
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    letI : ModelCategory C := NativePresentation.modelCategory e
    fibrations C ((fibrantReplacementToZero e).app X) :=
  (fibrantReplacement_classes e X).2

theorem cofibrantReplacement_map_mem_weakEquivalences
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) {X Y : C} (f : X ⟶ Y)
    (hf : NativePresentation.weakProperty e f) :
    NativePresentation.weakProperty e ((cofibrantReplacement e).map f) := by
  let _ : ModelCategory C := NativePresentation.modelCategory e
  change weakEquivalences C ((cofibrantReplacement e).map f)
  change weakEquivalences C f at hf
  have hpX : weakEquivalences C ((cofibrantReplacementCounit e).app X) :=
    cofibrantReplacementCounit_mem_weakEquivalences e X
  have hpY : weakEquivalences C ((cofibrantReplacementCounit e).app Y) :=
    cofibrantReplacementCounit_mem_weakEquivalences e Y
  apply (weakEquivalences C).of_postcomp
    ((cofibrantReplacement e).map f) ((cofibrantReplacementCounit e).app Y)
    hpY
  rw [cofibrantReplacementCounit_naturality]
  exact (weakEquivalences C).comp_mem _ _
    (cofibrantReplacementCounit_mem_weakEquivalences e X) hf

theorem fibrantReplacement_map_mem_weakEquivalences
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) {X Y : C} (f : X ⟶ Y)
    (hf : NativePresentation.weakProperty e f) :
    NativePresentation.weakProperty e ((fibrantReplacement e).map f) := by
  let _ : ModelCategory C := NativePresentation.modelCategory e
  change weakEquivalences C ((fibrantReplacement e).map f)
  change weakEquivalences C f at hf
  have hiX : weakEquivalences C ((fibrantReplacementUnit e).app X) :=
    fibrantReplacementUnit_mem_weakEquivalences e X
  have hiY : weakEquivalences C ((fibrantReplacementUnit e).app Y) :=
    fibrantReplacementUnit_mem_weakEquivalences e Y
  apply (weakEquivalences C).of_precomp
    ((fibrantReplacementUnit e).app X) ((fibrantReplacement e).map f)
    hiX
  rw [← fibrantReplacementUnit_naturality]
  exact (weakEquivalences C).comp_mem _ _ hf
    (fibrantReplacementUnit_mem_weakEquivalences e Y)

theorem cofibrantReplacement_map_weakEquivalence_iff
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) {X Y : C} (f : X ⟶ Y) :
    NativePresentation.weakProperty e ((cofibrantReplacement e).map f) ↔
      NativePresentation.weakProperty e f := by
  let _ : ModelCategory C := NativePresentation.modelCategory e
  change weakEquivalences C ((cofibrantReplacement e).map f) ↔ weakEquivalences C f
  constructor
  · intro hf
    have hpX : weakEquivalences C ((cofibrantReplacementCounit e).app X) :=
      cofibrantReplacementCounit_mem_weakEquivalences e X
    apply (weakEquivalences C).of_precomp ((cofibrantReplacementCounit e).app X) f hpX
    rw [← cofibrantReplacementCounit_naturality]
    exact (weakEquivalences C).comp_mem _ _ hf
      (cofibrantReplacementCounit_mem_weakEquivalences e Y)
  · exact cofibrantReplacement_map_mem_weakEquivalences e f

theorem fibrantReplacement_map_weakEquivalence_iff
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) {X Y : C} (f : X ⟶ Y) :
    NativePresentation.weakProperty e ((fibrantReplacement e).map f) ↔
      NativePresentation.weakProperty e f := by
  let _ : ModelCategory C := NativePresentation.modelCategory e
  change weakEquivalences C ((fibrantReplacement e).map f) ↔ weakEquivalences C f
  constructor
  · intro hf
    have hiY : weakEquivalences C ((fibrantReplacementUnit e).app Y) :=
      fibrantReplacementUnit_mem_weakEquivalences e Y
    apply (weakEquivalences C).of_postcomp f ((fibrantReplacementUnit e).app Y) hiY
    rw [fibrantReplacementUnit_naturality]
    exact (weakEquivalences C).comp_mem _ _
      (fibrantReplacementUnit_mem_weakEquivalences e X) hf
  · exact fibrantReplacement_map_mem_weakEquivalences e f

/-- The original fibrant replacement unit after the chosen source cofibrant replacement. -/
def cofibrantToCofibrantFibrantReplacement
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    cofibrantReplacement e ⟶ cofibrantFibrantReplacement e :=
  Functor.whiskerLeft (cofibrantReplacement e) (fibrantReplacementUnit e)

/-- The original cofibrant replacement projection after the chosen source fibrant replacement. -/
def fibrantCofibrantReplacementToFibrant
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    fibrantCofibrantReplacement e ⟶ fibrantReplacement e :=
  Functor.whiskerLeft (fibrantReplacement e) (cofibrantReplacementCounit e)

theorem cofibrantToCofibrantFibrantReplacement_naturality
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) {X Y : C} (f : X ⟶ Y) :
    (cofibrantReplacement e).map f ≫ (cofibrantToCofibrantFibrantReplacement e).app Y =
      (cofibrantToCofibrantFibrantReplacement e).app X ≫ (cofibrantFibrantReplacement e).map f :=
  (cofibrantToCofibrantFibrantReplacement e).naturality f

theorem fibrantCofibrantReplacementToFibrant_naturality
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) {X Y : C} (f : X ⟶ Y) :
    (fibrantCofibrantReplacement e).map f ≫ (fibrantCofibrantReplacementToFibrant e).app Y =
      (fibrantCofibrantReplacementToFibrant e).app X ≫ (fibrantReplacement e).map f :=
  (fibrantCofibrantReplacementToFibrant e).naturality f

theorem cofibrantToCofibrantFibrantReplacement_mem_trivialCofibrations
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    letI : ModelCategory C := NativePresentation.modelCategory e
    trivialCofibrations C ((cofibrantToCofibrantFibrantReplacement e).app X) :=
  fibrantReplacementUnit_mem_trivialCofibrations e ((cofibrantReplacement e).obj X)

theorem fibrantCofibrantReplacementToFibrant_mem_trivialFibrations
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    letI : ModelCategory C := NativePresentation.modelCategory e
    trivialFibrations C ((fibrantCofibrantReplacementToFibrant e).app X) :=
  cofibrantReplacementCounit_mem_trivialFibrations e ((fibrantReplacement e).obj X)

theorem isCofibrant_cofibrantFibrantReplacement
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    letI : ModelCategory C := NativePresentation.modelCategory e
    IsCofibrant ((cofibrantFibrantReplacement e).obj X) := by
  let _ : ModelCategory C := NativePresentation.modelCategory e
  change IsCofibrant ((fibrantReplacement e).obj ((cofibrantReplacement e).obj X))
  rw [isCofibrant_iff_of_isInitial
    ((initialToCofibrantReplacement e).app X ≫
      (fibrantReplacementUnit e).app ((cofibrantReplacement e).obj X)) (Zero.isInitial e)]
  exact (cofibration_iff _).2 ((cofibrations C).comp_mem _ _
    (initialToCofibrantReplacement_mem_cofibrations e X)
    (fibrantReplacementUnit_mem_cofibrations e ((cofibrantReplacement e).obj X)))

theorem isFibrant_cofibrantFibrantReplacement
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    letI : ModelCategory C := NativePresentation.modelCategory e
    IsFibrant ((cofibrantFibrantReplacement e).obj X) :=
  isFibrant_fibrantReplacement e ((cofibrantReplacement e).obj X)

theorem isCofibrant_fibrantCofibrantReplacement
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    letI : ModelCategory C := NativePresentation.modelCategory e
    IsCofibrant ((fibrantCofibrantReplacement e).obj X) :=
  isCofibrant_cofibrantReplacement e ((fibrantReplacement e).obj X)

theorem isFibrant_fibrantCofibrantReplacement
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    letI : ModelCategory C := NativePresentation.modelCategory e
    IsFibrant ((fibrantCofibrantReplacement e).obj X) := by
  let _ : ModelCategory C := NativePresentation.modelCategory e
  change IsFibrant ((cofibrantReplacement e).obj ((fibrantReplacement e).obj X))
  rw [isFibrant_iff_of_isTerminal
    ((cofibrantReplacementCounit e).app ((fibrantReplacement e).obj X) ≫
      (fibrantReplacementToZero e).app X) (Zero.isTerminal e)]
  exact (fibration_iff _).2 ((fibrations C).comp_mem _ _
    (cofibrantReplacementCounit_mem_fibrations e ((fibrantReplacement e).obj X))
    (fibrantReplacementToZero_mem_fibrations e X))

theorem cofibrantFibrantReplacement_map_weakEquivalence_iff
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) {X Y : C} (f : X ⟶ Y) :
    NativePresentation.weakProperty e ((cofibrantFibrantReplacement e).map f) ↔
      NativePresentation.weakProperty e f :=
  (fibrantReplacement_map_weakEquivalence_iff e ((cofibrantReplacement e).map f)).trans
    (cofibrantReplacement_map_weakEquivalence_iff e f)

theorem fibrantCofibrantReplacement_map_weakEquivalence_iff
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) {X Y : C} (f : X ⟶ Y) :
    NativePresentation.weakProperty e ((fibrantCofibrantReplacement e).map f) ↔
      NativePresentation.weakProperty e f :=
  (cofibrantReplacement_map_weakEquivalence_iff e ((fibrantReplacement e).map f)).trans
    (fibrantReplacement_map_weakEquivalence_iff e f)

/-- Both original full native Arrow maps remain in the source RQ map. -/
theorem cofibrantFibrantReplacement_original_map
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) {X Y : C} (f : X ⟶ Y) :
    (cofibrantFibrantReplacement e).map f = e.inverse.map
      ((Native.fibrantFactorizationData (B := B) (A := A)).Z.map
        (e.functor.mapArrow.map ((Zero.toZeroArrow e).map (e.inverse.map
          ((Native.cofibrantFactorizationData (B := B) (A := A)).Z.map
            (e.functor.mapArrow.map ((Zero.fromZeroArrow e).map f))))))) := rfl

/-- Both original full native Arrow maps remain in the reverse source QR map. -/
theorem fibrantCofibrantReplacement_original_map
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) {X Y : C} (f : X ⟶ Y) :
    (fibrantCofibrantReplacement e).map f = e.inverse.map
      ((Native.cofibrantFactorizationData (B := B) (A := A)).Z.map
        (e.functor.mapArrow.map ((Zero.fromZeroArrow e).map (e.inverse.map
          ((Native.fibrantFactorizationData (B := B) (A := A)).Z.map
            (e.functor.mapArrow.map ((Zero.toZeroArrow e).map f))))))) := rfl

end HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement
