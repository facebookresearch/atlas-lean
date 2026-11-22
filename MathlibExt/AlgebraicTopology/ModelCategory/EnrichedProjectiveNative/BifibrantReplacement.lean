/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.Replacement

/-!
# Bifibrant composites of the literal original native replacements

Both orders use the same original I and J middle functors. Their weak
comparison zigzags, full maps and level homotopy comparisons are derived
from those actual natural arrows.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra HomotopicalAlgebra.EnrichedProjective
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native.Replacement

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]

attribute [local instance] Native.modelCategory

/-- Apply the original free-I replacement and then the original free-J replacement. -/
def cofibrantFibrantReplacement : EnrichedFunctorCat PointedCGWH.{u, v} A ⥤
    EnrichedFunctorCat PointedCGWH.{u, v} A :=
  cofibrantReplacement ⋙ fibrantReplacement

/-- Apply the same original free-J replacement and then the same original free-I replacement. -/
def fibrantCofibrantReplacement : EnrichedFunctorCat PointedCGWH.{u, v} A ⥤
    EnrichedFunctorCat PointedCGWH.{u, v} A :=
  fibrantReplacement ⋙ cofibrantReplacement

/-- The actual original J first arrow after Q, giving the right side of the RQ zigzag. -/
def cofibrantToCofibrantFibrantReplacement :
    cofibrantReplacement (A := A) ⟶ cofibrantFibrantReplacement (A := A) :=
  Functor.whiskerLeft cofibrantReplacement fibrantReplacementUnit

/-- The actual original I second arrow after R, giving the left side of the QR zigzag. -/
def fibrantCofibrantReplacementToFibrant :
    fibrantCofibrantReplacement (A := A) ⟶ fibrantReplacement (A := A) :=
  Functor.whiskerLeft fibrantReplacement cofibrantReplacementCounit

theorem cofibrantToCofibrantFibrantReplacement_app
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    cofibrantToCofibrantFibrantReplacement.app X =
      fibrantReplacementUnit.app (cofibrantReplacement.obj X) := rfl

theorem fibrantCofibrantReplacementToFibrant_app
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    fibrantCofibrantReplacementToFibrant.app X =
      cofibrantReplacementCounit.app (fibrantReplacement.obj X) := rfl

theorem cofibrantToCofibrantFibrantReplacement_naturality
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    cofibrantReplacement.map f ≫ cofibrantToCofibrantFibrantReplacement.app Y =
      cofibrantToCofibrantFibrantReplacement.app X ≫ cofibrantFibrantReplacement.map f :=
  cofibrantToCofibrantFibrantReplacement.naturality f

theorem fibrantCofibrantReplacementToFibrant_naturality
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    fibrantCofibrantReplacement.map f ≫ fibrantCofibrantReplacementToFibrant.app Y =
      fibrantCofibrantReplacementToFibrant.app X ≫ fibrantReplacement.map f :=
  fibrantCofibrantReplacementToFibrant.naturality f

/-- The right side of the RQ zigzag is the original actual trivial cofibration. -/
theorem cofibrantToCofibrantFibrantReplacement_mem_trivialCofibrations
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)
      (cofibrantToCofibrantFibrantReplacement.app X) :=
  fibrantReplacementUnit_mem_trivialCofibrations (cofibrantReplacement.obj X)

/-- The left side of the QR zigzag is the original actual trivial fibration. -/
theorem fibrantCofibrantReplacementToFibrant_mem_trivialFibrations
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)
      (fibrantCofibrantReplacementToFibrant.app X) :=
  cofibrantReplacementCounit_mem_trivialFibrations (fibrantReplacement.obj X)

theorem isCofibrant_cofibrantFibrantReplacement
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    IsCofibrant (cofibrantFibrantReplacement.obj X) := by
  change IsCofibrant (fibrantReplacement.obj (cofibrantReplacement.obj X))
  rw [isCofibrant_iff_of_isInitial
    (initialToCofibrantReplacement.app X ≫
      fibrantReplacementUnit.app (cofibrantReplacement.obj X))
    Diagrams.zeroDiagramIsInitial]
  exact (cofibration_iff _).2
    ((cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)).comp_mem _ _
      (initialToCofibrantReplacement_mem_cofibrations X)
      (fibrantReplacementUnit_mem_cofibrations (cofibrantReplacement.obj X)))

theorem isFibrant_cofibrantFibrantReplacement
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    IsFibrant (cofibrantFibrantReplacement.obj X) :=
  isFibrant_fibrantReplacement (cofibrantReplacement.obj X)

theorem isCofibrant_fibrantCofibrantReplacement
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    IsCofibrant (fibrantCofibrantReplacement.obj X) :=
  isCofibrant_cofibrantReplacement (fibrantReplacement.obj X)

theorem isFibrant_fibrantCofibrantReplacement
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    IsFibrant (fibrantCofibrantReplacement.obj X) := by
  change IsFibrant (cofibrantReplacement.obj (fibrantReplacement.obj X))
  rw [isFibrant_iff_of_isTerminal
    (cofibrantReplacementCounit.app (fibrantReplacement.obj X) ≫
      fibrantReplacementToZero.app X)
    Diagrams.zeroDiagramIsTerminal]
  exact (fibration_iff _).2
    ((fibrations (EnrichedFunctorCat PointedCGWH.{u, v} A)).comp_mem _ _
      (cofibrantReplacementCounit_mem_fibrations (fibrantReplacement.obj X))
      (fibrantReplacementToZero_mem_fibrations X))

theorem cofibrantFibrantReplacement_map_mem_weakEquivalences
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (hf : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A) f) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A)
      (cofibrantFibrantReplacement.map f) :=
  fibrantReplacement_map_mem_weakEquivalences _
    (cofibrantReplacement_map_mem_weakEquivalences f hf)

theorem fibrantCofibrantReplacement_map_mem_weakEquivalences
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y)
    (hf : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A) f) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} A)
      (fibrantCofibrantReplacement.map f) :=
  cofibrantReplacement_map_mem_weakEquivalences _
    (fibrantReplacement_map_mem_weakEquivalences f hf)

/-- Every RQ map retains both complete original Arrow maps and middle functors. -/
theorem cofibrantFibrantReplacement_map_eq_original_data
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    cofibrantFibrantReplacement.map f =
      (Native.fibrantFactorizationData (B := B) (A := A)).Z.map
        (Diagrams.toZeroArrow.map
          ((Native.cofibrantFactorizationData (B := B) (A := A)).Z.map
            (Diagrams.fromZeroArrow.map f))) := rfl

/-- Every QR map retains those same two full original Arrow maps in the other order. -/
theorem fibrantCofibrantReplacement_map_eq_original_data
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    fibrantCofibrantReplacement.map f =
      (Native.cofibrantFactorizationData (B := B) (A := A)).Z.map
        (Diagrams.fromZeroArrow.map
          ((Native.fibrantFactorizationData (B := B) (A := A)).Z.map
            (Diagrams.toZeroArrow.map f))) := rfl

/-- Natural RQ compatibility with the actual original level projection. -/
def cofibrantFibrantReplacementProjectionIso :
    cofibrantFibrantReplacement (A := A) ⋙
      toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) ≅
    toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
  Functor.isoWhiskerLeft cofibrantReplacement fibrantReplacementProjectionIso.symm ≪≫
    cofibrantReplacementProjectionIso

/-- Natural QR compatibility with that same level projection. -/
def fibrantCofibrantReplacementProjectionIso :
    fibrantCofibrantReplacement (A := A) ⋙
      toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) ≅
    toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
  Functor.isoWhiskerLeft fibrantReplacement cofibrantReplacementProjectionIso ≪≫
    fibrantReplacementProjectionIso.symm

/-- The RQ projection uses the original Q second arrow and the inverse of the original R first
arrow. -/
theorem cofibrantFibrantReplacementProjectionIso_hom_app
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    cofibrantFibrantReplacementProjectionIso.hom.app X =
      fibrantReplacementProjectionIso.inv.app (cofibrantReplacement.obj X) ≫
        (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
          (cofibrantReplacementCounit.app X) := rfl

/-- The QR projection uses the original Q second arrow after R and the inverse of the original R
first arrow. -/
theorem fibrantCofibrantReplacementProjectionIso_hom_app
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    fibrantCofibrantReplacementProjectionIso.hom.app X =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A)).map
        (cofibrantReplacementCounit.app (fibrantReplacement.obj X)) ≫
          fibrantReplacementProjectionIso.inv.app X := rfl

end HomotopicalAlgebra.EnrichedProjective.Native.Replacement
