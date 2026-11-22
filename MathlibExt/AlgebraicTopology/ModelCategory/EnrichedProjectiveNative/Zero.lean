/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.Zero
public import MathlibExt.Topology.Category.PointedCGWH.Closed
public import MathlibExt.CategoryTheory.Enriched.PointwiseShapeInstances
public import MathlibExt.CategoryTheory.Enriched.ZeroCompletion
public import MathlibExt.CategoryTheory.Limits.Shapes.ZeroObjectArrowFunctors
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Actual initial, terminal and zero diagrams on native enriched carriers

Native pointed zero objects supply the empty base limits and colimits. The
existing enriched pointwise construction supplies the genuine diagrams.
Evaluation preserves those same constructions, and the proved pointwise-zero
characterization supplies the original-carrier zero object.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.Diagrams

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]

/-- The actual native empty colimit gives an initial enriched diagram. -/
theorem nativeHasInitial : HasInitial (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
  inferInstance

/-- The actual native empty limit gives a terminal enriched diagram. -/
theorem nativeHasTerminal : HasTerminal (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
  inferInstance

attribute [local instance] nativeHasInitial nativeHasTerminal

/-- The chosen original-carrier enriched initial diagram. -/
def initialDiagram : EnrichedFunctorCat PointedCGWH.{u, v} A :=
  ⊥_ (EnrichedFunctorCat PointedCGWH.{u, v} A)

/-- The chosen original-carrier enriched terminal diagram. -/
def terminalDiagram : EnrichedFunctorCat PointedCGWH.{u, v} A :=
  ⊤_ (EnrichedFunctorCat PointedCGWH.{u, v} A)

/-- Every actual initial-diagram component is the native pointed zero object. -/
def initialDiagramComponentZeroIso (a : A) :
    (initialDiagram (A := A)).toEnrichedFunctor.obj a ≅ (0 : PointedCGWH.{u, v}) := by
  let h : IsInitial (initialDiagram (A := A)) := initialIsInitial
  let hi : IsInitial ((EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v}) (A := A) a).obj
      (initialDiagram (A := A))) :=
    h.isInitialObj (EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v}) (A := A) a)
      initialDiagram
  exact ((isZero_zero PointedCGWH.{u, v}).isoIsInitial hi).symm

/-- Every actual terminal-diagram component is the native pointed zero object. -/
def terminalDiagramComponentZeroIso (a : A) :
    (terminalDiagram (A := A)).toEnrichedFunctor.obj a ≅ (0 : PointedCGWH.{u, v}) := by
  let h : IsTerminal (terminalDiagram (A := A)) := terminalIsTerminal
  let ht : IsTerminal ((EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v}) (A := A) a).obj
      (terminalDiagram (A := A))) :=
    h.isTerminalObj (EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v}) (A := A) a)
      terminalDiagram
  exact ((isZero_zero PointedCGWH.{u, v}).isoIsTerminal ht).symm

/-- Actual evaluation of the original initial diagram is zero. -/
theorem initialDiagram_component_isZero (a : A) :
    IsZero ((initialDiagram (A := A)).toEnrichedFunctor.obj a) :=
  (isZero_zero PointedCGWH.{u, v}).of_iso (initialDiagramComponentZeroIso a)

/-- Actual evaluation of the original terminal diagram is zero. -/
theorem terminalDiagram_component_isZero (a : A) :
    IsZero ((terminalDiagram (A := A)).toEnrichedFunctor.obj a) :=
  (isZero_zero PointedCGWH.{u, v}).of_iso (terminalDiagramComponentZeroIso a)

/-- The initial enriched diagram is zero by the proved full diagram characterization. -/
theorem initialDiagram_isZero : IsZero (initialDiagram (A := A)) :=
  CategoryTheory.EnrichedZeroCompletion.diagram_isZero_of_obj_isZero
    initialDiagram initialDiagram_component_isZero

/-- The terminal enriched diagram is zero by that same full characterization. -/
theorem terminalDiagram_isZero : IsZero (terminalDiagram (A := A)) :=
  CategoryTheory.EnrichedZeroCompletion.diagram_isZero_of_obj_isZero
    terminalDiagram terminalDiagram_component_isZero

/-- Native functor categories have zero objects without an incoming model dictionary. -/
theorem nativeHasZeroObject : HasZeroObject (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
  (initialDiagram_isZero (A := A)).hasZeroObject

/-- Use the same original initial diagram as the explicit zero diagram. -/
abbrev zeroDiagram : EnrichedFunctorCat PointedCGWH.{u, v} A := initialDiagram

theorem zeroDiagram_isZero : IsZero (zeroDiagram (A := A)) := initialDiagram_isZero

/-- The original bundled initial structure on the explicit zero diagram. -/
def zeroDiagramIsInitial : IsInitial (zeroDiagram (A := A)) :=
  zeroDiagram_isZero.isInitial

/-- The original bundled terminal structure on the explicit zero diagram. -/
def zeroDiagramIsTerminal : IsTerminal (zeroDiagram (A := A)) :=
  zeroDiagram_isZero.isTerminal

/-- The same actual initial and terminal constructions are canonically isomorphic. -/
def initialTerminalIso : initialDiagram (A := A) ≅ terminalDiagram (A := A) :=
  initialDiagram_isZero.iso terminalDiagram_isZero

/-- The unique source map from the explicit original zero diagram. -/
def zeroTo (X : EnrichedFunctorCat PointedCGWH.{u, v} A) : zeroDiagram ⟶ X :=
  zeroDiagram_isZero.to_ X

/-- The unique target map into that same explicit original zero diagram. -/
def toZero (X : EnrichedFunctorCat PointedCGWH.{u, v} A) : X ⟶ zeroDiagram :=
  zeroDiagram_isZero.from_ X

theorem zeroTo_eq_initial_to (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    zeroTo X = initial.to X :=
  zeroDiagramIsInitial.hom_ext _ _

theorem zeroTo_naturality {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    zeroTo X ≫ f = zeroTo Y :=
  zeroDiagram_isZero.eq_of_src _ _

theorem toZero_naturality {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    f ≫ toZero Y = toZero X :=
  zeroDiagram_isZero.eq_of_tgt _ _

/-- The full zero-to-object Arrow functor, retaining both sides of every square. -/
def fromZeroArrow : EnrichedFunctorCat PointedCGWH.{u, v} A ⥤
    Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
  originalInitialArrowFunctor zeroDiagram_isZero

/-- The full object-to-zero Arrow functor on that same explicit original zero. -/
def toZeroArrow : EnrichedFunctorCat PointedCGWH.{u, v} A ⥤
    Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
  originalTerminalArrowFunctor zeroDiagram_isZero

theorem fromZeroArrow_obj (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    fromZeroArrow.obj X = Arrow.mk (zeroTo X) := rfl

theorem toZeroArrow_obj (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    toZeroArrow.obj X = Arrow.mk (toZero X) := rfl

theorem fromZeroArrow_map_left {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    (fromZeroArrow.map f).left = 𝟙 zeroDiagram := rfl

theorem fromZeroArrow_map_right {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    (fromZeroArrow.map f).right = f := rfl

theorem toZeroArrow_map_left {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    (toZeroArrow.map f).left = f := rfl

theorem toZeroArrow_map_right {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    (toZeroArrow.map f).right = 𝟙 zeroDiagram := rfl

theorem fromZeroArrow_leftFunc :
    fromZeroArrow (A := A) ⋙ Arrow.leftFunc =
      (Functor.const (EnrichedFunctorCat PointedCGWH.{u, v} A)).obj zeroDiagram := rfl

theorem fromZeroArrow_rightFunc :
    fromZeroArrow (A := A) ⋙ Arrow.rightFunc = 𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} A) := rfl

theorem toZeroArrow_leftFunc :
    toZeroArrow (A := A) ⋙ Arrow.leftFunc = 𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} A) := rfl

theorem toZeroArrow_rightFunc :
    toZeroArrow (A := A) ⋙ Arrow.rightFunc =
      (Functor.const (EnrichedFunctorCat PointedCGWH.{u, v} A)).obj zeroDiagram := rfl

end HomotopicalAlgebra.EnrichedProjective.Native.Diagrams
