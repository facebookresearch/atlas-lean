/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.Zero

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalClosed
open HomotopicalAlgebra.EnrichedProjective.Native

namespace NativeDiagramZeroOwner

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]

example : HasInitial (EnrichedFunctorCat PointedCGWH.{u, v} A) := Diagrams.nativeHasInitial
example : HasTerminal (EnrichedFunctorCat PointedCGWH.{u, v} A) := Diagrams.nativeHasTerminal
example : HasZeroObject (EnrichedFunctorCat PointedCGWH.{u, v} A) := Diagrams.nativeHasZeroObject
example : IsZero (Diagrams.initialDiagram (A := A)) := Diagrams.initialDiagram_isZero
example : IsZero (Diagrams.terminalDiagram (A := A)) := Diagrams.terminalDiagram_isZero
example : IsInitial (Diagrams.zeroDiagram (A := A)) := Diagrams.zeroDiagramIsInitial
example : IsTerminal (Diagrams.zeroDiagram (A := A)) := Diagrams.zeroDiagramIsTerminal

example (a : A) : IsZero ((Diagrams.zeroDiagram (A := A)).toEnrichedFunctor.obj a) :=
  Diagrams.initialDiagram_component_isZero a

example {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    (Diagrams.fromZeroArrow.map f).left = 𝟙 Diagrams.zeroDiagram ∧
      (Diagrams.fromZeroArrow.map f).right = f :=
  ⟨Diagrams.fromZeroArrow_map_left f, Diagrams.fromZeroArrow_map_right f⟩

example {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    (Diagrams.toZeroArrow.map f).left = f ∧
      (Diagrams.toZeroArrow.map f).right = 𝟙 Diagrams.zeroDiagram :=
  ⟨Diagrams.toZeroArrow_map_left f, Diagrams.toZeroArrow_map_right f⟩

example (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    Diagrams.zeroTo X = initial.to X := Diagrams.zeroTo_eq_initial_to X

example {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    Diagrams.zeroTo X ≫ f = Diagrams.zeroTo Y := Diagrams.zeroTo_naturality f

example {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    f ≫ Diagrams.toZero Y = Diagrams.toZero X := Diagrams.toZero_naturality f


example : Diagrams.zeroDiagramIsInitial (A := A) =
    (Diagrams.zeroDiagram_isZero (A := A)).isInitial := rfl

example : Diagrams.zeroDiagramIsTerminal (A := A) =
    (Diagrams.zeroDiagram_isZero (A := A)).isTerminal := rfl

end NativeDiagramZeroOwner

run_cmd do
  let env ← Lean.getEnv
  let moduleName :=
    "MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.Zero".toName
  let some moduleIndex := env.getModuleIdx? moduleName
    | throwError "actual current original native zero source not loaded"
  let roots : Array Lean.Name := #[
    (("HomotopicalAlgebra.EnrichedProjective.Native.Diagrams." ++
      "nativeHasInitial").toName),
    (("HomotopicalAlgebra.EnrichedProjective.Native.Diagrams." ++
      "nativeHasTerminal").toName),
    (("HomotopicalAlgebra.EnrichedProjective.Native.Diagrams." ++
      "initialDiagram").toName),
    (("HomotopicalAlgebra.EnrichedProjective.Native.Diagrams." ++
      "terminalDiagram").toName),
    (("HomotopicalAlgebra.EnrichedProjective.Native.Diagrams." ++
      "initialDiagramComponentZeroIso").toName),
    (("HomotopicalAlgebra.EnrichedProjective.Native.Diagrams." ++
      "terminalDiagramComponentZeroIso").toName),
    (("HomotopicalAlgebra.EnrichedProjective.Native.Diagrams." ++
      "initialDiagram_component_isZero").toName),
    (("HomotopicalAlgebra.EnrichedProjective.Native.Diagrams." ++
      "terminalDiagram_component_isZero").toName),
    (("HomotopicalAlgebra.EnrichedProjective.Native.Diagrams." ++
      "initialDiagram_isZero").toName),
    (("HomotopicalAlgebra.EnrichedProjective.Native.Diagrams." ++
      "terminalDiagram_isZero").toName),
    (("HomotopicalAlgebra.EnrichedProjective.Native.Diagrams." ++
      "nativeHasZeroObject").toName),
    (("HomotopicalAlgebra.EnrichedProjective.Native.Diagrams." ++
      "zeroDiagram").toName),
    (("HomotopicalAlgebra.EnrichedProjective.Native.Diagrams." ++
      "zeroDiagram_isZero").toName),
    (("HomotopicalAlgebra.EnrichedProjective.Native.Diagrams." ++
      "zeroDiagramIsInitial").toName),
    (("HomotopicalAlgebra.EnrichedProjective.Native.Diagrams." ++
      "zeroDiagramIsTerminal").toName),
    (("HomotopicalAlgebra.EnrichedProjective.Native.Diagrams." ++
      "initialTerminalIso").toName),
    (("HomotopicalAlgebra.EnrichedProjective.Native.Diagrams." ++
      "zeroTo").toName),
    (("HomotopicalAlgebra.EnrichedProjective.Native.Diagrams." ++
      "toZero").toName),
    (("HomotopicalAlgebra.EnrichedProjective.Native.Diagrams." ++
      "zeroTo_eq_initial_to").toName),
    (("HomotopicalAlgebra.EnrichedProjective.Native.Diagrams." ++
      "zeroTo_naturality").toName),
    (("HomotopicalAlgebra.EnrichedProjective.Native.Diagrams." ++
      "toZero_naturality").toName),
    (("HomotopicalAlgebra.EnrichedProjective.Native.Diagrams." ++
      "fromZeroArrow").toName),
    (("HomotopicalAlgebra.EnrichedProjective.Native.Diagrams." ++
      "toZeroArrow").toName),
    (("HomotopicalAlgebra.EnrichedProjective.Native.Diagrams." ++
      "fromZeroArrow_obj").toName),
    (("HomotopicalAlgebra.EnrichedProjective.Native.Diagrams." ++
      "toZeroArrow_obj").toName),
    (("HomotopicalAlgebra.EnrichedProjective.Native.Diagrams." ++
      "fromZeroArrow_map_left").toName),
    (("HomotopicalAlgebra.EnrichedProjective.Native.Diagrams." ++
      "fromZeroArrow_map_right").toName),
    (("HomotopicalAlgebra.EnrichedProjective.Native.Diagrams." ++
      "toZeroArrow_map_left").toName),
    (("HomotopicalAlgebra.EnrichedProjective.Native.Diagrams." ++
      "toZeroArrow_map_right").toName),
    (("HomotopicalAlgebra.EnrichedProjective.Native.Diagrams." ++
      "fromZeroArrow_leftFunc").toName),
    (("HomotopicalAlgebra.EnrichedProjective.Native.Diagrams." ++
      "fromZeroArrow_rightFunc").toName),
    (("HomotopicalAlgebra.EnrichedProjective.Native.Diagrams." ++
      "toZeroArrow_leftFunc").toName),
    (("HomotopicalAlgebra.EnrichedProjective.Native.Diagrams." ++
      "toZeroArrow_rightFunc").toName)
  ]
  let standard : Array Lean.Name := #[`propext, `Quot.sound, `Classical.choice]
  for declaration in roots do
    unless env.getModuleIdxFor? declaration == some moduleIndex do
      throwError m!"wrong actual native zero defining module: {declaration}"
    let some info := env.find? declaration
      | throwError m!"missing original native zero root: {declaration}"
    let signature ← Lean.Elab.Command.liftTermElabM do Lean.Meta.ppExpr info.type
    Lean.logInfo m!"originalNativeZeroFullSignature {declaration}: {signature}"
    let axioms ← Lean.Elab.Command.liftCoreM (Lean.collectAxioms declaration)
    for axiomName in axioms do
      unless standard.contains axiomName do
        throwError m!"nonstandard axiom {axiomName} in {declaration}"
    Lean.logInfo m!"originalNativeZeroAxioms {declaration}: {axioms}"
  Lean.logInfo m!"actualOriginalNativeZeroModule {moduleName}: roots {roots.size}"
