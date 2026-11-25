/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.Zero

set_option autoImplicit false
noncomputable section
universe u v uC vC
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective

namespace NativePresentationZeroOwner
variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
variable {C : Type uC} [Category.{vC} C]

example (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    IsZero (NativePresentation.Zero.object e) := NativePresentation.Zero.isZero e

example (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    e.functor.obj (NativePresentation.Zero.object e) ≅ Native.Diagrams.zeroDiagram :=
  NativePresentation.Zero.comparisonIso e

example (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) {X Y : C} (f : X ⟶ Y) :
    ((NativePresentation.Zero.fromZeroArrow e).map f).right = f :=
  NativePresentation.Zero.fromZeroArrow_map_right e f

example (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (X : C) :
    ((NativePresentation.Zero.toZeroArrowIso e).hom.app X).right =
      e.counitIso.hom.app Native.Diagrams.zeroDiagram :=
  NativePresentation.Zero.toZeroArrowIso_hom_app_right e X



end NativePresentationZeroOwner

/-! All original signature and axiom queries use the actual producer environment. -/

run_cmd do
  let env ← Lean.getEnv
  let standard : Array Lean.Name := #[`propext, `Quot.sound, `Classical.choice]
  let moduleName :=
    (("MathlibExt.AlgebraicTopology.ModelCategory." ++
      "EnrichedProjectiveNativePresentation.Zero").toName)
  let roots : Array (Lean.Name × Bool) := #[
    ("HomotopicalAlgebra.EnrichedProjective.NativePresentation.Zero.object".toName, false),
    ((("HomotopicalAlgebra.EnrichedProjective.NativePresentation.Zero." ++
      "comparisonIso").toName), false),
    ((("HomotopicalAlgebra.EnrichedProjective.NativePresentation.Zero." ++
      "mapped_isZero").toName), true),
    ("HomotopicalAlgebra.EnrichedProjective.NativePresentation.Zero.isZero".toName, true),
    ((("HomotopicalAlgebra.EnrichedProjective.NativePresentation.Zero." ++
      "isInitial").toName), false),
    ((("HomotopicalAlgebra.EnrichedProjective.NativePresentation.Zero." ++
      "isTerminal").toName), false),
    ((("HomotopicalAlgebra.EnrichedProjective.NativePresentation.Zero." ++
      "hasZeroObject").toName), true),
    ((("HomotopicalAlgebra.EnrichedProjective.NativePresentation.Zero.toObject").toName), false),
    ((("HomotopicalAlgebra.EnrichedProjective.NativePresentation.Zero." ++
      "fromObject").toName), false),
    ((("HomotopicalAlgebra.EnrichedProjective.NativePresentation.Zero." ++
      "toObject_naturality").toName), true),
    ((("HomotopicalAlgebra.EnrichedProjective.NativePresentation.Zero." ++
      "fromObject_naturality").toName), true),
    ((("HomotopicalAlgebra.EnrichedProjective.NativePresentation.Zero." ++
      "fromZeroArrow").toName), false),
    ((("HomotopicalAlgebra.EnrichedProjective.NativePresentation.Zero." ++
      "toZeroArrow").toName), false),
    ((("HomotopicalAlgebra.EnrichedProjective.NativePresentation.Zero." ++
      "fromZeroArrow_map_left").toName), true),
    ((("HomotopicalAlgebra.EnrichedProjective.NativePresentation.Zero." ++
      "fromZeroArrow_map_right").toName), true),
    ((("HomotopicalAlgebra.EnrichedProjective.NativePresentation.Zero." ++
      "toZeroArrow_map_left").toName), true),
    ((("HomotopicalAlgebra.EnrichedProjective.NativePresentation.Zero." ++
      "toZeroArrow_map_right").toName), true),
    ((("HomotopicalAlgebra.EnrichedProjective.NativePresentation.Zero." ++
      "fromZeroArrowObjIso").toName), false),
    ((("HomotopicalAlgebra.EnrichedProjective.NativePresentation.Zero." ++
      "toZeroArrowObjIso").toName), false),
    ((("HomotopicalAlgebra.EnrichedProjective.NativePresentation.Zero." ++
      "fromZeroArrowIso").toName), false),
    ((("HomotopicalAlgebra.EnrichedProjective.NativePresentation.Zero." ++
      "toZeroArrowIso").toName), false),
    ((("HomotopicalAlgebra.EnrichedProjective.NativePresentation.Zero." ++
      "fromZeroArrowIso_hom_app_left").toName), true),
    ((("HomotopicalAlgebra.EnrichedProjective.NativePresentation.Zero." ++
      "fromZeroArrowIso_hom_app_right").toName), true),
    ((("HomotopicalAlgebra.EnrichedProjective.NativePresentation.Zero." ++
      "toZeroArrowIso_hom_app_left").toName), true),
    ((("HomotopicalAlgebra.EnrichedProjective.NativePresentation.Zero." ++
      "toZeroArrowIso_hom_app_right").toName), true)
  ]
  let some moduleIndex := env.getModuleIdx? moduleName
    | throwError m!"whole original producer absent: {moduleName}"
  for (declaration, theoremExpected) in roots do
    unless env.getModuleIdxFor? declaration == some moduleIndex do
      throwError m!"wrong actual defining module: {declaration}"
    let some info := env.find? declaration
      | throwError m!"missing original declaration: {declaration}"
    let (kind, isTheorem) := match info with
      | .defnInfo _ => ("definition", false)
      | .thmInfo _ => ("theorem", true)
      | _ => ("unexpected", !theoremExpected)
    unless isTheorem == theoremExpected do
      throwError m!"original declaration kind changed: {declaration}"
    let signature ← Lean.Elab.Command.liftTermElabM do
      Lean.withOptions (fun opts => opts.setBool `pp.universes true) do
        Lean.Meta.ppExpr info.type
    Lean.logInfo m!"originalFunctionTYPE {declaration}: {signature}"
    Lean.logInfo m!"originalFullTypeExpr {declaration}: {reprStr info.type}"
    Lean.logInfo m!"originalKernelKind {declaration}: {kind}"
    let axioms ← Lean.Elab.Command.liftCoreM (Lean.collectAxioms declaration)
    for axiomName in axioms do
      unless standard.contains axiomName do
        throwError m!"nonstandard axiom {axiomName} in {declaration}"
    Lean.logInfo m!"originalStandardAxioms {declaration}: {axioms}"
    Lean.logInfo m!"originalActualModule {declaration}: {moduleName}"
