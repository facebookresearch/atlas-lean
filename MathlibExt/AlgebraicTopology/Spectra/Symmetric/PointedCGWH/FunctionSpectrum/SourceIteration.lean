/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.Lambda
import MathlibExt.AlgebraicTopology.Spectra.Sequential.OrderedLoop.Association
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.CoaugmentationTelescope
import MathlibExt.CategoryTheory.Functor.CoaugmentationEvaluation
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.CoaugmentationTelescopeModel
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHLoopWeakEquivalence

/-!
# The original native function-spectrum coaugmentation and its full iteration

The transition is the original `Rⁿ(λ*_X)`, with the canonical reassociation
of that same native functor. The evaluated comparison is constructed in
the original-input order; every stage retains the actual native free
function comparison. No equation with the coaugmentation at `RⁿX`, and
no sphere self-interchange identity, is assumed.

The native mapping-cylinder telescope uses precisely these full source
transitions on the unchanged enriched spectrum carrier.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CGWH.modelCategory

namespace NativeOmegaRecovery.NativeSymmetricR.SourceIteration

open PointedCGWH.SequentialSpectrum.OrderedLoop.AssociationGeometry (loopPower_succ_prefix)

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev J := PointedCGWH.SymmetricOperatorIndex.{u, v}
private abbrev Carrier := EnrichedFunctorCat V.{u, v} J.{u, v}

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal

/-- The original complete prefix association of the actual native function functor. -/
def prefixComparison (n : ℕ) : iterate.{u, v} (n + 1) ≅ functor ⋙ iterate n :=
  Functor.Iteration.iteratePrefixIso functor n

/-- The actual original function-source coaugmentation is iterated on its original input. -/
def transition (n : ℕ) : iterate.{u, v} n ⟶ iterate (n + 1) :=
  Functor.Iteration.inputTransition (C := Carrier.{u, v}) (F := functor.{u, v})
    NativeSymmetricLambda.coaugmentation n

/-- Every transition retains the literal `Rⁿ(λ*_X)` and its canonical inverse prefix map. -/
theorem transition_app (n : ℕ) (X : Carrier.{u, v}) :
    (transition n).app X =
      (iterate n).map (X := X) (Y := functor.obj X)
        (NativeSymmetricLambda.coaugmentation.app X) ≫
        (prefixComparison n).inv.app X := by
  unfold transition prefixComparison
  rfl

/-- The whole original coaugmentation is natural on every input arrow at every stage. -/
theorem transition_naturality (n : ℕ) {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    (iterate n).map (X := X) (Y := Y) f ≫ (transition n).app Y =
      (transition n).app X ≫ (iterate (n + 1)).map (X := X) (Y := Y) f :=
  (transition n).naturality f

/-- Elaborate the explicitly supplied whole native transition proof and submit
its complete declared proposition to the ordinary kernel. -/
local elab (name := exactWholeTypedTransitionApplication)
    "exact_whole_transition_from_data " "[" originalCarrier:term "," nativeFunctor:term ","
      nativeCoaugmentation:term "," stage:term "," inputObject:term "]" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let carrier ← Lean.Elab.Term.elabTerm originalCarrier none
    let f ← Lean.Elab.Term.elabTerm nativeFunctor none
    let eta ← Lean.Elab.Term.elabTerm nativeCoaugmentation none
    let n ← Lean.Elab.Term.elabTerm stage none
    let X ← Lean.Elab.Term.elabTerm inputObject none
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let carrier ← Lean.instantiateMVars carrier
    let f ← Lean.instantiateMVars f
    let eta ← Lean.instantiateMVars eta
    let n ← Lean.instantiateMVars n
    let X ← Lean.instantiateMVars X
    let fType ← Lean.Meta.inferType f
    let args := fType.getAppArgs
    unless fType.getAppFn.isConstOf ``CategoryTheory.Functor && args.size == 4 do
      throwError "The complete original functor category argument order changed"
    let category := args[1]!
    let body ← Lean.Meta.mkAppOptM ``Functor.Iteration.inputTransition_succ_app
      #[some carrier, some category, some f, some eta, some n, some X]
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let body ← Lean.instantiateMVars body
    unless !body.hasMVar && !body.hasLevelMVar && !body.hasSorry do
      throwError "The complete actual generic transition proof is unresolved"
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.assign body
    Lean.Elab.Tactic.replaceMainGoal []

/-- Apply the supplied independent proposition to the original source carrier
and the category in the whole functor's already checked declared type. -/
local elab (name := exactWholeOriginalNativeTypeApplication)
    "whole_native_source_type " "[" literalType:term "," originalCarrier:term ","
      nativeFunctor:term ","
      nativeCoaugmentation:term "]" : term => do
  let carrier ← Lean.Elab.Term.elabTerm originalCarrier none
  let f ← Lean.Elab.Term.elabTerm nativeFunctor none
  let eta ← Lean.Elab.Term.elabTerm nativeCoaugmentation none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let carrier ← Lean.instantiateMVars carrier
  let f ← Lean.instantiateMVars f
  let eta ← Lean.instantiateMVars eta
  let fType ← Lean.Meta.inferType f
  let args := fType.getAppArgs
  unless fType.getAppFn.isConstOf ``CategoryTheory.Functor && args.size == 4 do
    throwError "The complete original functor carrier/category argument order changed"
  let category := args[1]!
  let literal ← Lean.Elab.Term.elabTerm literalType none
  let .lam _ carrierDomain _ _ := literal |
    throwError "The complete independent literal proposition has no carrier parameter"
  unless ← Lean.Meta.isDefEq carrierDomain (← Lean.Meta.inferType carrier) do
    throwError "The independently supplied carrier sort differs from the actual original carrier"
  let applied ← Lean.Meta.mkAppOptM' literal
    #[some carrier, some category, some f, some eta]
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let result ← Lean.instantiateMVars applied
  unless !result.hasMVar && !result.hasLevelMVar && !result.hasSorry do
    throwError "The complete independently supplied native proposition is unresolved"
  return result

/-- The successor transition applies the same actual native function functor. -/
abbrev transitionSuccApp :
    whole_native_source_type [
      (fun (C₀ : Type _) [Category.{v} C₀] (F : C₀ ⥤ C₀)
      (η : @Quiver.Hom (C₀ ⥤ C₀)
        ((Functor.category : Category (C₀ ⥤ C₀)).toCategoryStruct.toQuiver)
        (𝟭 C₀) F) =>
      ∀ (n : ℕ) (X : C₀),
        (Functor.Iteration.inputTransition η (n + 1)).app X =
          F.map (X := (Functor.Iteration.iterate F n).obj X)
            (Y := (Functor.Iteration.iterate F (n + 1)).obj X)
            ((Functor.Iteration.inputTransition η n).app X)),
      Carrier.{u, v}, functor.{u, v}, NativeSymmetricLambda.coaugmentation.{u, v}] := by
  intro n X
  exact_whole_transition_from_data [
    Carrier.{u, v}, functor.{u, v}, NativeSymmetricLambda.coaugmentation.{u, v}, n, X]

/-- Every original operator Hom action remains natural under the full source transition. -/
theorem transition_uncurried_naturality (n : ℕ) (X : Carrier.{u, v}) (a b : J.{u, v}) :
    MonoidalClosed.uncurry (((iterate n).obj X).toEnrichedFunctor.map a b) ≫
        component ((transition n).app X) b =
      (component ((transition n).app X) a ⊗ₘ 𝟙 (a ⟶[V.{u, v}] b)) ≫
        MonoidalClosed.uncurry (((iterate (n + 1)).obj X).toEnrichedFunctor.map a b) :=
  ((transition n).app X).uncurriedNaturality a b

/-- The complete native `Rⁿ(λ*_X)` diagram, including all nonadjacent arrows. -/
abbrev diagram :=
  Functor.Iteration.inputDiagram (C := Carrier.{u, v}) (F := functor.{u, v})
    NativeSymmetricLambda.coaugmentation

/-- The original native input maps act on the entire source iteration diagram. -/
def diagramFunctor : Carrier.{u, v} ⥤ (ℕ ⥤ Carrier.{u, v}) :=
  Functor.Iteration.inputDiagramFunctor (C := Carrier.{u, v}) (F := functor.{u, v})
    NativeSymmetricLambda.coaugmentation

/-- Every source diagram stage is the original entire native iterate. -/
theorem diagram_obj (X : Carrier.{u, v}) (n : ℕ) :
    (diagram X).obj n = (iterate n).obj X := rfl

/-- The source successor arrow is the original iterated coaugmentation. -/
abbrev diagramMapSucc :=
  Functor.Iteration.inputDiagram_map_succ (C := Carrier.{u, v}) (F := functor.{u, v})
    NativeSymmetricLambda.coaugmentation

/-- The entire compared coaugmentation is the actual source whiskering and free comparison. -/
def coaugmentationCoordinate (m : ℕ) :
    level.{u, v} m ⟶ level (m + 1) ⋙ ihom PointedCGWH.sphereOne.{u, v} :=
  (level m).leftUnitor.inv ≫
    Functor.whiskerRight NativeSymmetricLambda.coaugmentation (level m) ≫
      (levelComparison m).hom

/-- Every original input arrow is natural for the actual compared coaugmentation coordinate. -/
theorem coaugmentationCoordinate_naturality (m : ℕ)
    {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    (level m).map f ≫ (coaugmentationCoordinate m).app Y =
      (coaugmentationCoordinate m).app X ≫
        (ihom PointedCGWH.sphereOne).map ((level (m + 1)).map f) :=
  (coaugmentationCoordinate m).naturality f

/-- The generic output power is the same entire original sphere-one loop power. -/
theorem loopPower_eq_original (n : ℕ) :
    Functor.Iteration.iterate (ihom PointedCGWH.sphereOne.{u, v}) n =
      PointedCGWH.SequentialSpectrum.OrderedLoop.loopPower.{u, v} n := by
  induction n with
  | zero => rfl
  | succ n hn =>
    exact congrArg (fun G : V.{u, v} ⥤ V.{u, v} =>
      G ⋙ ihom PointedCGWH.sphereOne) hn

/-- The canonical whole output identification only associates the same loop functor. -/
def outputPowerComparison (n m : ℕ) :
    level.{u, v} (m + n) ⋙
        Functor.Iteration.iterate (ihom PointedCGWH.sphereOne.{u, v}) n ≅
      level (m + n) ⋙ PointedCGWH.SequentialSpectrum.OrderedLoop.loopPower.{u, v} n :=
  Functor.isoWhiskerLeft (level (m + n)) (eqToIso (loopPower_eq_original n))

/-- The original source-order comparison uses the actual native free-function maps. -/
def sourcePowerComparison (n m : ℕ) :
    iterate.{u, v} n ⋙ level m ≅ level (m + n) ⋙
      Functor.Iteration.iterate (ihom PointedCGWH.sphereOne.{u, v}) n :=
  Functor.CoaugmentationEvaluation.comparison functor (ihom PointedCGWH.sphereOne)
    level levelComparison n m

/-- The output family is the complete original level and complete original loop power. -/
def outputFamily (n m : ℕ) : Carrier.{u, v} ⥤ V.{u, v} :=
  level (m + n) ⋙ PointedCGWH.SequentialSpectrum.OrderedLoop.loopPower n

/-- Each original evaluated stage uses the same native free maps and whole original loop power. -/
abbrev levelComparisonSource (n m : ℕ) :
    iterate.{u, v} n ⋙ level m ≅
      level (m + n) ⋙ PointedCGWH.SequentialSpectrum.OrderedLoop.loopPower.{u, v} n :=
  Functor.CoaugmentationEvaluation.comparisonWithOutput (R := functor.{u, v})
    (ihom PointedCGWH.sphereOne.{u, v}) level levelComparison outputFamily
    outputPowerComparison n m

/-- The actual compared original-input coaugmentation supplies every output transition. -/
abbrev sourcePowerTransition :=
  Functor.CoaugmentationEvaluation.diagonalTransition (C := Carrier.{u, v})
    (R := functor.{u, v}) (ihom PointedCGWH.sphereOne.{u, v}) level levelComparison
    NativeSymmetricLambda.coaugmentation

/-- Its source square is derived for every actual native `Rⁿ(λ*_X)`. -/
abbrev sourcePowerTransitionSquare :=
  Functor.CoaugmentationEvaluation.inputTransition_square (C := Carrier.{u, v})
    (R := functor.{u, v}) (ihom PointedCGWH.sphereOne.{u, v}) level levelComparison
    NativeSymmetricLambda.coaugmentation

/-- The inverse source square retains the same actual iterated coaugmentation. -/
abbrev sourcePowerTransitionSquareInv :=
  Functor.CoaugmentationEvaluation.inputTransition_square_inv (C := Carrier.{u, v})
    (R := functor.{u, v}) (ihom PointedCGWH.sphereOne.{u, v}) level levelComparison
    NativeSymmetricLambda.coaugmentation

/-- The native diagonal transition keeps the complete original output loop power. -/
abbrev levelTransitionSource (n m : ℕ) :
    level.{u, v} (m + n) ⋙ PointedCGWH.SequentialSpectrum.OrderedLoop.loopPower.{u, v} n ⟶
      level (m + (n + 1)) ⋙ PointedCGWH.SequentialSpectrum.OrderedLoop.loopPower.{u, v} (n + 1) :=
  Functor.CoaugmentationEvaluation.transitionWithOutput (R := functor.{u, v})
    (ihom PointedCGWH.sphereOne.{u, v}) level levelComparison NativeSymmetricLambda.coaugmentation
    outputFamily outputPowerComparison n m

/-- The full native transition square follows from the original source evaluation theorem. -/
abbrev levelTransitionSourceSquare :=
  Functor.CoaugmentationEvaluation.inputTransition_output_square (C := Carrier.{u, v})
    (R := functor.{u, v}) (ihom PointedCGWH.sphereOne.{u, v}) level levelComparison
    NativeSymmetricLambda.coaugmentation outputFamily outputPowerComparison

/-- Both original inverse maps commute with the same entire source transition. -/
abbrev levelTransitionSourceSquareInv :=
  Functor.CoaugmentationEvaluation.inputTransition_output_square_inv (C := Carrier.{u, v})
    (R := functor.{u, v}) (ihom PointedCGWH.sphereOne.{u, v}) level levelComparison
    NativeSymmetricLambda.coaugmentation outputFamily outputPowerComparison

/-- Both maps compare the entire actual native evaluated diagram in source order. -/
abbrev sourcePowerDiagramIso :=
  Functor.CoaugmentationEvaluation.diagramIso (C := Carrier.{u, v})
    (R := functor.{u, v}) (ihom PointedCGWH.sphereOne.{u, v}) level levelComparison
    NativeSymmetricLambda.coaugmentation

/-- The full original evaluated source-diagram comparison is natural in every native input. -/
abbrev sourcePowerDiagramNatIso :=
  Functor.CoaugmentationEvaluation.diagramNatIso (C := Carrier.{u, v})
    (R := functor.{u, v}) (ihom PointedCGWH.sphereOne.{u, v}) level levelComparison
    NativeSymmetricLambda.coaugmentation

/-- The source-order comparison is natural in every complete original native map. -/
theorem levelComparisonSource_naturality (n m : ℕ) {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    (level m).map ((iterate n).map f) ≫ (levelComparisonSource n m).hom.app Y =
      (levelComparisonSource n m).hom.app X ≫
        (PointedCGWH.SequentialSpectrum.OrderedLoop.loopPower n).map
          ((level (m + n)).map f) :=
  (levelComparisonSource n m).hom.naturality f

/-- Its inverse is natural on the same original complete input map. -/
theorem levelComparisonSource_inv_naturality (n m : ℕ)
    {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    (PointedCGWH.SequentialSpectrum.OrderedLoop.loopPower n).map
        ((level (m + n)).map f) ≫ (levelComparisonSource n m).inv.app Y =
      (levelComparisonSource n m).inv.app X ≫ (level m).map ((iterate n).map f) :=
  (levelComparisonSource n m).inv.naturality f

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The actual native telescope uses the original source-coaugmentation diagram. -/
abbrev telescopeFunctor :=
  PointedCGWH.EnrichedCoaugmentationTelescope.telescopeFunctor
    (I := J.{u, v}) (F := functor.{u, v}) NativeSymmetricLambda.coaugmentation

/-- Its unit is the actual chosen stage-zero leg on the same original native carrier. -/
abbrev telescopeUnit :=
  PointedCGWH.EnrichedCoaugmentationTelescope.unit
    (I := J.{u, v}) (F := functor.{u, v}) NativeSymmetricLambda.coaugmentation

/-- Every original cylinder stage uses the full actual native input transition. -/
def telescopeStage (n : ℕ) : Carrier.{u, v} ⥤ Carrier.{u, v} :=
  (PointedCGWH.EnrichedCoaugmentationTelescope.stage
    (I := J.{u, v}) (F := functor.{u, v}) NativeSymmetricLambda.coaugmentation n).functor

/-- Every projection retains the actual original whole native `Rⁿ` target. -/
abbrev telescopeProjection :=
  PointedCGWH.EnrichedCoaugmentationTelescope.projection
    (I := J.{u, v}) (F := functor.{u, v}) NativeSymmetricLambda.coaugmentation

/-- Every cylinder transition is the same original second-endpoint map. -/
abbrev telescopeTransition :=
  PointedCGWH.EnrichedCoaugmentationTelescope.transition
    (I := J.{u, v}) (F := functor.{u, v}) NativeSymmetricLambda.coaugmentation

/-- The entire cylinder projection factors precisely the original native `Rⁿ(λ*_X)` arrow. -/
abbrev telescopeTransitionProjection :=
  PointedCGWH.EnrichedCoaugmentationTelescope.transition_projection
    (I := J.{u, v}) (F := functor.{u, v}) NativeSymmetricLambda.coaugmentation

/-- The actual native free-one-sphere function functor preserves the original level weak class. -/
theorem functor_map_mem_weak {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (hf : weakEquivalences Carrier.{u, v} f) :
    weakEquivalences Carrier.{u, v} (functor.map f) := by
  let W := weakEquivalences Carrier.{u, v}
  let shift := PointedCGWH.SymmetricShift.functor.{u, v} firstIndex
  let shiftedLoop := shift ⋙ cotensor PointedCGWH.sphereOne.{u, v}
  have hfLevels :=
    (PointedCGWH.EnrichedCoaugmentationTelescope.weakEquivalences_iff_components f).mp hf
  have hs (a : J.{u, v}) :
      CGWH.weakHomotopyEquivalences (component (shift.map f) a).right := by
    rw [show component (shift.map f) a =
      component f ((PointedCGWH.SymmetricShift.indexShift firstIndex).obj a)
      from EnrichedFunctorCat.restrictionMap_component
        (PointedCGWH.SymmetricShift.indexShift firstIndex) f a]
    exact hfLevels _
  have hLoop : W (shiftedLoop.map f) := by
    apply (PointedCGWH.EnrichedCoaugmentationTelescope.weakEquivalences_iff_components _).mpr
    intro a
    change CGWH.weakHomotopyEquivalences
      (component (cotensorMap PointedCGWH.sphereOne (shift.map f)) a).right
    rw [cotensorMap_component]
    exact PointedCGWH.loop_map_mem_weakHomotopyEquivalences (component (shift.map f) a) (hs a)
  have hNat : functor.map f ≫ comparison.hom.app Y =
      comparison.hom.app X ≫ shiftedLoop.map f := comparison.hom.naturality f
  have hComp : W (functor.map f ≫ comparison.hom.app Y) := by
    rw [hNat]
    exact W.comp_mem _ _ (W.of_isIso _) hLoop
  exact W.of_postcomp _ _ (W.of_isIso _) hComp

end NativeOmegaRecovery.NativeSymmetricR.SourceIteration
