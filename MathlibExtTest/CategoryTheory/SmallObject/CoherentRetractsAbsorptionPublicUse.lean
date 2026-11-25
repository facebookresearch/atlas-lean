/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.SmallObject.CoherentRetracts.Absorption
public import Batteries.Tactic.Lint
public import Lean.Util.CollectAxioms

/-!
# Public original-order coherent absorption and prefix APIs

The endpoint client uses the original diagram and source object, including both
Arrow squares and target splitting. Prefix clients use only the assumptions of
the restriction or actual successor construction they call. Object, Hom and
original-order universes remain independent.
-/

@[expose] public section
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `MathlibExt.CategoryTheory.SmallObject.CoherentRetracts.Absorption
    | throwError "actual absorption module is missing"
  let names := env.constants.fold (init := #[]) fun xs n _ =>
    if env.getModuleIdxFor? n == some idx then xs.push n else xs
  unless names.size > 0 do throwError "empty absorption module"
  for n in names do
    let axs ← Lean.collectAxioms n
    let bad := axs.filter fun a => a != ``propext && a != ``Quot.sound && a != ``Classical.choice
    unless bad.isEmpty do throwError "forbidden axioms in {n}: {bad}"
  logInfo m!"ABSORPTION_ALL_CONSTANTS {names.size} standard-three only"
#lint only unusedArguments in MathlibExt.CategoryTheory.SmallObject.CoherentRetracts.Absorption
#print axioms CategoryTheory.SmallObject.CoherentRetracts.prefixInductionData
#print axioms CategoryTheory.SmallObject.CoherentRetracts.coherentPrefixSection
#print axioms CategoryTheory.SmallObject.CoherentRetracts.coherentPrefixSection_bottom
#print axioms CategoryTheory.SmallObject.CoherentRetracts.existsCoherentRetractAbsorption

namespace OriginalAbsorptionPublicClient
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject.CoherentRetracts
variable {C : Type u} [Category.{v} C] {J : Type w}
  [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasPushouts C] [HasColimitsOfSize.{w, w} C]
  (P : MorphismProperty C) {X Y : C} {f : X ⟶ Y}
example (c : P.retracts.TransfiniteCompositionOfShape J f) :
    ∃ (Z : C) (g : X ⟶ Z) (d : P.pushouts.TransfiniteCompositionOfShape J g)
      (R : RetractArrow f g),
      R.i.left = 𝟙 X ∧ R.r.left = 𝟙 X ∧
      R.i.left ≫ g = f ≫ R.i.right ∧ R.r.left ≫ f = g ≫ R.r.right ∧
      R.i.right ≫ R.r.right = 𝟙 Y ∧
      ∀ (j : J) (_hj : ¬IsMax j), P.pushouts (d.F.map (homOfLE (Order.le_succ j))) := by
  obtain ⟨Z, g, d, R, hI, hR⟩ := existsCoherentRetractAbsorption P c
  exact ⟨Z, g, d, R, hI, hR, R.i_w, R.r_w, R.retract_right, d.map_mem⟩
end OriginalAbsorptionPublicClient

namespace OriginalAbsorptionPrefixPublicClient
universe u v w
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.SmallObject CategoryTheory.SmallObject.CoherentRetracts

section Restrictions
variable {C : Type u} [Category.{v} C] {J : Type w}
  [LinearOrder J] [OrderBot J] [SuccOrder J]
  (P : MorphismProperty C) (F : J ⥤ C)

example {j : J} (S : PrefixSplit P F j) : S.restrict le_rfl = S :=
  PrefixSplit.restrict_id S

example {i j k : J} (S : PrefixSplit P F k) (hij : i ≤ j) (hjk : j ≤ k) :
    (S.restrict hjk).restrict hij = S.restrict (hij.trans hjk) :=
  PrefixSplit.restrict_comp S hij hjk

example (j : J) (hj : ¬ IsMax j) :
    SuccStruct.extendToSucc hj ((Set.initialSegIic j).monotone.functor ⋙ F)
      (F.map (homOfLE (Order.le_succ j))) =
        (Set.initialSegIic (Order.succ j)).monotone.functor ⋙ F :=
  SuccStruct.extendToSucc_original_eq hj F

example [HasPushouts C] (j : J) (hj : ¬ IsMax j) (S : PrefixSplit P F j)
    {A B : C} (k : A ⟶ B)
    (R : RetractArrow (F.map (homOfLE (Order.le_succ j))) k) (hk : P k) :
    (PrefixSplitSuccessor.originalSuccessorState P F j S hj k R hk).restrict
      (Order.le_succ j) = S :=
  PrefixSplitSuccessor.originalSuccessorState_restrict P F j S hj k R hk
end Restrictions

section ConstructedSection
variable {C : Type u} [Category.{v} C] {J : Type w}
  [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasPushouts C] [HasColimitsOfSize.{w, w} C]
  (P : MorphismProperty C) (F : J ⥤ C) [F.IsWellOrderContinuous]
  (hF : ∀ (j : J) (_ : ¬ IsMax j), P.retracts (F.map (homOfLE (Order.le_succ j))))

example : (coherentPrefixSection P F hF).val (Opposite.op (⊥ : J)) =
    PrefixSplit.seed (P := P) (F := F) :=
  coherentPrefixSection_bottom P F hF

example :
    let D := PrefixSplitGlue.wholeDiagram P F (coherentPrefixSection P F hF)
    D ⋙ SplitObject.sourceFunctor = F ∧
      SplitObject.inclusionNatTrans D ≫ SplitObject.retractionNatTrans D =
        𝟙 (D ⋙ SplitObject.sourceFunctor) :=
  ⟨PrefixSplitGlue.wholeDiagram_source P F (coherentPrefixSection P F hF),
    SplitObject.inclusion_retraction _⟩
end ConstructedSection
end OriginalAbsorptionPrefixPublicClient

open Lean Elab Command
run_cmd do
  let env ← getEnv
  for mod in #[
      `MathlibExt.CategoryTheory.SmallObject.CoherentRetracts.PrefixSystem,
      `MathlibExt.CategoryTheory.SmallObject.CoherentRetracts.PrefixGlue,
      `MathlibExt.CategoryTheory.SmallObject.CoherentRetracts.Successors,
      `MathlibExt.CategoryTheory.SmallObject.CoherentRetracts.Limits] do
    let some idx := env.getModuleIdx? mod | throwError "coherent source module missing: {mod}"
    let names := env.constants.fold (init := #[]) fun xs n _ =>
      if env.getModuleIdxFor? n == some idx then xs.push n else xs
    unless names.size > 0 do throwError "empty coherent module: {mod}"
    for n in names do
      let axs ← Lean.collectAxioms n
      let bad := axs.filter fun a => a != ``propext && a != ``Quot.sound && a != ``Classical.choice
      unless bad.isEmpty do throwError "forbidden axioms in {n}: {bad}"
    logInfo m!"COHERENT_PUBLIC_CLIENT_AXIOMS {mod}: {names.size} standard-three only"
