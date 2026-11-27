/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.SmallObject.CellularRetractsClosure
import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CellTreeWeakSaturation
import Lean.Util.CollectAxioms

/-!
# Actual maps and closure of original cellular Arrow retracts

Generic Arrow maps are checked in the low-level retract public client.
Cellular closure clients use the canonical class and actual stability producers.
Cell-tree clients retain the original root and endpoint, including empty trees.
-/

set_option autoImplicit false
noncomputable section

namespace OriginalCellularRetractsPublicUse

universe u v w κ ν t
open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject
open CategoryTheory.SmallObject.CellularRetractsClosure
open CategoryTheory.SmallObject.CellularNormalization

section DerivedCobaseClosure

variable {C : Type u} [Category.{v} C] [HasPushouts C]
  (P : MorphismProperty C)

example {A B : C} (f : A ⟶ B) (hf : P f) :
    (cellularClosure.{w, ν} P).retracts f := le_cellularRetracts P f hf

example {A B X Z : C} {f : A ⟶ B} {q : X ⟶ Z} {a : A ⟶ X} {b : B ⟶ Z}
    (sq : IsPushout a f q b) (hf : (cellularClosure.{w, ν} P).retracts f) :
    (cellularClosure.{w, ν} P).retracts q := by
  let _ := cellularRetractsIsStableUnderCobaseChange.{w, ν} P
  exact MorphismProperty.of_isPushout (P := (cellularClosure.{w, ν} P).retracts) sq hf

end DerivedCobaseClosure

section DerivedCoproductClosure

variable {C : Type u} [Category.{v} C] [HasPushouts C]
  [HasCoproducts.{w} C] [HasInitial C] (P : MorphismProperty C)

example : (cellularClosure.{w, ν} P).retracts.IsStableUnderCoproducts.{w} :=
  cellularRetractsIsStableUnderCoproducts P

example {I : Type w} {A B : I → C} (f : ∀ i, A i ⟶ B i)
    (hf : ∀ i, (cellularClosure.{w, ν} P).retracts (f i)) :
    (cellularClosure.{w, ν} P).retracts (Limits.Sigma.map f) := by
  let Q := (cellularClosure.{w, ν} P).retracts
  let _ : Q.IsStableUnderCoproducts.{w} := cellularRetractsIsStableUnderCoproducts P
  let τ : Discrete.functor A ⟶ Discrete.functor B :=
    Discrete.natTrans (fun i => f i.as)
  change Q (colimMap τ)
  exact MorphismProperty.colimMap (W := Q) τ (fun i => hf i.as)

end DerivedCoproductClosure

section DerivedTransfiniteClosure

variable {C : Type u} [Category.{v} C] [HasPushouts C]
  [HasColimitsOfSize.{w, w} C] (P : MorphismProperty C)
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {X Y : C} {f : X ⟶ Y}

example : MorphismProperty.IsStableUnderTransfiniteComposition.{w}
    (cellularClosure.{w, ν} P).retracts :=
  cellularRetractsIsStableUnderTransfiniteComposition P

example (outer : (cellularClosure.{w, ν} P).retracts.TransfiniteCompositionOfShape J f) :
    (cellularClosure.{w, ν} P).retracts f := by
  let _ := cellularRetractsIsStableUnderTransfiniteComposition.{w, ν} P
  exact (cellularClosure.{w, ν} P).retracts.transfiniteCompositionsOfShape_le J f outer.mem

end DerivedTransfiniteClosure

section ActualCellTreeEndpoint

attribute [local instance] CompactRootBaseChange.constructionIndexWellFounded
  CompactRootBaseChange.constructionIndexSuccOrder

variable {C : Type u} [Category.{v} C] {P : Type w} [PartialOrder P]
  {α : Type t} {s : α → Arrow C} {X : C}
  (W : MorphismProperty C) [W.IsStableUnderCobaseChange]
  [MorphismProperty.IsStableUnderTransfiniteComposition.{w} W]

example (T : CellTree s X (P := P)) (M : LowerSetColimitData T.diagram)
    (hCell : ∀ a : P, W (s (T.label a)).hom) : W T.hom :=
  CellTreeWeakSaturation.hom_mem W T M hCell

example [IsEmpty P] (T : CellTree s X (P := P))
    (M : LowerSetColimitData T.diagram) : W T.hom :=
  CellTreeWeakSaturation.hom_mem W T M (fun a => isEmptyElim a)

example (T : CellTree s X (P := P)) (M : LowerSetColimitData T.diagram) :
    let _ : WellFoundedLT P := T.wellFoundedLT
    (CellTreeWeakSaturation.presentation T M).F = CellTreeWeakSaturation.diagram T M ∧
      (CellTreeWeakSaturation.botIso T M).inv ≫
        (CellTreeWeakSaturation.endpoint T M).app ⊥ = T.hom := by
  let _ : WellFoundedLT P := T.wellFoundedLT
  exact ⟨rfl, CellTreeWeakSaturation.root_endpoint T M⟩

end ActualCellTreeEndpoint

end OriginalCellularRetractsPublicUse

open Lean Elab Command
run_cmd do
  let env ← getEnv
  for moduleName in #[
      `MathlibExt.CategoryTheory.SmallObject.CellularRetractsClosure,
      `MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CellTreeWeakSaturation] do
    let some idx := env.getModuleIdx? moduleName
      | throwError "actual cellular source module is missing: {moduleName}"
    let names := env.constants.fold (init := #[]) fun xs n _ =>
      if env.getModuleIdxFor? n == some idx then xs.push n else xs
    unless names.size > 0 do throwError "empty cellular module: {moduleName}"
    for n in names do
      let axs ← Lean.collectAxioms n
      let bad := axs.filter fun a => a != ``propext && a != ``Quot.sound && a != ``Classical.choice
      unless bad.isEmpty do throwError "forbidden axioms in {n}: {bad}"
    logInfo m!"CELLULAR_PUBLIC_AXIOMS {moduleName}: {names.size} standard-three only"
