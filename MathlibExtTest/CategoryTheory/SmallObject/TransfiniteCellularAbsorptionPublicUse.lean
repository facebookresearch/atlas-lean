/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.SmallObject.CoherentRetracts.TransfiniteAbsorption
public import Batteries.Tactic.Lint
public import Lean.Util.CollectAxioms

/-!
# Original outer and inner histories in cellular retract absorption

These clients retain the supplied stage representatives and original inner
orders, including genuine maximal vertices. The whole auxiliary diagram,
natural splitting and endpoint Arrow retract use the original outer order.
Object, Hom, outer order, inner order and cell-label universes are independent.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace OriginalTransfiniteCellularPublicUse

universe u v w w' ν
open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject.CoherentRetracts
open CategoryTheory.SmallObject.CellularNormalization

section OriginalRepresentatives

variable {C : Type u} [Category.{v} C] {J : Type w}
  [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasPushouts C] [HasColimitsOfSize.{w, w} C]
  (P : MorphismProperty C) {X Y : C} {f : X ⟶ Y}
  (outer : CategoryTheory.TransfiniteCompositionOfShape J f)
  {A B : {j : J // ¬ IsMax j} → C}
  (k : ∀ i, A i ⟶ B i)
  (R : ∀ i, RetractArrow (outer.F.map (homOfLE (Order.le_succ i.1))) (k i))
  (K : {j : J // ¬ IsMax j} → OriginalInnerShape.{w'})
  (c : ∀ i, (MorphismProperty.coproducts.{ν} P).pushouts.TransfiniteCompositionOfShape
    (K i).carrier (k i))
  (emptySource : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
  (emptyTarget : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
  (hSource : IsColimit emptySource) (hTarget : IsColimit emptyTarget)

noncomputable local instance completedLinear (j : J) :
    LinearOrder (originalCompletedFamily K j) := (completeOriginalShapes K j).linearOrder
noncomputable local instance completedBot (j : J) :
    OrderBot (originalCompletedFamily K j) := (completeOriginalShapes K j).orderBot
noncomputable local instance completedSucc (j : J) :
    SuccOrder (originalCompletedFamily K j) := (completeOriginalShapes K j).succOrder
local instance completedWF (j : J) : WellFoundedLT (originalCompletedFamily K j) :=
  (completeOriginalShapes K j).wellFounded
local instance : WellFoundedLT (Index (originalCompletedFamily K)) := lexWellFounded
noncomputable local instance : SuccOrder (Index (originalCompletedFamily K)) := flatSuccOrder

include R c in
example : ∃ (Z : C) (g : X ⟶ Z)
    (_flat : (MorphismProperty.coproducts.{ν} P).pushouts.TransfiniteCompositionOfShape
      (Index (originalCompletedFamily K)) g)
    (G : J ⥤ C) (d : CategoryTheory.TransfiniteCompositionOfShape J g)
    (_inner : ∀ i : {j : J // ¬ IsMax j},
      (MorphismProperty.coproducts.{ν} P).pushouts.TransfiniteCompositionOfShape (K i).carrier
        (G.map (homOfLE (Order.le_succ i.1))))
    (incl : outer.F ⟶ G) (ret : G ⟶ outer.F) (h : RetractArrow f g),
    d.F = G ∧ incl ≫ ret = 𝟙 outer.F ∧ h.i.left = 𝟙 X ∧ h.r.left = 𝟙 X ∧
    h.i.left ≫ g = f ≫ h.i.right ∧ h.r.left ≫ f = g ≫ h.r.right ∧
    h.i.right ≫ h.r.right = 𝟙 Y := by
  obtain ⟨Z, g, flat, G, d, inner, incl, ret, h, hD, hSplit, hI, hR⟩ :=
    ChosenCellularStages.existsOriginalTransfiniteCellularAbsorption P outer k R K c
      emptySource emptyTarget hSource hTarget
  exact ⟨Z, g, flat, G, d, inner, incl, ret, h, hD, hSplit, hI, hR,
    h.i_w, h.r_w, h.retract_right⟩

example (i : {j : J // ¬ IsMax j}) :
    let d := ChosenCellularStages.pushedOriginalHistory P outer k R K c i
    d.isoBot.inv ≫ d.incl.app ⊥ =
      (ChosenCellularStages.originalTarget P outer k R K c).map
        (homOfLE (Order.le_succ i.1)) :=
  (ChosenCellularStages.pushedOriginalHistory P outer k R K c i).fac

example (i : {j : J // ¬ IsMax j}) :
    completeOriginalHistories (ChosenCellularStages.originalTarget P outer k R K c) K
      (fun j => (ChosenCellularStages.pushedOriginalHistory
        P outer k R K c j).toTransfiniteCompositionOfShape) i.1 ≍
      (ChosenCellularStages.pushedOriginalHistory
        P outer k R K c i).toTransfiniteCompositionOfShape :=
  completeOriginalHistories_nonmax _ K _ i.1 i.2

example (i : {j : J // ¬ IsMax j}) : completeOriginalShapes K i.1 = K i :=
  completeOriginalShapes_nonmax K i.1 i.2

example (j : J) (hj : IsMax j) : Subsingleton (originalCompletedFamily K j) := by
  classical
  unfold originalCompletedFamily completeOriginalShapes
  simp only [dite_eq_left hj]
  infer_instance

end OriginalRepresentatives

section ActualTransfiniteClosure

variable {C : Type u} [Category.{v} C] {J : Type w}
  [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasPushouts C] [HasColimitsOfSize.{w, w} C]
  (P : MorphismProperty C) {X Y : C} {f : X ⟶ Y}

example (outer : (MorphismProperty.transfiniteCompositions.{w}
    (MorphismProperty.coproducts.{ν} P).pushouts).retracts.TransfiniteCompositionOfShape J f)
    (e : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C))) (he : IsColimit e) :
    (MorphismProperty.transfiniteCompositions.{w}
      (MorphismProperty.coproducts.{ν} P).pushouts).retracts f :=
  cellular_retracts_of_transfiniteComposition P outer e e he he

end ActualTransfiniteClosure

end OriginalTransfiniteCellularPublicUse

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx?
      `MathlibExt.CategoryTheory.SmallObject.CoherentRetracts.TransfiniteAbsorption
    | throwError "actual transfinite absorption module is missing"
  let names := env.constants.fold (init := #[]) fun xs n _ =>
    if env.getModuleIdxFor? n == some idx then xs.push n else xs
  unless names.size > 0 do throwError "empty transfinite absorption module"
  for n in names do
    let axs ← Lean.collectAxioms n
    let bad := axs.filter fun a => a != ``propext && a != ``Quot.sound && a != ``Classical.choice
    unless bad.isEmpty do throwError "forbidden axioms in {n}: {bad}"
  logInfo m!"TRANSFINITE_CELLULAR_PUBLIC_AXIOMS {names.size} standard-three only"

#lint only unusedArguments in
  MathlibExt.CategoryTheory.SmallObject.CoherentRetracts.TransfiniteAbsorption
