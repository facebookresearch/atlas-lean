/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact concatenation laws for segmented replacement context replay. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCIndexRepairContexts

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Decoding an append preserves both exact signed context lists and chronological references. -/
theorem y322TCIndexRepairMoves_append (i : Fin 174819)
    (first second : List Y322RawContextEquationMove)
    (h : ∀ move ∈ first ++ second, move.Allowed 48648 (77243 + i.val)) :
    y322TCIndexRepairMoves i (first ++ second) h =
      y322TCIndexRepairMoves i first (fun move hm => h move (List.mem_append_left _ hm)) ++
      y322TCIndexRepairMoves i second (fun move hm => h move (List.mem_append_right _ hm)) := by
  unfold y322TCIndexRepairMoves
  rw [List.pmap_append]

/-- The exact empty raw context list decodes to the empty context list. -/
theorem y322TCIndexRepairMoves_nil (i : Fin 174819)
    (h : ∀ move ∈ ([] : List Y322RawContextEquationMove),
      move.Allowed 48648 (77243 + i.val)) : y322TCIndexRepairMoves i [] h = [] := rfl

/-- Replaying a reduced input gives exactly the same result as the original input. -/
theorem y322TCIndexRepairRun_reduce {alphabet : Type*} [DecidableEq alphabet] {earlier : ℕ}
    (prior : Fin earlier → Y322WordEquation alphabet)
    (moves : List (Y322ContextEquationMove alphabet earlier)) (word : List (alphabet × Bool)) :
    y322ContextEquationRun prior moves (FreeGroup.reduce word) =
      y322ContextEquationRun prior moves word := by
  cases moves with
  | nil => simp only [y322ContextEquationRun, FreeGroup.reduce.idem]
  | cons move rest =>
    simp only [y322ContextEquationRun, y322ContextEquationStep, FreeGroup.reduce.idem]

/-- Exact context replay of an append is the composition of its two checked runs. -/
theorem y322TCIndexRepairRun_append {alphabet : Type*} [DecidableEq alphabet] {earlier : ℕ}
    (prior : Fin earlier → Y322WordEquation alphabet)
    (first second : List (Y322ContextEquationMove alphabet earlier))
    (word : List (alphabet × Bool)) :
    y322ContextEquationRun prior (first ++ second) word =
      (y322ContextEquationRun prior first word).bind (y322ContextEquationRun prior second) := by
  induction first generalizing word with
  | nil =>
    simp only [List.nil_append, y322ContextEquationRun, Option.bind_some]
    exact (y322TCIndexRepairRun_reduce prior second word).symm
  | cons move rest ih =>
    simp only [List.cons_append, y322ContextEquationRun, ih, Option.bind_assoc]

/-- Empty exact context replay performs only the checker's existing free reduction. -/
theorem y322TCIndexRepairRun_nil {alphabet : Type*} [DecidableEq alphabet] {earlier : ℕ}
    (prior : Fin earlier → Y322WordEquation alphabet) (word : List (alphabet × Bool)) :
    y322ContextEquationRun prior [] word = some (FreeGroup.reduce word) := rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
