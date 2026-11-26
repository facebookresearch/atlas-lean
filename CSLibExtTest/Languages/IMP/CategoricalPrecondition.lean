/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import CSLibExt.Languages.IMP.CategoricalPrecondition

open CategoryTheory PowersetVerification
namespace Cslib.IMP.CategoricalPreconditionTests
open CategoricalHoare

example (c : Cmd) (Q : Assertion) :
    liberalPre (commandRel c) {s | Q s} = {s | wlp c Q s} := liberalPre_commandRel c Q

example (b : BExp) (c : Cmd) (Q : Assertion) :
    {s | wlp (.while b c) Q s} = (whileStep b c Q).gfp := wlp_while_eq_gfp b c Q

-- Backward reasoning computes an exact, nontrivial assignment precondition.
example : liberalPre (commandRel (.assign 0 (.add (.var 0) (.const 1))))
    {s | s 0 = 5} = {s | s 0 = 4} := by
  rw [liberalPre_commandRel, wlp.assign]
  ext s
  simp [Assertion.subst, AExp.eval, Function.update]

-- Composition passes the intermediate assertion backward through both assignments.
example : liberalPre (commandRel (.seq (.assign 0 (.add (.var 0) (.const 1)))
    (.assign 0 (.add (.var 0) (.const 2))))) {s | s 0 = 7} = {s | s 0 = 4} := by
  rw [commandRel_seq, liberalPre_comp]
  change liberalPre (commandRel _) (liberalPre (commandRel _) _) = _
  rw [liberalPre_commandRel, liberalPre_commandRel, wlp.assign, wlp.assign]
  ext s
  simp [Assertion.subst, AExp.eval, Function.update]

-- The guard selects different final values, so the desired value determines the input branch.
example : liberalPre (commandRel (.ite (.le (.var 0) (.const 3))
    (.assign 1 (.const 1)) (.assign 1 (.const 2)))) {s | s 1 = 1} =
    {s | s 0 ≤ 3} := by
  rw [liberalPre_commandRel, wlp.ite, wlp.assign, wlp.assign]
  ext s
  simp only [Assertion.subst, AExp.eval, BExp.eval, Function.update_self]
  simp only [Nat.reduceEqDiff, implies_true, true_and, imp_false, Bool.not_eq_false]
  exact decide_eq_true_iff

private def countdown : Cmd :=
  .while (.le (.const 1) (.var 0)) (.assign 0 (.sub (.var 0) (.const 1)))

-- Coinduction proves every terminating countdown ends at zero, over unbounded states.
private theorem countdown_wlp : ∀ s, wlp countdown (fun t => t 0 = 0) s := by
  have h := while_coinduction (.le (.const 1) (.var 0))
    (.assign 0 (.sub (.var 0) (.const 1))) (fun t => t 0 = 0) Set.univ ?_
  · exact fun s => h (Set.mem_univ s)
  intro s _
  constructor
  · intro hb
    have hn : ¬ 1 ≤ s 0 := by
      intro hle
      have ht : (BExp.le (.const 1) (.var 0)).eval s = true :=
        BExp.eval_le_eq_true.mpr hle
      rw [hb] at ht
      contradiction
    omega
  · intro _ t _
    trivial

example : liberalPre (commandRel countdown) {s | s 0 = 0} = Set.univ := by
  rw [liberalPre_commandRel]
  ext s
  exact ⟨fun _ => trivial, fun _ => countdown_wlp s⟩

-- An actual two-iteration execution prevents a vacuous successful specification.
private theorem countdown_two : ∃ t, BigStep countdown (fun _ => 2) t ∧ t 0 = 0 := by
  let s : State := fun _ => 2
  let m := Function.update s 0 1
  let t := Function.update m 0 0
  refine ⟨t, ?_, by decide⟩
  exact .whileTrue (by decide) (.assign s 0 _)
    (.whileTrue (by decide) (.assign m 0 _) (.whileFalse (by decide)))

example : (fun _ => 2) ∉ liberalPre (commandRel countdown) {s | s 0 = 1} := by
  intro h
  obtain ⟨t, ht, hz⟩ := countdown_two
  have bad : t 0 = 1 := h ht
  omega

example : ¬ IMP.Derivable (fun s => s = (fun _ => 2)) countdown (fun s => s 0 = 1) := by
  rw [derivable_iff_subset_liberalPre]
  intro h
  obtain ⟨t, ht, hz⟩ := countdown_two
  have bad : t 0 = 1 := h rfl ht
  omega

-- A false guard exits immediately: its greatest fixed point is exactly the postcondition.
example (Q : Assertion) : (whileStep (.truth false) .skip Q).gfp = {s | Q s} := by
  rw [← wlp_while_eq_gfp, wlp.whileLoop]
  ext s
  simp [BExp.eval]

private def spin : Cmd := .while (.truth true) .skip

-- A true guard and skip body have every state in the greatest fixed point, even for False.
private theorem spin_wlp : ∀ s, wlp spin (fun _ => False) s := by
  have h := while_coinduction (.truth true) .skip (fun _ => False) Set.univ ?_
  · exact fun s => h (Set.mem_univ s)
  intro s _
  constructor
  · simp [BExp.eval]
  · intro _ t _
    trivial

example : (whileStep (.truth true) .skip (fun _ => False)).gfp = Set.univ := by
  rw [← wlp_while_eq_gfp]
  ext s
  exact ⟨fun _ => trivial, fun _ => spin_wlp s⟩

example : liberalPre (commandRel spin) ∅ = Set.univ := by
  change liberalPre (commandRel spin) {s | (fun _ => False) s} = Set.univ
  rw [liberalPre_commandRel]
  ext s
  exact ⟨fun _ => trivial, fun _ => spin_wlp s⟩

example : ¬ ∃ t, BigStep spin (fun _ => 0) t := by
  rintro ⟨t, ht⟩
  exact spin_wlp _ ht

-- The existing while functional is precisely the categorical one, not a second semantics.
example (b : BExp) (c : Cmd) (Q : Assertion) :
    feedbackStep (loopBody b c) {s | Q s} = whileStep b c Q := feedbackStep_loopBody b c Q

example (b : BExp) (c : Cmd) (Q : Assertion) :
    safeInvariant (loopBody b c) {s | Q s} = {s | wlp (.while b c) Q s} :=
  safeInvariant_loopBody b c Q

#print axioms wlp_while_eq_gfp
#print axioms while_coinduction
end Cslib.IMP.CategoricalPreconditionTests
