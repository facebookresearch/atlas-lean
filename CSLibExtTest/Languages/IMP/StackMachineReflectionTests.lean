/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.IMP.StackMachineReflection
import CSLibExtTest.Languages.IMP.HoareExamples
import CSLibExtTest.Languages.IMP.StackMachineTests

/-! # Consumers and boundaries for IMP compiler termination reflection

Named private consumers keep their proof dependencies visible to import and trust audits.
-/

namespace Cslib.IMP.StackMachine.ReflectionTests

open Relation

-- An arbitrary halting machine run, not a run supplied by forward correctness.
private theorem countdown_compiled_valid {a b : Nat} {s s' : State} {stk' : List Nat}
    (hp : s 0 = a ∧ s 1 = b)
    (h : Steps (compile Examples.countdownProg 0) (0, [], s)
      (codeLength Examples.countdownProg, stk', s')) :
    s' 0 = a + b ∧ s' 1 = 0 :=
  valid_iff_compiled.mp (Examples.countdown_valid a b) s s' stk' hp h

private theorem countdown_stack_restored {s s' : State} {stk' : List Nat}
    (h : Steps (compile Tests.stackCountdown 0) (0, [7, 9], s)
      (codeLength Tests.stackCountdown, stk', s')) : stk' = [7, 9] :=
  (bigStep_of_compile_halts h).2

private theorem countdown_terminates (n : Nat) {s : State} (hs : s 0 = n) :
    ∃ s', BigStep Tests.stackCountdown s s' ∧ s' 0 = 0 := by
  induction n generalizing s with
  | zero =>
      refine ⟨s, BigStep.whileFalse ?_, hs⟩
      simp [BExp.eval, AExp.eval, hs]
  | succ n ih =>
      let t := Function.update s 0 (s 0 - 1)
      obtain ⟨s', hb, hz⟩ := ih (s := t) (by simp [t, hs])
      refine ⟨s', BigStep.whileTrue ?_ ?_ hb, hz⟩
      · simp [BExp.eval, AExp.eval, hs]
      · exact BigStep.assign s 0 (.sub (.var 0) (.const 1))

-- Nonvacuity: a loop with two iterations really halts, changes the state,
-- and the iff relates that same final state with a nonempty restored stack.
private theorem countdown_changes_state {s : State} (hs : s 0 = 2) :
    ∃ s', Steps (compile Tests.stackCountdown 0) (0, [7, 9], s)
      (codeLength Tests.stackCountdown, [7, 9], s') ∧
      BigStep Tests.stackCountdown s s' ∧ s' 0 = 0 ∧ s' ≠ s := by
  obtain ⟨s', hb, hz⟩ := countdown_terminates 2 hs
  refine ⟨s', compile_run_iff.mpr ⟨hb, rfl⟩, hb, hz, ?_⟩
  intro heq
  subst s'
  omega

-- Empty code is a genuine zero-step boundary, not a positive-length assumption.
private theorem skip_run_iff {s s' : State} {stk stk' : List Nat} :
    Steps (compile .skip 0) (0, stk, s) (0, stk', s') ↔
      s' = s ∧ stk' = stk := by
  simpa [codeLength] using (compile_run_iff (c := .skip) (s := s) (s' := s')
    (stk := stk) (stk' := stk'))

-- Empty branches and both Boolean outcomes exercise the branch endpoint layout.
private theorem empty_branches_halt (b : Bool) (s : State) :
    Steps (compile (.ite (.truth b) .skip .skip) 0) (0, [5], s)
      (codeLength (.ite (.truth b) .skip .skip), [5], s) := by
  apply compile_run_iff.mpr
  refine ⟨?_, rfl⟩
  cases b
  · exact .iteFalse rfl (.skip s)
  · exact .iteTrue rfl (.skip s)

-- A nonzero segment entry and an arbitrary prefix are allowed. The suffix can
-- jump back, but the two-step confined run stops before that reentry step.
private theorem nonzero_segment_reflects (s : State) :
    ∃ s', BigStep (.assign 3 (.const 12)) s s' ∧
      (3, [8], Function.update s 3 12) = (3, [8], s') := by
  let prog := [Instr.add] ++ compile (.assign 3 (.const 12)) 1 ++ [Instr.jump 1]
  have h₁ : SegStep prog 1 3 (1, [8], s) (2, [12, 8], s) :=
    ⟨.push rfl, by omega, by omega⟩
  have h₂ : SegStep prog 1 3 (2, [12, 8], s)
      (3, [8], Function.update s 3 12) := ⟨.store rfl, by omega, by omega⟩
  exact bigStep_of_segRun (before := [Instr.add]) (after := [Instr.jump 1])
    ((RelatesInSteps.single h₁).trans (.single h₂)) rfl

private theorem true_loop_no_bigStep {s s' : State} :
    ¬ BigStep (.while (.truth true) .skip) s s' := by
  intro h
  generalize heq : Cmd.while (.truth true) .skip = c at h
  induction h with
  | skip => cases heq
  | assign => cases heq
  | seq => cases heq
  | iteTrue => cases heq
  | iteFalse => cases heq
  | whileFalse hg =>
      cases heq
      simp at hg
  | whileTrue _ _ _ _ ih =>
      cases heq
      exact ih rfl

-- Non-halting is proved; existence of an infinite execution is NOT claimed.
private theorem true_loop_never_halts (s : State) (stk : List Nat) :
    ¬ ∃ stk' s', Steps (compile (.while (.truth true) .skip) 0) (0, stk, s)
      (codeLength (.while (.truth true) .skip), stk', s') := by
  rw [compile_halts_iff]
  rintro ⟨s', h⟩
  exact true_loop_no_bigStep h

private def increment : Cmd := .assign 0 (.add (.var 0) (.const 1))
private def reentryProgram : List Instr := compile increment 0 ++ [.jump 0]

private theorem increment_four_steps (s : State) :
    RelatesInSteps (Step reentryProgram) (0, [], s)
      (4, [], Function.update s 0 (s 0 + 1)) 4 := by
  have h1 : Step reentryProgram (0, [], s) (1, [s 0], s) := .load rfl
  have h2 : Step reentryProgram (1, [s 0], s) (2, [1, s 0], s) := .push rfl
  have h3 : Step reentryProgram (2, [1, s 0], s) (3, [s 0 + 1], s) := .add rfl
  have h4 : Step reentryProgram (3, [s 0 + 1], s)
      (4, [], Function.update s 0 (s 0 + 1)) := .store rfl
  exact ((RelatesInSteps.single h1).trans (.single h2)).trans
    ((RelatesInSteps.single h3).trans (.single h4))

-- Nine actual instructions reach the segment end for the second time. An
-- unrestricted segment-reflection statement would wrongly equate 2 with 1.
private theorem context_reentry_counterexample :
    ∃ s', RelatesInSteps (Step reentryProgram) (0, [], fun _ => 0)
      (codeLength increment, [], s') 9 ∧ s' 0 = 2 ∧
      ¬ BigStep increment (fun _ => 0) s' := by
  let s₀ : State := fun _ => 0
  let s₁ := Function.update s₀ 0 (s₀ 0 + 1)
  let s₂ := Function.update s₁ 0 (s₁ 0 + 1)
  have hj : Step reentryProgram (4, [], s₁) (0, [], s₁) := .jump rfl
  refine ⟨s₂, (increment_four_steps s₀).trans
    ((RelatesInSteps.single hj).trans (increment_four_steps s₁)), ?_, ?_⟩
  · simp [s₂, s₁, s₀]
  · intro hb
    have heq := BigStep.assign_iff.mp hb
    have hvalue := congrArg (fun s : State => s 0) heq
    simp [s₂, s₁, s₀, AExp.eval] at hvalue

-- The reentry transition is exactly the step excluded by SegStep.
private theorem reentry_not_confined (s : State) :
    ¬ SegStep reentryProgram 0 (codeLength increment) (4, [], s) (0, [], s) := by
  intro h
  simpa [increment, codeLength, alen] using h.2.2

-- Not compiled code: it is stuck before its end, not halted. Reflection does
-- not imply progress and does not turn stuckness into infinite execution.
private theorem noncompiled_add_stuck (s : State) :
    (∀ y, ¬ Step [Instr.add] (0, [], s) y) ∧
      (0 : Nat) ≠ ([Instr.add] : List Instr).length := by
  constructor
  · intro y h
    cases h <;> simp_all
  · decide

/-! ## Witnessed consumers of reachable progress -/

private theorem normal_halt (c : Cmd) (stk : List Nat) (s : State) :
    Relation.Normal (Step (compile c 0)) (codeLength c, stk, s) := by
  rintro ⟨w, hw⟩
  exact no_step_of_length_le (by simp [compile_length]) w hw

private theorem progress_before_end {c : Cmd} {s : State} {stk : List Nat} {z : Config}
    (hr : Steps (compile c 0) (0, stk, s) z) (hne : z.1 ≠ codeLength c) :
    z.1 < codeLength c ∧ ∃ w, Step (compile c 0) z w := by
  rcases compile_reachable_cases hr with ⟨s', _, heq⟩ | hs
  · exact (hne (congrArg Prod.fst heq)).elim
  · exact hs

-- A concrete starting state, actual terminating run, and actual normal endpoint.
private theorem countdown_normal_witness :
    let s : State := fun x => if x = 0 then 2 else 0
    ∃ z, Steps (compile Tests.stackCountdown 0) (0, [7, 9], s) z ∧
      Relation.Normal (Step (compile Tests.stackCountdown 0)) z ∧
      ∃ s', BigStep Tests.stackCountdown s s' ∧
        z = (codeLength Tests.stackCountdown, [7, 9], s') ∧ s' 0 = 0 := by
  dsimp only
  obtain ⟨fin, hb, hz⟩ := countdown_terminates 2 (s := fun x => if x = 0 then 2 else 0)
    (by simp)
  have hr := (compile_run_iff (stk := [7, 9])).mpr ⟨hb, rfl⟩
  have hn := normal_halt Tests.stackCountdown [7, 9] fin
  refine ⟨_, hr, hn, ?_⟩
  obtain ⟨s', hb', heq⟩ := compile_reachable_normal hr hn
  refine ⟨s', hb', heq, ?_⟩
  rw [BigStep.deterministic hb' hb]
  exact hz

-- Unlike the planner's random generator, this actual machine fixture uses mul.
private theorem multiplication_midrun (s : State) :
    let c := Cmd.assign 0 (.mul (.const 2) (.const 3))
    Steps (compile c 0) (0, [11], s) (2, [3, 2, 11], s) ∧
      2 < codeLength c ∧ Step (compile c 0) (2, [3, 2, 11], s) (3, [6, 11], s) := by
  dsimp only
  let c := Cmd.assign 0 (.mul (.const 2) (.const 3))
  have h₁ : Step (compile c 0) (0, [11], s) (1, [2, 11], s) := .push rfl
  have h₂ : Step (compile c 0) (1, [2, 11], s) (2, [3, 2, 11], s) := .push rfl
  have hr := (ReflTransGen.single h₁).trans (.single h₂)
  obtain ⟨hlt, w, hw⟩ := progress_before_end hr (by simp [c, codeLength, alen])
  have hexact : Step (compile c 0) (2, [3, 2, 11], s) (3, [6, 11], s) := .mul rfl
  exact ⟨hr, hlt, (Step.deterministic hw hexact) ▸ hw⟩

private theorem skip_normal_progress (s : State) :
    Relation.Normal (Step (compile .skip 0)) (0, [9], s) ∧
      ∃ s', BigStep .skip s s' ∧ (0, [9], s) = (codeLength .skip, [9], s') := by
  have hr : Steps (compile .skip 0) (0, [9], s) (0, [9], s) := .refl
  have hn := normal_halt .skip [9] s
  exact ⟨hn, compile_reachable_normal hr hn⟩

-- For both Boolean outcomes the guard endpoint is reachable and enabled.
private theorem branch_guard_progress (b : Bool) (s : State) :
    let c := Cmd.ite (.truth b) .skip .skip
    Steps (compile c 0) (0, [7], s) (1, cond b 1 0 :: [7], s) ∧
      1 < codeLength c ∧ ∃ w, Step (compile c 0) (1, cond b 1 0 :: [7], s) w := by
  dsimp only
  have hs : Step (compile (.ite (.truth b) .skip .skip) 0)
      (0, [7], s) (1, cond b 1 0 :: [7], s) := .push rfl
  have hr := ReflTransGen.single hs
  exact ⟨hr, progress_before_end hr (by simp [codeLength, blen])⟩

private theorem true_empty_branch_boundary (s : State) :
    let c := Cmd.ite (.truth true) .skip .skip
    Steps (compile c 0) (0, [7], s) (2, [7], s) ∧
      2 < codeLength c ∧ Step (compile c 0) (2, [7], s) (3, [7], s) := by
  dsimp only
  let c := Cmd.ite (.truth true) .skip .skip
  have h₁ : Step (compile c 0) (0, [7], s) (1, [1, 7], s) := .push rfl
  have h₂ : Step (compile c 0) (1, [1, 7], s) (2, [7], s) := .jumpIfZeroSucc rfl
  have hr := (ReflTransGen.single h₁).trans (.single h₂)
  obtain ⟨hlt, w, hw⟩ := progress_before_end hr (by simp [c, codeLength, blen])
  have hexact : Step (compile c 0) (2, [7], s) (3, [7], s) := .jump rfl
  exact ⟨hr, hlt, (Step.deterministic hw hexact) ▸ hw⟩

private theorem false_empty_branch_normal (s : State) :
    let c := Cmd.ite (.truth false) .skip .skip
    Steps (compile c 0) (0, [7], s) (3, [7], s) ∧
      Relation.Normal (Step (compile c 0)) (3, [7], s) ∧
      ∃ s', BigStep c s s' ∧ (3, [7], s) = (codeLength c, [7], s') := by
  dsimp only
  let c := Cmd.ite (.truth false) .skip .skip
  have hr : Steps (compile c 0) (0, [7], s) (3, [7], s) :=
    compile_run_iff.mpr ⟨.iteFalse rfl (.skip s), rfl⟩
  have hn := normal_halt c [7] s
  exact ⟨hr, hn, compile_reachable_normal hr hn⟩

private theorem sequence_boundary_progress (s : State) :
    let c := Cmd.seq (.assign 0 (.const 4)) (.assign 1 (.const 5))
    let t := Function.update s 0 4
    Steps (compile c 0) (0, [8], s) (2, [8], t) ∧
      2 < codeLength c ∧ Step (compile c 0) (2, [8], t) (3, [5, 8], t) := by
  dsimp only
  let c := Cmd.seq (.assign 0 (.const 4)) (.assign 1 (.const 5))
  have hr : Steps (compile c 0) (0, [8], s) (2, [8], Function.update s 0 4) := by
    simpa [c, compile, compileA, codeLength, alen] using
      (compile_runs (BigStep.assign s 0 (.const 4)) (before := [])
        (after := compile (.assign 1 (.const 5)) 2) (stack := [8]))
  obtain ⟨hlt, w, hw⟩ := progress_before_end hr (by simp [c, codeLength, alen])
  have hexact : Step (compile c 0) (2, [8], Function.update s 0 4)
      (3, [5, 8], Function.update s 0 4) := .push rfl
  exact ⟨hr, hlt, (Step.deterministic hw hexact) ▸ hw⟩

private theorem false_loop_normal (s : State) :
    let c := Cmd.while (.truth false) .skip
    Steps (compile c 0) (0, [6], s) (3, [6], s) ∧
      Relation.Normal (Step (compile c 0)) (3, [6], s) ∧
      ∃ s', BigStep c s s' ∧ (3, [6], s) = (codeLength c, [6], s') := by
  dsimp only
  let c := Cmd.while (.truth false) .skip
  have hr : Steps (compile c 0) (0, [6], s) (3, [6], s) :=
    compile_run_iff.mpr ⟨.whileFalse rfl, rfl⟩
  have hn := normal_halt c [6] s
  exact ⟨hr, hn, compile_reachable_normal hr hn⟩

-- Every reachable configuration is enabled, but no infinite trace is claimed here.
private theorem true_loop_always_enabled {s : State} {stk : List Nat} {z : Config}
    (hr : Steps (compile (.while (.truth true) .skip) 0) (0, stk, s) z) :
    z.1 ≠ codeLength (.while (.truth true) .skip) ∧
      ∃ w, Step (compile (.while (.truth true) .skip) 0) z w := by
  have hne : z.1 ≠ codeLength (.while (.truth true) .skip) := by
    rcases z with ⟨pc, stk', s'⟩
    intro heq
    change pc = codeLength (.while (.truth true) .skip) at heq
    subst pc
    exact true_loop_never_halts s stk ⟨stk', s', hr⟩
  exact ⟨hne, (compile_progress hr).resolve_left hne⟩

private theorem true_loop_backedge (s : State) :
    let c := Cmd.while (.truth true) .skip
    Steps (compile c 0) (0, [6], s) (2, [6], s) ∧
      Step (compile c 0) (2, [6], s) (0, [6], s) := by
  dsimp only
  let c := Cmd.while (.truth true) .skip
  have h₁ : Step (compile c 0) (0, [6], s) (1, [1, 6], s) := .push rfl
  have h₂ : Step (compile c 0) (1, [1, 6], s) (2, [6], s) := .jumpIfZeroSucc rfl
  have hr := (ReflTransGen.single h₁).trans (.single h₂)
  obtain ⟨_, w, hw⟩ := true_loop_always_enabled hr
  have hexact : Step (compile c 0) (2, [6], s) (0, [6], s) := .jump rfl
  exact ⟨hr, (Step.deterministic hw hexact) ▸ hw⟩

-- Progress refutes interpreting an arbitrary stuck add as compiled source code.
private theorem stuck_add_not_compiled (s : State) :
    ¬ ∃ c, compile c 0 = [Instr.add] := by
  rintro ⟨c, hc⟩
  have hr : Steps (compile c 0) (0, [], s) (0, [], s) := .refl
  rcases compile_progress hr with hhalt | ⟨w, hw⟩
  · have hlen := compile_length c 0
    rw [hc] at hlen
    simp only [List.length_cons, List.length_nil] at hlen
    change 0 = codeLength c at hhalt
    omega
  · rw [hc] at hw
    exact (noncompiled_add_stuck s).1 w hw

-- A suffix push is enabled at the segment end, then reaches the outer end.
-- Thus normality for arbitrary surrounding code is not the standalone theorem.
private theorem suffix_boundary (s : State) :
    let c := Cmd.assign 0 (.const 5)
    let t := Function.update s 0 5
    let prog := compile c 0 ++ [Instr.push 7]
    (∃ s', BigStep c s s' ∧ (2, [9], t) = (codeLength c, [9], s')) ∧
      Steps prog (0, [9], s) (3, [7, 9], t) ∧
      Relation.Normal (Step prog) (3, [7, 9], t) ∧ 3 ≠ codeLength c := by
  dsimp only
  let c := Cmd.assign 0 (.const 5)
  let t := Function.update s 0 5
  let prog := compile c 0 ++ [Instr.push 7]
  have hstand : Steps (compile c 0) (0, [9], s) (2, [9], t) :=
    compile_run_iff.mpr ⟨.assign s 0 (.const 5), rfl⟩
  have hsource := compile_reachable_normal hstand (normal_halt c [9] t)
  have hr : Steps prog (0, [9], s) (2, [9], t) := by
    simpa [prog, c, t, codeLength, alen] using
      (compile_runs (BigStep.assign s 0 (.const 5)) (before := [])
        (after := [Instr.push 7]) (stack := [9]))
  have hs : Step prog (2, [9], t) (3, [7, 9], t) := .push rfl
  refine ⟨hsource, hr.trans (.single hs), ?_, by simp [codeLength, alen]⟩
  rintro ⟨w, hw⟩
  exact no_step_of_length_le (by simp [compile, compileA]) w hw

#print axioms Cslib.IMP.StackMachine.compile_reachable_cases
#print axioms Cslib.IMP.StackMachine.compile_progress
#print axioms Cslib.IMP.StackMachine.compile_reachable_normal

#print axioms Cslib.IMP.StackMachine.bigStep_of_segRun
#print axioms Cslib.IMP.StackMachine.bigStep_of_compile_halts
#print axioms Cslib.IMP.StackMachine.compile_run_iff
#print axioms Cslib.IMP.StackMachine.compile_correct_iff
#print axioms Cslib.IMP.StackMachine.compile_halts_iff
#print axioms Cslib.IMP.StackMachine.valid_iff_compiled

end Cslib.IMP.StackMachine.ReflectionTests
