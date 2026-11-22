/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.IMP.StackMachineReflection
public import CSLibExt.Languages.IMP.Equivalence
public import Cslib.Foundations.Relation.Termination

/-!
# Infinite executions of the IMP compiler

The source admits an infinite small-step execution exactly when its standalone
compiled program admits an infinite machine execution, for any original stack.
An execution is an actual Nat-indexed chain from the specified initial configuration.
Canonical `Relation.SN` connects these chains to the absence of a source big-step
execution. Compiled progress is essential: arbitrary machine code could be stuck
without halting, whereas a reachable normal compiled configuration is a source result.

This is an equivalence of existence, not a lockstep simulation or a correspondence
between particular traces. It makes no claim about step counts, events, fairness,
arbitrary surrounding code, costs, or TimeM.
-/

@[expose] public section

-- Determinism makes a reachable normal form exclude every infinite alternative.
private theorem sn_of_reflTransGen_normal {α : Type*} {r : α → α → Prop}
    (hdet : Relator.RightUnique r) {x y : α}
    (hxy : Relation.ReflTransGen r x y) (hy : Relation.Normal r y) : Relation.SN r x := by
  induction hxy using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.SN.of_normal hy
  | head hs _ ih =>
      apply Relation.SN.intro
      intro z hz
      exact (hdet hs hz) ▸ ih

namespace Cslib.IMP

private theorem sn_step_iff_exists_bigStep {c : Cmd} {s : State} :
    Relation.SN Step (c, s) ↔ ∃ s', BigStep c s s' := by
  constructor
  · intro hsn
    obtain ⟨⟨c', s'⟩, hr, hn⟩ := hsn.normalizable
    have hc : c' = .skip := Step.terminal_iff.mp (fun z hz => hn ⟨z, hz⟩)
    subst c'
    exact ⟨s', BigStep.of_terminates hr⟩
  · rintro ⟨s', hb⟩
    apply sn_of_reflTransGen_normal (r := Step) (fun _ _ _ hs ht => Step.deterministic hs ht)
      (Terminates.of_bigStep hb)
    rintro ⟨z, hz⟩
    exact Step.skip_not_step hz

/-- Infinite source executions are exactly the commands with no big-step result. -/
theorem exists_infinite_step_iff {c : Cmd} {s : State} :
    (∃ g : ℕ → Config, g 0 = (c, s) ∧ ∀ n, Step (g n) (g (n + 1))) ↔
      ∀ s', ¬ BigStep c s s' := by
  have hchain : ¬ Relation.SN Step (c, s) ↔
      ∃ g : ℕ → Config, g 0 = (c, s) ∧ ∀ n, Step (g n) (g (n + 1)) :=
    not_acc_iff_exists_descending_chain
  exact hchain.symm.trans (by rw [sn_step_iff_exists_bigStep, not_exists])

namespace StackMachine

private theorem compile_sn_iff_exists_bigStep {c : Cmd} {s : State} {stk : List Nat} :
    Relation.SN (Step (compile c 0)) (0, stk, s) ↔ ∃ s', BigStep c s s' := by
  constructor
  · intro hsn
    obtain ⟨z, hr, hn⟩ := hsn.normalizable
    obtain ⟨s', hb, _⟩ := compile_reachable_normal hr hn
    exact ⟨s', hb⟩
  · rintro ⟨s', hb⟩
    have hr : Steps (compile c 0) (0, stk, s) (codeLength c, stk, s') := by
      simpa using (compile_runs hb (before := []) (after := []) (stack := stk))
    apply sn_of_reflTransGen_normal (r := Step (compile c 0))
      (fun _ _ _ hs ht => Step.deterministic hs ht) hr
    rintro ⟨z, hz⟩
    exact no_step_of_length_le (by simp [compile_length]) z hz

/-- Infinite compiled executions are exactly the commands with no source big-step result.
The program is standalone compiled code; non-halting arbitrary code might instead be stuck. -/
theorem exists_infinite_run_iff {c : Cmd} {s : State} {stk : List Nat} :
    (∃ f : ℕ → Config, f 0 = (0, stk, s) ∧
      ∀ n, Step (compile c 0) (f n) (f (n + 1))) ↔ ∀ s', ¬ BigStep c s s' := by
  have hchain : ¬ Relation.SN (Step (compile c 0)) (0, stk, s) ↔
      ∃ f : ℕ → Config, f 0 = (0, stk, s) ∧
        ∀ n, Step (compile c 0) (f n) (f (n + 1)) :=
    not_acc_iff_exists_descending_chain
  exact hchain.symm.trans (by rw [compile_sn_iff_exists_bigStep, not_exists])

/-- The compiler preserves and reflects existence of infinite executions, for every
initial stack. This compares actual source and machine chains from their exact starts. -/
theorem compile_infinite_iff {c : Cmd} {s : State} {stk : List Nat} :
    (∃ g : ℕ → Cslib.IMP.Config, g 0 = (c, s) ∧
      ∀ n, Cslib.IMP.Step (g n) (g (n + 1))) ↔
    (∃ f : ℕ → Config, f 0 = (0, stk, s) ∧
      ∀ n, Step (compile c 0) (f n) (f (n + 1))) :=
  Cslib.IMP.exists_infinite_step_iff.trans exists_infinite_run_iff.symm

/-- The infinite-execution equivalence expressed through canonical strong normalization. -/
theorem compile_not_sn_iff_source {c : Cmd} {s : State} {stk : List Nat} :
    ¬ Relation.SN Cslib.IMP.Step (c, s) ↔
      ¬ Relation.SN (Step (compile c 0)) (0, stk, s) := by
  rw [sn_step_iff_exists_bigStep, compile_sn_iff_exists_bigStep]

end StackMachine
end Cslib.IMP
