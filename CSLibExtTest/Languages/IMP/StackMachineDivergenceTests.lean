/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.IMP.StackMachineDivergence

/-! # Explicit infinite chains and boundaries for compiled IMP

Cycles below are constructed from actual transition constructors, independently
of the equivalence under test. All consumers are named private declarations.
-/

namespace Cslib.IMP.StackMachine.DivergenceTests

private def spin : Cmd := .while (.truth true) .skip

private def cycle3 {α : Type*} (a b c : α) (n : Nat) : α :=
  match n % 3 with
  | 0 => a
  | 1 => b
  | _ => c

private theorem cycle3_steps {α : Type*} {r : α → α → Prop} {a b c : α}
    (hab : r a b) (hbc : r b c) (hca : r c a) :
    ∀ n, r (cycle3 a b c n) (cycle3 a b c (n + 1)) := by
  intro n
  have hlt : n % 3 < 3 := Nat.mod_lt n (by omega)
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h0 | h1 | h2
  · have hn : (n + 1) % 3 = 1 := by omega
    simpa [cycle3, h0, hn] using hab
  · have hn : (n + 1) % 3 = 2 := by omega
    simpa [cycle3, h1, hn] using hbc
  · have hn : (n + 1) % 3 = 0 := by omega
    simpa [cycle3, h2, hn] using hca

-- while true skip unfolds, takes the true branch, then removes the leading skip.
private theorem spin_source_chain (s : State) :
    ∃ g : ℕ → Cslib.IMP.Config, g 0 = (spin, s) ∧
      ∀ n, Cslib.IMP.Step (g n) (g (n + 1)) := by
  refine ⟨cycle3 (spin, s) (.ite (.truth true) (.seq .skip spin) .skip, s)
    (.seq .skip spin, s), rfl, ?_⟩
  exact cycle3_steps (Cslib.IMP.Step.whileStep (.truth true) .skip s)
    (Cslib.IMP.Step.iteTrue rfl) (Cslib.IMP.Step.seqSkip spin s)

-- The concrete compiled cycle restores ANY stack, without using a divergence theorem.
private theorem spin_machine_chain (s : State) (stk : List Nat) :
    ∃ f : ℕ → Config, f 0 = (0, stk, s) ∧
      ∀ n, Step (compile spin 0) (f n) (f (n + 1)) := by
  refine ⟨cycle3 (0, stk, s) (1, 1 :: stk, s) (2, stk, s), rfl, ?_⟩
  exact cycle3_steps (Step.push rfl) (Step.jumpIfZeroSucc rfl) (Step.jump rfl)

private theorem spin_no_bigStep_from_source (s : State) :
    ∀ s', ¬ BigStep spin s s' :=
  Cslib.IMP.exists_infinite_step_iff.mp (spin_source_chain s)

private theorem spin_no_bigStep_from_machine (s : State) :
    ∀ s', ¬ BigStep spin s s' :=
  exists_infinite_run_iff.mp (spin_machine_chain s [7, 9])

-- Supply an independently constructed source chain to the forward headline.
private theorem spin_transport_to_machine (s : State) (stk : List Nat) :
    ∃ f : ℕ → Config, f 0 = (0, stk, s) ∧
      (∀ n, Step (compile spin 0) (f n) (f (n + 1))) ∧ f 1 = (1, 1 :: stk, s) := by
  obtain ⟨f, h0, hs⟩ := (compile_infinite_iff (stk := stk)).mp (spin_source_chain s)
  refine ⟨f, h0, hs, ?_⟩
  have hfirst : Step (compile spin 0) (0, stk, s) (f 1) := by
    simpa only [h0] using hs 0
  exact Step.deterministic hfirst (Step.push rfl)

-- Supply an independently constructed machine chain to the reverse headline.
private theorem spin_transport_to_source (s : State) :
    ∃ g : ℕ → Cslib.IMP.Config, g 0 = (spin, s) ∧
      (∀ n, Cslib.IMP.Step (g n) (g (n + 1))) ∧
      g 1 = (.ite (.truth true) (.seq .skip spin) .skip, s) := by
  obtain ⟨g, h0, hs⟩ := compile_infinite_iff.mpr (spin_machine_chain s [7, 9])
  refine ⟨g, h0, hs, ?_⟩
  have hfirst : Cslib.IMP.Step (spin, s) (g 1) := by
    simpa only [h0] using hs 0
  exact Cslib.IMP.Step.deterministic hfirst
    (Cslib.IMP.Step.whileStep (.truth true) .skip s)

private theorem spin_not_sn_bridge (s : State) (stk : List Nat) :
    ¬ Relation.SN Cslib.IMP.Step (spin, s) ∧
      ¬ Relation.SN (Step (compile spin 0)) (0, stk, s) := by
  have hsource : ¬ Relation.SN Cslib.IMP.Step (spin, s) :=
    (not_acc_iff_exists_descending_chain
      (r := fun a b => Cslib.IMP.Step b a)).mpr (spin_source_chain s)
  have hmachine : ¬ Relation.SN (Step (compile spin 0)) (0, stk, s) :=
    (not_acc_iff_exists_descending_chain
      (r := fun a b => Step (compile spin 0) b a)).mpr (spin_machine_chain s stk)
  exact ⟨compile_not_sn_iff_source.mpr hmachine,
    (compile_not_sn_iff_source (stk := stk)).mp hsource⟩

private theorem spin_stack_boundaries (s : State) :
    (∃ f : ℕ → Config, f 0 = (0, [], s) ∧
      ∀ n, Step (compile spin 0) (f n) (f (n + 1))) ∧
    (∃ f : ℕ → Config, f 0 = (0, [7, 9], s) ∧
      ∀ n, Step (compile spin 0) (f n) (f (n + 1))) :=
  ⟨spin_machine_chain s [], spin_machine_chain s [7, 9]⟩

private theorem skip_no_chain_direct (s : State) (stk : List Nat) :
    Relation.SN (Step (compile .skip 0)) (0, stk, s) ∧
      ¬ ∃ f : ℕ → Config, f 0 = (0, stk, s) ∧
        ∀ n, Step (compile .skip 0) (f n) (f (n + 1)) := by
  have hn : Relation.Normal (Step (compile .skip 0)) (0, stk, s) := by
    rintro ⟨z, hz⟩
    exact no_step_of_length_le (by simp [compile]) z hz
  have hsn := Relation.SN.of_normal hn
  refine ⟨hsn, ?_⟩
  intro hchain
  exact ((not_acc_iff_exists_descending_chain
    (r := fun a b => Step (compile .skip 0) b a)).mpr hchain) hsn

private theorem skip_no_chain_via_bridge (s : State) (stk : List Nat) :
    (¬ ∃ g : ℕ → Cslib.IMP.Config, g 0 = (.skip, s) ∧
      ∀ n, Cslib.IMP.Step (g n) (g (n + 1))) ∧
    (¬ ∃ f : ℕ → Config, f 0 = (0, stk, s) ∧
      ∀ n, Step (compile .skip 0) (f n) (f (n + 1))) := by
  have hsource : ¬ ∃ g : ℕ → Cslib.IMP.Config, g 0 = (.skip, s) ∧
      ∀ n, Cslib.IMP.Step (g n) (g (n + 1)) := by
    intro hchain
    exact (Cslib.IMP.exists_infinite_step_iff.mp hchain) s (.skip s)
  exact ⟨hsource, fun hchain => hsource (compile_infinite_iff.mpr hchain)⟩

-- The terminating example changes the actual initial state and uses a nonempty stack.
private theorem assignment_changes_state_no_chain :
    let s : State := fun _ => 0
    ∃ t, BigStep (.assign 0 (.const 5)) s t ∧ t 0 = 5 ∧ t ≠ s ∧
      ¬ ∃ f : ℕ → Config, f 0 = (0, [7, 9], s) ∧
        ∀ n, Step (compile (.assign 0 (.const 5)) 0) (f n) (f (n + 1)) := by
  dsimp only
  let s : State := fun _ => 0
  let t := Function.update s 0 5
  have hb : BigStep (.assign 0 (.const 5)) s t := .assign s 0 (.const 5)
  refine ⟨t, hb, by simp [t], ?_, ?_⟩
  · intro heq
    have hvalue := congrArg (fun u : State => u 0) heq
    simp [s, t] at hvalue
  · intro hchain
    exact (exists_infinite_run_iff.mp hchain) t hb

private theorem false_loop_terminates_no_chain (s : State) (stk : List Nat) :
    BigStep (.while (.truth false) .skip) s s ∧
    (¬ ∃ g : ℕ → Cslib.IMP.Config, g 0 = (.while (.truth false) .skip, s) ∧
      ∀ n, Cslib.IMP.Step (g n) (g (n + 1))) ∧
    (¬ ∃ f : ℕ → Config, f 0 = (0, stk, s) ∧
      ∀ n, Step (compile (.while (.truth false) .skip) 0) (f n) (f (n + 1))) := by
  have hb : BigStep (.while (.truth false) .skip) s s := .whileFalse rfl
  exact ⟨hb, fun h => (Cslib.IMP.exists_infinite_step_iff.mp h) s hb,
    fun h => (exists_infinite_run_iff.mp h) s hb⟩

-- Noncompiled code is stuck before the end: non-halting does not imply divergence.
private theorem add_stuck_not_divergent (s : State) :
    Relation.Normal (Step [Instr.add]) (0, [], s) ∧
      Relation.SN (Step [Instr.add]) (0, [], s) ∧
      (0 : Nat) ≠ ([Instr.add] : List Instr).length ∧
      ¬ ∃ f : ℕ → Config, f 0 = (0, [], s) ∧
        ∀ n, Step [Instr.add] (f n) (f (n + 1)) := by
  have hn : Relation.Normal (Step [Instr.add]) (0, [], s) := by
    rintro ⟨z, hz⟩
    cases hz <;> simp_all
  have hsn := Relation.SN.of_normal hn
  refine ⟨hn, hsn, by decide, ?_⟩
  intro hchain
  exact ((not_acc_iff_exists_descending_chain
    (r := fun a b => Step [Instr.add] b a)).mpr hchain) hsn

-- A jump in the surrounding code creates an infinite constant chain after empty skip.
private theorem embedded_skip_infinite (s : State) (stk : List Nat) :
    BigStep .skip s s ∧
      ∃ f : ℕ → Config, f 0 = (0, stk, s) ∧
        ∀ n, Step (compile .skip 0 ++ [Instr.jump 0]) (f n) (f (n + 1)) := by
  refine ⟨.skip s, fun _ => (0, stk, s), rfl, ?_⟩
  intro n
  exact Step.jump rfl

-- Normalizability without determinism does not exclude an infinite alternative.
private def fork (a b : Bool) : Prop := a = false ∧ (b = false ∨ b = true)

private theorem nondeterministic_normal_and_infinite :
    Relation.Normalizable fork false ∧
      (∃ f : ℕ → Bool, f 0 = false ∧ ∀ n, fork (f n) (f (n + 1))) ∧
      ¬ Relator.RightUnique fork := by
  have hstop : fork false true := ⟨rfl, Or.inr rfl⟩
  have hloop : fork false false := ⟨rfl, Or.inl rfl⟩
  have hn : Relation.Normal fork true := by
    rintro ⟨b, hb, _⟩
    cases hb
  refine ⟨⟨true, .single hstop, hn⟩, ⟨fun _ => false, rfl, fun _ => hloop⟩, ?_⟩
  intro hdet
  have hbad : false = true := hdet hloop hstop
  cases hbad

#print axioms Cslib.IMP.exists_infinite_step_iff
#print axioms Cslib.IMP.StackMachine.exists_infinite_run_iff
#print axioms Cslib.IMP.StackMachine.compile_infinite_iff
#print axioms Cslib.IMP.StackMachine.compile_not_sn_iff_source

end Cslib.IMP.StackMachine.DivergenceTests
