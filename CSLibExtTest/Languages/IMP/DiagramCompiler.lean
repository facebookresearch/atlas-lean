/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import CSLibExt.Languages.IMP.DiagramCompiler

/-!
# Structural compilation and proof-transport regressions

These tests distinguish branch orientation, actual terminating executions, proof
transport with explicit source derivations, and partial correctness of divergence.
The worked transfer loop preserves the sum of two variables. Nested-loop probes
exercise feedback inside feedback without adding composite-command atoms.
-/

open CategoryTheory Cslib Cslib.IMP Cslib.IMP.DiagramCompiler
open Cslib.IMP.CategoricalHoare (states)
open scoped MonoidalCategory

namespace Cslib.IMP.DiagramCompilerTests

example (c : Cmd) :
    (compile c).denote interpret SumRelCat.symmetricTrace = CategoricalHoare.commandRel c :=
  denote_compile c

example {P Q : Assertion} {c : Cmd} (h : IMP.Derivable P c Q) :
    TracedHoare.Derivable interpret PowersetVerification.verification
      {s | P s} (compile c) {s | Q s} :=
  transport h

example (c d : Cmd) : compile (.seq c d) = .seq (compile c) (compile d) := rfl

example (b : BExp) (c d : Cmd) : compile (.ite b c d) =
    .seq (.atom (.branch b)) (.seq (.tensor (compile d) (compile c)) (.atom .join)) := rfl

example (b : BExp) (c : Cmd) : compile (.while b c) =
    .feedback (.seq (.atom .join)
      (.seq (.atom (.branch b)) (.tensor (.atom .skip) (compile c)))) := rfl

example (b : BExp) (s : State) :
    (s, Sum.inl s) ∈ (interpret (.branch b)).rel ↔ b.eval s = false := by
  change (_ ∧ s = s) ↔ _
  simp

example (b : BExp) (s : State) :
    (s, Sum.inr s) ∈ (interpret (.branch b)).rel ↔ b.eval s = true := by
  change (_ ∧ s = s) ↔ _
  simp

example (s : State) : (s, s) ∈ ((compile .skip).denote interpret SumRelCat.symmetricTrace).rel :=
  (execution_iff _ _ _).mpr (.skip s)

example (s : State) (x : Nat) (a : AExp) :
    (s, Function.update s x (a.eval s)) ∈
      ((compile (.assign x a)).denote interpret SumRelCat.symmetricTrace).rel :=
  (execution_iff _ _ _).mpr (.assign s x a)

-- Different branches assign different constants: swapping the tensor factors fails these probes.
example (s : State) :
    (s, Function.update s 0 7) ∈
      ((compile (.ite (.truth true) (.assign 0 (.const 7)) (.assign 0 (.const 9)))).denote
        interpret SumRelCat.symmetricTrace).rel :=
  (execution_iff _ _ _).mpr (.iteTrue rfl (.assign s 0 _))

example (s : State) :
    (s, Function.update s 0 9) ∈
      ((compile (.ite (.truth false) (.assign 0 (.const 7)) (.assign 0 (.const 9)))).denote
        interpret SumRelCat.symmetricTrace).rel :=
  (execution_iff _ _ _).mpr (.iteFalse rfl (.assign s 0 _))

-- Transport an explicit conditional derivation, including consequence and both branches.
example : TracedHoare.Derivable interpret PowersetVerification.verification Set.univ
    (compile (.ite (.truth true) (.assign 0 (.const 7)) (.assign 0 (.const 9))))
    {s | s 0 = 7 ∨ s 0 = 9} := by
  apply transport
  apply IMP.Derivable.ite
  · refine .consequence ?_ (.assign _ 0 (.const 7)) (Assertion.entails_refl _)
    intro s _
    simp [Assertion.subst, AExp.eval, Function.update]
  · refine .consequence ?_ (.assign _ 0 (.const 9)) (Assertion.entails_refl _)
    intro s _
    simp [Assertion.subst, AExp.eval, Function.update]

private def transferBody : Cmd :=
  .seq (.assign 1 (.add (.var 1) (.const 1))) (.assign 0 (.sub (.var 0) (.const 1)))

private def transferLoop : Cmd := .while (.le (.const 1) (.var 0)) transferBody

/-- The source proof explicitly uses assignment, sequencing, the invariant rule and consequence. -/
private theorem transfer_source (n : Nat) :
    IMP.Derivable (fun s => s 0 + s 1 = n) transferLoop (fun s => s 0 = 0 ∧ s 1 = n) := by
  refine .consequence (Assertion.entails_refl _) (.whileLoop (invariant :=
    fun s => s 0 + s 1 = n) ?_) ?_
  · refine .consequence ?_ (.seq (.assign _ 1 (.add (.var 1) (.const 1)))
      (.assign _ 0 (.sub (.var 0) (.const 1)))) (Assertion.entails_refl _)
    intro s hs
    have hle := BExp.eval_le_eq_true.mp hs.2
    change 1 ≤ s 0 at hle
    simp [Assertion.subst, AExp.eval, Function.update]
    omega
  · intro s hs
    have hn : ¬ 1 ≤ s 0 := by
      intro hle
      have ht : (BExp.le (.const 1) (.var 0)).eval s = true := BExp.eval_le_eq_true.mpr hle
      rw [hs.2] at ht
      contradiction
    exact ⟨by omega, by omega⟩

example (n : Nat) :
    TracedHoare.Derivable interpret PowersetVerification.verification {s : State | s 0 + s 1 = n}
      (compile transferLoop) {s | s 0 = 0 ∧ s 1 = n} := transport (transfer_source n)

example (s : State) (h : s 0 = 0) :
    (s, s) ∈ ((compile transferLoop).denote interpret SumRelCat.symmetricTrace).rel := by
  apply (execution_iff _ _ _).mpr
  exact .whileFalse (by simp [BExp.eval, AExp.eval, h])

private def initial (n : Nat) : State := Function.update (fun _ => 0) 0 n

-- Two actual loop iterations witness that the invariant example is not vacuous.
example : ∃ t, (initial 2, t) ∈
    ((compile transferLoop).denote interpret SumRelCat.symmetricTrace).rel ∧
    t 0 = 0 ∧ t 1 = 2 := by
  let m₁ := Function.update (initial 2) 1 1
  let s₁ := Function.update m₁ 0 1
  let m₂ := Function.update s₁ 1 2
  let s₂ := Function.update m₂ 0 0
  refine ⟨s₂, (execution_iff _ _ _).mpr ?_, by decide, by decide⟩
  exact .whileTrue (by decide) (.seq (.assign (initial 2) 1 _) (.assign m₁ 0 _))
    (.whileTrue (by decide) (.seq (.assign s₁ 1 _) (.assign m₂ 0 _)) (.whileFalse (by decide)))

private def nested : Cmd := .while (.le (.const 1) (.var 0))
  (.seq (.while (.le (.const 1) (.var 1)) (.assign 1 (.const 0))) (.assign 0 (.const 0)))

example : ∃ t, (Function.update (initial 1) 1 1, t) ∈
    ((compile nested).denote interpret SumRelCat.symmetricTrace).rel ∧ t 0 = 0 ∧ t 1 = 0 := by
  let s := Function.update (initial 1) 1 1
  let m := Function.update s 1 0
  let t := Function.update m 0 0
  refine ⟨t, (execution_iff _ _ _).mpr ?_, by decide, by decide⟩
  exact .whileTrue (by decide)
    (.seq (.whileTrue (by decide) (.assign s 1 _) (.whileFalse (by decide))) (.assign m 0 _))
    (.whileFalse (by decide))

example {P Q : Assertion} {c : Cmd}
    (h : TracedHoare.Derivable interpret PowersetVerification.verification
      {s | P s} (compile c) {s | Q s}) : IMP.Derivable P c Q := reflect h

example (P Q : Assertion) (c : Cmd) : IMP.Derivable P c Q ↔
    TracedHoare.Derivable interpret PowersetVerification.verification
      {s | P s} (compile c) {s | Q s} := DiagramCompiler.derivable_iff P Q c

-- A false specification for a terminating assignment remains unprovable.
example : ¬ TracedHoare.Derivable interpret PowersetVerification.verification Set.univ
    (compile (.assign 0 (.const 7))) {s | s 0 = 9} := by
  intro h
  have hf := (reflect h).sound (initial := fun _ => 0) trivial (.assign _ 0 (.const 7))
  simp [AExp.eval, Function.update] at hf

private def spin : Cmd := .while (.truth true) .skip

private theorem spin_no_run (s t : State) : ¬ BigStep spin s t := by
  intro h
  obtain ⟨n, hn⟩ := Iterates.exists_of_bigStep h
  clear h
  induction hn with
  | exit h => simp at h
  | step _ _ _ ih => exact ih

example (s t : State) :
    (s, t) ∉ ((compile spin).denote interpret SumRelCat.symmetricTrace).rel := by
  rw [execution_iff]
  exact spin_no_run s t

-- The loop rule proves arbitrary postconditions for divergence, without proving termination.
example : TracedHoare.Derivable interpret PowersetVerification.verification Set.univ
    (compile spin) ∅ := by
  apply transport
  refine .consequence (Assertion.entails_refl _) (.whileLoop (invariant := fun _ => True)
    (.consequence (fun _ _ => trivial) (.skip _) (Assertion.entails_refl _))) ?_
  intro s hs
  simp [BExp.eval] at hs

example : ¬ TValid (fun _ => True) spin (fun _ => True) := by
  intro h
  obtain ⟨t, ht, _⟩ := h (s := fun _ => 0) trivial
  exact spin_no_run _ _ ht

#print axioms denote_compile
#print axioms transport
#print axioms reflect

end Cslib.IMP.DiagramCompilerTests
