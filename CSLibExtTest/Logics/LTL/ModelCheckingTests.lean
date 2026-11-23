/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.LTL.DecidableModelChecking

/-!
# Executable and lasso consumers of full-LTL model checking

Kernel-checked Boolean computations exercise the complete state/product/graph
path. A two-state model has both satisfying and violating constant lassos.
A deadlock test pins the deliberately infinite-run, non-serial semantics.
-/

@[expose] public section

namespace Cslib.LTL.ModelCheckingTests

open Automata.NA Automata.ωAcceptor ModelChecking

/-- A one-state model with a real self-loop. -/
def stutter : LTS Unit Unit where
  Tr _ _ _ := True

instance : ∀ s action t, Decidable (stutter.Tr s action t) :=
  fun _ _ _ => isTrue trivial

/-- The sole state is initial. -/
def one : Set Unit := Set.univ

instance : DecidablePred (· ∈ one) := fun _ => isTrue trivial

/-- An infinite atom type with only atom zero true. -/
def labels (_ : Unit) (a : ℕ) : Prop := a = 0

instance : ∀ s a, Decidable (labels s a) :=
  fun _ a => inferInstanceAs (Decidable (a = 0))

example : checkB stutter one labels (.atom 0) = true := by decide

example : checkB stutter one labels (.atom 1) = false := by decide

/-- An initial deadlock has no infinite executions; it is not totalized. -/
def dead : LTS Unit Unit where
  Tr _ _ _ := False

instance : ∀ s action t, Decidable (dead.Tr s action t) := fun _ _ _ => isFalse id

example : checkB dead one labels (.not .top) = true := by decide

example (w : ωSequence Unit) : ¬ IsRun dead one w := by
  rintro ⟨_, actions, hexec⟩
  exact hexec 0

example : Models dead one labels (.not .top) :=
  (checkB_iff dead one labels (.not .top)).mp (by decide)

/-- Two initial self-loops, whose state labels have different truth values. -/
def loops : LTS Bool Unit where
  Tr s _ t := s = t

instance : ∀ s action t, Decidable (loops.Tr s action t) :=
  fun s _ t => inferInstanceAs (Decidable (s = t))

/-- Both loop states are initially possible. -/
def both : Set Bool := Set.univ

instance : DecidablePred (· ∈ both) := fun _ => isTrue trivial

/-- Restrict the same model to its satisfying loop. -/
def positive : Set Bool := {true}

instance : DecidablePred (· ∈ positive) := fun s => inferInstanceAs (Decidable (s = true))

/-- The state, not the action, determines the atomic truth value. -/
def loopVal (s : Bool) (a : ℕ) : Prop := s = true ∧ a = 0

instance : ∀ s a, Decidable (loopVal s a) :=
  fun s a => inferInstanceAs (Decidable (s = true ∧ a = 0))

private theorem false_counterexample : ωSequence.const false ∈ language
    (counterexample loops both loopVal (Formula.always (.atom 0))) := by
  rw [mem_counterexample_iff]
  refine ⟨⟨trivial, ωSequence.const (), fun _ => rfl⟩, ?_⟩
  simp [Word.Satisfies.always_iff, Word.satisfiesAt_atom, loopVal]

example : IsRun loops both (ωSequence.const true) :=
  ⟨trivial, ωSequence.const (), fun _ => rfl⟩

/-- The other constant lasso is a genuine model run but not a counterexample. -/
example : ωSequence.const true ∉ language
    (counterexample loops both loopVal (Formula.always (.atom 0))) := by
  rw [mem_counterexample_iff]
  rintro ⟨_, hnot⟩
  apply hnot
  simp [Word.Satisfies.always_iff, Word.satisfiesAt_atom, loopVal]

example : (counterexample loops both loopVal (Formula.always (.atom 0))).HasLasso :=
  Buchi.hasLasso_of_mem false_counterexample

private theorem models_positive :
    Models loops positive loopVal (Formula.always (.atom 0)) := by
  intro w
  rintro ⟨hstart, actions, hexec⟩
  have hall : ∀ n, w n = true := by
    intro n
    induction n with
    | zero => exact hstart
    | succ n ih => exact (hexec n).symm.trans ih
  rw [Word.Satisfies.always_iff]
  intro n
  simp [Word.satisfiesAt_atom, loopVal, hall n]

example : ¬ (counterexample loops positive loopVal (Formula.always (.atom 0))).HasLasso :=
  (models_iff_no_lasso loops positive loopVal (Formula.always (.atom 0))).mp models_positive

set_option maxRecDepth 4096 in
example : checkB loops both loopVal (.atom 0) = false := by decide

example : checkB loops positive loopVal (.atom 0) = true := by decide

example : checkB stutter (∅ : Set Unit) labels (.not .top) = true := by decide

/-- The semantic/lasso result, unlike this enumeration algorithm, allows infinite actions. -/
example (lts : LTS Bool ℕ) (initial : Set Bool) (valuation : Bool → ℕ → Prop)
    (φ : Formula ℕ) : Models lts initial valuation φ ↔
      ¬ (counterexample lts initial valuation φ).HasLasso :=
  models_iff_no_lasso lts initial valuation φ

end Cslib.LTL.ModelCheckingTests
