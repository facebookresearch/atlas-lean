/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Foundations.Semantics.LTS.OmegaExecution

/-!
# Weak and strong fairness for action classes

Enabledness concerns all outgoing transitions from the current state, while occurrence
concerns the label actually taken at the corresponding step of an infinite execution.

Lamport's `WF_f(A)` and `SF_f(A)` use `⟨A⟩_f`, the `A` steps that change the value of `f`.
The label-based predicates agree with them when a taken label is in the class exactly when
its step is an `⟨A⟩_f` step, and at each state of the execution a class-labeled transition is
available exactly when some target state in the TLA state space makes `⟨A⟩_f` true from that
state. A class-labeled step that leaves `f` unchanged can count as an occurrence or a witness
of enabledness here, but not in Lamport's conditions.

## References

* L. Lamport, *The temporal logic of actions*, 1994, Section 5.3, equations (17) and (18).
-/

@[expose] public section

namespace Cslib.LTS

variable {State Label : Type*}

/-- An action class is enabled at `s` if some label in the class labels a transition out of `s`.
The witnessing label and target may vary from state to state. -/
def ActionClassEnabled (lts : LTS State Label) (actions : Set Label) (s : State) : Prop :=
  ∃ label ∈ actions, ∃ t, lts.Tr s label t

namespace OmegaExecution

variable {lts : LTS State Label} {states : ωSequence State} {labels : ωSequence Label}

/-- An infinite execution is weakly fair for `actions` if enabledness of the class at every
state index from some cutoff onward implies that labels in `actions` are taken at arbitrarily
late steps. -/
def WeaklyFair (_execution : lts.OmegaExecution states labels) (actions : Set Label) : Prop :=
  (∃ start, ∀ n ≥ start, lts.ActionClassEnabled actions (states n)) →
    ∀ cutoff, ∃ n ≥ cutoff, labels n ∈ actions

/-- An infinite execution is strongly fair for `actions` if enabledness of the class at
arbitrarily late state indices implies that labels in `actions` are taken at arbitrarily
late steps. -/
def StronglyFair (_execution : lts.OmegaExecution states labels) (actions : Set Label) : Prop :=
  (∀ cutoff, ∃ n ≥ cutoff, lts.ActionClassEnabled actions (states n)) →
    ∀ cutoff, ∃ n ≥ cutoff, labels n ∈ actions

/-- Strong fairness implies weak fairness for the same execution and action class. -/
theorem StronglyFair.weaklyFair {execution : lts.OmegaExecution states labels}
    {actions : Set Label} (h : execution.StronglyFair actions) : execution.WeaklyFair actions := by
  rintro ⟨start, henabled⟩
  exact h fun cutoff ↦ ⟨max start cutoff, le_max_right _ _, henabled _ (le_max_left _ _)⟩

end OmegaExecution
end Cslib.LTS
