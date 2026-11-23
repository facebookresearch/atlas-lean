/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Epistemic.Basic

/-!
# Consumer tests for epistemic logic

The coin model distinguishes the two agents and both coin values. A dead-end
model checks that knowledge is universal over successors and that the truth
axiom needs reflexivity.
-/

set_option autoImplicit false

open Cslib.Epistemic

namespace CSLibExtTest.Logics.Epistemic.Basic

private def deadEnd : Model Bool Unit Unit where
  rel := fun _ _ _ => False
  valuation := fun _ _ => False
  nonempty_world := ⟨false⟩

/-- The informed agent knows heads at the heads world. -/
example : Sat muddy (.know 0 (.atom ())) true :=
  (sat_know_zero_atom true).mpr rfl

/-- The same agent does not know heads at tails. -/
example : ¬ Sat muddy (.know 0 (.atom ())) false := by
  intro h
  exact Bool.false_ne_true ((sat_know_zero_atom false).mp h)

/-- Negation reverses the informed agent's answer at tails. -/
example : Sat muddy (.know 0 (.not (.atom ()))) false :=
  (sat_know_zero_not_atom false).mpr rfl

/-- Negation does not make tails true at heads. -/
example : ¬ Sat muddy (.know 0 (.not (.atom ()))) true := by
  intro h
  exact Bool.false_ne_true ((sat_know_zero_not_atom true).mp h).symm

/-- The uninformed agent cannot exclude tails even at the heads world. -/
example : ¬ Sat muddy (.know 1 (.atom ())) true :=
  muddy_not_know_one_p_true

/-- Negative introspection applies to the uninformed agent's total relation. -/
example : Sat muddy (.know 1 (.not (.know 1 (.atom ())))) true :=
  valid_know_neg muddy (i := 1) (φ := .atom ()) (by
    intro a b c _ _
    simp [muddy]) true muddy_not_know_one_p_true

/-- Positive introspection applies to the informed agent's identity relation. -/
example : Sat muddy (.know 0 (.know 0 (.atom ()))) true :=
  valid_know_pos muddy (i := 0) (φ := .atom ()) (by
    intro a b c hab hbc
    exact hab.trans hbc) true ((sat_know_zero_atom true).mpr rfl)

/-- Knowledge is true for the informed agent at both coin values. -/
example : Valid muddy (.imp (.know 0 (.atom ())) (.atom ())) :=
  valid_know_truth muddy (i := 0) (by
    intro v
    simp [muddy])

/-- Distribution remains valid for the uninformed agent. -/
example : Valid muddy (.imp (.know 1 (.imp (.atom ()) .bot))
    (.imp (.know 1 (.atom ())) (.know 1 .bot))) :=
  valid_know_dist muddy

/-- The uninformed agent knows that the other agent knows whether heads holds. -/
example : Sat muddy (.know 1 (.or (.know 0 (.atom ()))
    (.know 0 (.not (.atom ()))))) false :=
  muddy_know_one_knows_whether false

/-- Nonempty worlds prevent vacuous validity of falsity. -/
example : ¬ Valid muddy .bot :=
  not_valid_bot muddy

/-- At a dead end even knowledge of falsity holds, with no successor witness. -/
example : Sat deadEnd (.know () .bot) false := by
  intro v h
  cases h

/-- The truth axiom fails on that nonreflexive frame. -/
example : ¬ Sat deadEnd (.imp (.know () .bot) .bot) false := by
  intro h
  apply h
  intro v hrel
  cases hrel

end CSLibExtTest.Logics.Epistemic.Basic
