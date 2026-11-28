/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Logics.Testing.ControlFlowCoverage

/-! # Regressions for control-flow coverage -/

set_option autoImplicit false

namespace Cslib.Testing.ControlFlowCoverage.Tests

private def noEdge (_ _ : Unit) : Prop := False

-- With an isolated node and no tests, branch coverage is vacuous but statement coverage fails.
example : BranchCoverage (∅ : Set (Path noEdge)) ∧
    ¬ StatementCoverage (∅ : Set (Path noEdge)) := by
  constructor
  · intro _ _ h
    exact h.elim
  · intro h
    obtain ⟨_, hm, _⟩ := h ()
    exact hm

-- Visiting the endpoints with an intervening block does not cover a direct edge.
example : ¬ ([0, 2] : List (Fin 3)) <:+: [0, 1, 2] := by
  simp [List.infix_cons_iff, List.cons_prefix_cons]

-- Both atoms can individually attain both truth values but cannot disagree in one evaluation.
private def correlated : Evaluations Bool (fun _ : Unit => Bool) :=
  fun _ t => {fun _ => some t}

example : ConditionCoverage correlated Set.univ ∧
    ¬ MultipleConditionCoverage correlated Set.univ := by
  constructor
  · intro c a b
    exact ⟨b, Set.mem_univ _, fun _ => some b, rfl, rfl⟩
  · intro h
    obtain ⟨t, _, hobs⟩ := h () id
    have he : (fun b : Bool => some (id b)) = (fun _ => some t) := hobs
    have hf : some false = some t := congrFun he false
    have ht : some true = some t := congrFun he true
    cases hf.trans ht.symm

-- An atom skipped in every evaluation cannot be credited with either value.
private def partialObservations : Evaluations Bool (fun _ : Unit => Bool) :=
  fun _ t => {fun a => if a then none else some t}

example : ¬ ConditionCoverage partialObservations Set.univ := by
  intro h
  obtain ⟨t, _, eval, hobs, hv⟩ := h () true false
  have he : eval = (fun a : Bool => if a then none else some t) := hobs
  subst eval
  cases hv

end Cslib.Testing.ControlFlowCoverage.Tests
