/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Parameterized.Defs

/-!
# Checking circuit admissibility

Check the gate references and every gate's weft and depth in the circuit
representation used by weighted satisfiability.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized.NormalForm

/-- Check the weft and depth of every gate, including gates unreachable from the output.
Every reference in a NOT, AND or OR gate must point to a strictly earlier gate. -/
def validCircuit (t d : ℕ) (C : List WCGate) : Bool :=
  ((List.finRange C.length).all fun i => C[i].2.all fun j =>
    decide ((C[i].1 = 2 ∨ C[i].1 = 3 ∨ C[i].1 = 4) → j < i.val)) &&
  (wcCircuitWefts C).all (· ≤ t) && (wcCircuitDepths C).all (· ≤ d)

/-- The executable validity check enforces exactly the syntax, weft, and depth restrictions. -/
theorem validCircuit_iff (t d : ℕ) (C : List WCGate) :
    validCircuit t d C ↔ WCWellFormed C ∧ (∀ i ∈ wcCircuitWefts C, i ≤ t) ∧
      (∀ i ∈ wcCircuitDepths C, i ≤ d) := by
  simp only [validCircuit, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_finRange, true_implies, and_assoc]
  apply and_congr_left'
  constructor
  · intro h j hj a ha hg
    exact h ⟨j, hj⟩ a ha hg
  · intro h j a ha hg
    exact h j.val j.isLt a ha hg

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized.NormalForm
