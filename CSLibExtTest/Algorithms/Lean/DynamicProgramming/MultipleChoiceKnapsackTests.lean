/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.MultipleChoiceKnapsack
public meta import CSLibExt.Algorithms.Lean.DynamicProgramming.MultipleChoiceKnapsack
public import Mathlib.Algebra.Order.Group.Int
public meta import Mathlib.Algebra.Order.Group.Int

/-!
# Multiple-choice knapsack tests

Two groups `{(1, 3), (2, 5)}` and `{(1, 2), (3, 7)}` (weight, value): the packing optimum is
`10` at capacity `4`, `12` at capacity `5`, and `⊥` at capacity `1` (every selection weighs at
least `2`); the covering optimum is `12` for target `5` and `⊥` for target `6` (every selection
weighs at most `5`). A CellBender-style instance with negative log-probability values and a
noise-count target.
The bottom-up table agrees with the recurrence. Non-vacuity: an explicit selection, and the
theorems instantiated. Axiom audit follows.
-/

namespace Cslib.Algorithms.Lean.MultipleChoiceKnapsack

/-- Two groups of two items each. -/
def groups : List (List (Item ℤ)) := [[⟨1, 3⟩, ⟨2, 5⟩], [⟨1, 2⟩, ⟨3, 7⟩]]

#guard bestPacking groups 4 = ((10 : ℤ) : WithBot ℤ)
#guard bestPacking groups 1 = ⊥
#guard bestPacking groups 5 = ((12 : ℤ) : WithBot ℤ)
#guard bestCovering groups 5 = ((12 : ℤ) : WithBot ℤ)
#guard bestCovering groups 6 = ⊥
#guard bestCovering groups 0 = ((12 : ℤ) : WithBot ℤ)
#guard bestPacking ([] : List (List (Item ℤ))) 0 = ((0 : ℤ) : WithBot ℤ)
#guard bestCovering ([] : List (List (Item ℤ))) 1 = ⊥
#guard packingTable 6 groups = (List.range 7).map (bestPacking groups)

/-- Two count-matrix entries; item `c` is "noise count `c`" with a negative log-probability. -/
def noiseEntries : List (List (Item ℤ)) :=
  [[⟨0, -1⟩, ⟨1, -2⟩, ⟨2, -5⟩], [⟨0, -3⟩, ⟨1, -1⟩, ⟨2, -4⟩]]

-- Without a target the per-entry maxima are chosen (counts 0 and 1, value -2); a total noise
-- target of 3 forces counts (1, 2) or (2, 1), the better being -6.
#guard bestCovering noiseEntries 0 = ((-2 : ℤ) : WithBot ℤ)
#guard bestCovering noiseEntries 3 = ((-6 : ℤ) : WithBot ℤ)
#guard bestCovering noiseEntries 5 = ⊥

/-- Non-vacuity: a selection of weight `4` and value `10`. -/
theorem selection_witness : IsSelection groups [⟨1, 3⟩, ⟨3, 7⟩] :=
  List.Forall₂.cons (by simp) (List.Forall₂.cons (by simp) List.Forall₂.nil)

example : ((totalValue ([⟨1, 3⟩, ⟨3, 7⟩] : List (Item ℤ)) : ℤ) : WithBot ℤ) ≤
    bestPacking groups 4 :=
  le_bestPacking selection_witness (by decide)

example : ((totalValue ([⟨1, 3⟩, ⟨3, 7⟩] : List (Item ℤ)) : ℤ) : WithBot ℤ) ≤
    bestCovering groups 4 :=
  le_bestCovering selection_witness (by decide)

example : ¬ ∃ choice, IsSelection groups choice ∧ totalWeight choice ≤ 1 :=
  bestPacking_eq_bot_iff.mp (by decide)

#print axioms le_bestPacking
#print axioms exists_eq_of_bestPacking_eq_coe
#print axioms bestPacking_eq_bot_iff
#print axioms le_bestCovering
#print axioms exists_eq_of_bestCovering_eq_coe
#print axioms bestCovering_eq_bot_iff
#print axioms packingTable_eq

end Cslib.Algorithms.Lean.MultipleChoiceKnapsack
