/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WEIGHTED EARLINESS-TARDINESS ABOUT A COMMON DUE DATE: definitions

Source:
N. G. Hall and M. E. Posner, "Earliness-tardiness scheduling problems, I: weighted deviation of
completion times about a common due date", Operations Research 39 (1991), 836-846,
doi:10.1287/opre.39.5.836.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeightedEarlinessTardinessCommonDueDate

/-- An instance: the jobs, job `j` given as `(p_j, w_j)` (processing time and weight), the
common due date `d` and the bound `K`. -/
abbrev WeightedEarlinessTardinessCommonDueDateInstance := List (ℕ × ℕ) × ℕ × ℕ

/-- Well-formedness of an instance: every processing time is positive and the due date is at
least the total processing time. -/
def WellFormed (i : WeightedEarlinessTardinessCommonDueDateInstance) : Prop :=
  (∀ job ∈ i.1, 0 < job.1) ∧ (i.1.map Prod.fst).sum ≤ i.2.1

/-- There is a nonpreemptive one-machine schedule with total weighted deviation at most `K`:
start times `S` such that distinct jobs occupy disjoint intervals `[S_j, S_j + p_j)`, and
`∑_j w_j |S_j + p_j - d| ≤ K`. -/
def WeightedEarlinessTardinessCommonDueDateFeasible
    (i : WeightedEarlinessTardinessCommonDueDateInstance) : Prop :=
  ∃ S : Fin i.1.length → ℕ,
    (∀ j k, j ≠ k → S j + (i.1.get j).1 ≤ S k ∨ S k + (i.1.get k).1 ≤ S j) ∧
    ∑ j, (i.1.get j).2 * (((S j + (i.1.get j).1 : ℕ) : ℤ) - i.2.1).natAbs ≤ i.2.2

open Classical in
/-- WEIGHTED EARLINESS-TARDINESS ABOUT A COMMON DUE DATE as a decision problem over bitstrings. -/
noncomputable def weightedEarlinessTardinessCommonDueDateDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := WeightedEarlinessTardinessCommonDueDateInstance) x with
  | some i => decide (WellFormed i ∧ WeightedEarlinessTardinessCommonDueDateFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.WeightedEarlinessTardinessCommonDueDate
