/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TOTAL DISCREPANCY: definitions

Source:
M. R. Garey, R. E. Tarjan, and G. T. Wilfong, "One-processor scheduling with symmetric
earliness and tardiness penalties", Mathematics of Operations Research 13 (1988), 330-348,
doi:10.1287/moor.13.2.330 (Section 2.1, the Total Discrepancy decision problem is
NP-complete); technical report version: "One-processor scheduling of tasks with preferred
starting times", Princeton University CS-TR-049-86 (1986).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TotalDiscrepancy

/-- An instance: the tasks, task `i` being the `i`-th pair `(lᵢ, Mᵢ)` of length and preferred
midtime, and the bound `k`. -/
abbrev TotalDiscrepancyInstance := List (ℕ × ℕ) × ℕ

/-- The tasks of the instance, `Fin N` for `N` listed pairs. -/
abbrev Task (i : TotalDiscrepancyInstance) : Type := Fin i.1.length

/-- The length `lᵢ` of task `t`. -/
def taskLength (i : TotalDiscrepancyInstance) (t : Task i) : ℕ :=
  (i.1.get t).1

/-- The preferred midtime `Mᵢ` of task `t`. -/
def preferredMidtime (i : TotalDiscrepancyInstance) (t : Task i) : ℕ :=
  (i.1.get t).2

/-- Starting times `s` form a one-processor schedule for positive lengths `l`: of any two
distinct tasks, one finishes before the other starts. -/
def IsSchedule {N : ℕ} (l : Fin N → ℕ) (s : Fin N → ℝ) : Prop :=
  ∀ a b, a ≠ b → s a + l a ≤ s b ∨ s b + l b ≤ s a

/-- Well-formedness of an instance: `N ∈ ℤ⁺` (some task), every length and preferred midtime
is positive, and `k ∈ ℤ⁺`. -/
def WellFormed (i : TotalDiscrepancyInstance) : Prop :=
  i.1 ≠ [] ∧ (∀ x ∈ i.1, 0 < x.1 ∧ 0 < x.2) ∧ 0 < i.2

/-- Some schedule has total discrepancy at most `k`: the sum over the tasks of the distance
between the actual midtime `sᵢ + lᵢ / 2` and the preferred midtime `Mᵢ` is at most `k`. -/
def TotalDiscrepancyFeasible (i : TotalDiscrepancyInstance) : Prop :=
  ∃ s : Task i → ℝ, IsSchedule (taskLength i) s ∧
    ∑ t, |s t + (taskLength i t : ℝ) / 2 - preferredMidtime i t| ≤ i.2

open Classical in
/-- TOTAL DISCREPANCY as a decision problem over bitstrings. -/
noncomputable def totalDiscrepancyDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TotalDiscrepancyInstance) x with
  | some i => decide (WellFormed i ∧ TotalDiscrepancyFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TotalDiscrepancy
