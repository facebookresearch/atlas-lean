/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EARLINESS-TARDINESS WITH A RESTRICTIVE COMMON DUE DATE: definitions

Source:
N. G. Hall, W. Kubiak, and S. P. Sethi, "Earliness-tardiness scheduling problems, II:
deviation of completion times about a restrictive common due date", Operations Research 39
(1991), 847-856, doi:10.1287/opre.39.5.847 (the recognition version is NP-complete in the
ordinary sense);
J. A. Hoogeveen and S. L. van de Velde, "Scheduling around a small common due date",
European Journal of Operational Research 55 (1991), 237-242,
doi:10.1016/0377-2217(91)90228-N (Theorem 3, with all weights equal to 1; independent proof).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EarlinessTardinessRestrictiveCommonDueDate

/-- An instance: the processing times `pᵢ` of the jobs (job `i` is the `i`-th entry), the
common due date `d`, and the threshold `y`. -/
abbrev EarlinessTardinessRestrictiveCommonDueDateInstance := List ℕ × ℕ × ℕ

/-- The jobs of the instance, `Fin n` for `n` listed processing times. -/
abbrev Job (i : EarlinessTardinessRestrictiveCommonDueDateInstance) : Type := Fin i.1.length

/-- The processing time `pᵢ` of job `j`. -/
def processingTime (i : EarlinessTardinessRestrictiveCommonDueDateInstance) (j : Job i) : ℕ :=
  i.1.get j

/-- Completion times `C` form a single-machine schedule from time `0` for processing times
`p`: every job starts at or after time `0`, and of any two distinct jobs one completes before
the other starts. -/
def IsSchedule {n : ℕ} (p : Fin n → ℕ) (C : Fin n → ℝ) : Prop :=
  (∀ j, (p j : ℝ) ≤ C j) ∧ ∀ a b, a ≠ b → C a ≤ C b - p b ∨ C b ≤ C a - p a

/-- Well-formedness of an instance: every processing time is positive, and the common due
date is restrictive, `d < ∑ pᵢ`. -/
def WellFormed (i : EarlinessTardinessRestrictiveCommonDueDateInstance) : Prop :=
  (∀ p ∈ i.1, 0 < p) ∧ i.2.1 < i.1.sum

/-- Some schedule has `∑ᵢ |Cᵢ - d| ≤ y`. -/
def EarlinessTardinessRestrictiveCommonDueDateFeasible
    (i : EarlinessTardinessRestrictiveCommonDueDateInstance) : Prop :=
  ∃ C : Job i → ℝ, IsSchedule (processingTime i) C ∧ ∑ j, |C j - i.2.1| ≤ i.2.2

open Classical in
/-- EARLINESS-TARDINESS WITH A RESTRICTIVE COMMON DUE DATE as a decision problem over
bitstrings. -/
noncomputable def earlinessTardinessRestrictiveCommonDueDateDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EarlinessTardinessRestrictiveCommonDueDateInstance) x with
  | some i => decide (WellFormed i ∧ EarlinessTardinessRestrictiveCommonDueDateFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.EarlinessTardinessRestrictiveCommonDueDate
