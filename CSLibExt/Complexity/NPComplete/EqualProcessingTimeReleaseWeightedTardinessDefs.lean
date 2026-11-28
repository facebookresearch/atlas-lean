/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EQUAL-PROCESSING-TIME WEIGHTED TARDINESS WITH RELEASE DATES (1|p_i=p;r_i|Σw_iT_i): definitions

Source:
Z.-L. Chen and N. G. Hall, "Strong NP-hardness and approximation algorithm for weighted tardiness
with release dates and identical processing times", arXiv:2609.28751 (2026), Section 3 and
Theorem 1 (preprint);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class `ein_ma` (single
machine problems), entry `1|p_i=p;r_i|Σw_iT_i` (listed as open).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import CSLibExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EqualProcessingTimeReleaseWeightedTardiness

open SequencingToMinimizeWeightedTardiness (IsOneProcessorSchedule)

/-- An instance: the common processing time `p`, the jobs, job `j` being the `j`-th triple
`(r_j, d_j, w_j)` of release date, due date and weight, and the bound `K`. -/
abbrev EqualProcessingTimeReleaseWeightedTardinessInstance := ℕ × List (ℕ × ℕ × ℕ) × ℕ

/-- The jobs of the instance, `Fin N` for `N` listed triples. -/
abbrev Job (i : EqualProcessingTimeReleaseWeightedTardinessInstance) : Type :=
  Fin i.2.1.length

/-- The release date `r_j` of job `j`. -/
def release (i : EqualProcessingTimeReleaseWeightedTardinessInstance) (j : Job i) : ℕ :=
  (i.2.1.get j).1

/-- The due date `d_j` of job `j`. -/
def dueDate (i : EqualProcessingTimeReleaseWeightedTardinessInstance) (j : Job i) : ℕ :=
  (i.2.1.get j).2.1

/-- The weight `w_j` of job `j`. -/
def weight (i : EqualProcessingTimeReleaseWeightedTardinessInstance) (j : Job i) : ℕ :=
  (i.2.1.get j).2.2

/-- Well-formedness of an instance: the common processing time `p` and every weight are
positive. -/
def WellFormed (i : EqualProcessingTimeReleaseWeightedTardinessInstance) : Prop :=
  0 < i.1 ∧ ∀ x ∈ i.2.1, 0 < x.2.2

/-- Some one-processor schedule with every processing time equal to `p` starts every job no
earlier than its release date and has total weighted tardiness
`∑_j w_j (s_j + p - d_j)` (truncated subtraction) at most `K`. -/
def EqualProcessingTimeReleaseWeightedTardinessFeasible
    (i : EqualProcessingTimeReleaseWeightedTardinessInstance) : Prop :=
  ∃ s : Job i → ℕ, IsOneProcessorSchedule (fun _ => i.1) s ∧
    (∀ j, release i j ≤ s j) ∧
    ∑ j, weight i j * (s j + i.1 - dueDate i j) ≤ i.2.2

open Classical in
/-- EQUAL-PROCESSING-TIME WEIGHTED TARDINESS WITH RELEASE DATES as a decision problem over
bitstrings. -/
noncomputable def equalProcessingTimeReleaseWeightedTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EqualProcessingTimeReleaseWeightedTardinessInstance) x with
  | some i => decide (WellFormed i ∧ EqualProcessingTimeReleaseWeightedTardinessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.EqualProcessingTimeReleaseWeightedTardiness
