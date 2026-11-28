/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPLE CHOICE SCHEDULING WITHIN INTERVALS: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 4 (1983), 189-203,
doi:10.1016/0196-6774(83)90045-7, problem [1] MULTIPLE CHOICE SCHEDULING WITHIN INTERVALS (the
problem, credited to Simons and Sipser, transformation from 3SAT);
B. Simons and M. Sipser, "On scheduling unit-length jobs with multiple release time/deadline
intervals", Operations Research 32 (1984), 80-88, doi:10.1287/opre.32.1.80.
-/
module

public import Mathlib.Data.Fintype.Card
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipleChoiceSchedulingWithinIntervals

/-- An instance: the number `m` of processors, the common task length `l`, and for each task the
list of its permissible intervals `(aᵢ(t), bᵢ(t))`. -/
abbrev MultipleChoiceSchedulingWithinIntervalsInstance := ℕ × ℕ × List (List (ℕ × ℕ))

/-- Well-formedness of an instance: every permissible interval `[a, b]` has `a ≤ b - l`, i.e.
`a + l ≤ b`. -/
def WellFormed (i : MultipleChoiceSchedulingWithinIntervalsInstance) : Prop :=
  ∀ C ∈ i.2.2, ∀ I ∈ C, I.1 + i.2.1 ≤ I.2

/-- Some starting times `s` run at most `m` tasks at every time and place every task inside one
of its permissible intervals. -/
def MultipleChoiceSchedulingWithinIntervalsFeasible
    (i : MultipleChoiceSchedulingWithinIntervalsInstance) : Prop :=
  ∃ s : Fin i.2.2.length → ℕ,
    (∀ u : ℕ, (Finset.univ.filter fun t => s t ≤ u ∧ u < s t + i.2.1).card ≤ i.1) ∧
      ∀ t : Fin i.2.2.length, ∃ I ∈ i.2.2[t], I.1 ≤ s t ∧ s t + i.2.1 ≤ I.2

open Classical in
/-- MULTIPLE CHOICE SCHEDULING WITHIN INTERVALS as a decision problem over bitstrings. -/
noncomputable def multipleChoiceSchedulingWithinIntervalsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipleChoiceSchedulingWithinIntervalsInstance) x with
  | some i => decide (WellFormed i ∧ MultipleChoiceSchedulingWithinIntervalsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultipleChoiceSchedulingWithinIntervals
