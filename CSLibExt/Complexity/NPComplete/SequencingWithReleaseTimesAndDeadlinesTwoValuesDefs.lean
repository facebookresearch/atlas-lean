/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEQUENCING WITH RELEASE TIMES AND DEADLINES with two release times and two deadlines: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS1] SEQUENCING WITH RELEASE TIMES
AND DEADLINES, p. 236, comment: the problem "remains NP-complete (in the ordinary sense) even
when each [of `r(t)` and `d(t)`] can take on only two values" (no citation is given), and
Theorem 3.8, pp. 70-71, whose transformation from PARTITION to SEQUENCING WITHIN INTERVALS uses
only the release times `0` and `⌈B/2⌉` and the deadlines `⌈(B+1)/2⌉` and `B + 1`.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Card
public import CSLibExt.Complexity.NPComplete.ReleaseDeadlinesSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SequencingWithReleaseTimesAndDeadlinesTwoValues

/-- Well-formedness of an instance: every length `l(t)` and every deadline `d(t)` is positive,
the set `{r(t) : t ∈ T}` of release times has at most two elements, and the set
`{d(t) : t ∈ T}` of deadlines has at most two elements. -/
def WellFormed (i : ReleaseDeadlinesScheduling.ReleaseDeadlinesSchedulingInstance) : Prop :=
  (∀ t ∈ i, 0 < t.1 ∧ 0 < t.2.2) ∧ (i.map fun t => t.2.1).toFinset.card ≤ 2 ∧
    (i.map fun t => t.2.2).toFinset.card ≤ 2

open Classical in
/-- SEQUENCING WITH RELEASE TIMES AND DEADLINES with two release times and two deadlines as a
decision problem over bitstrings. -/
noncomputable def sequencingWithReleaseTimesAndDeadlinesTwoValuesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ReleaseDeadlinesScheduling.ReleaseDeadlinesSchedulingInstance) x with
  | some i => decide (WellFormed i ∧
      ReleaseDeadlinesScheduling.ReleaseDeadlinesSchedulingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SequencingWithReleaseTimesAndDeadlinesTwoValues
