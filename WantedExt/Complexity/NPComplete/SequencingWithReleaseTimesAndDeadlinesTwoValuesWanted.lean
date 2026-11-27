/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEQUENCING WITH RELEASE TIMES AND DEADLINES with two release times and two deadlines is
NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS1] SEQUENCING WITH RELEASE TIMES
AND DEADLINES, p. 236, comment: the problem "remains NP-complete (in the ordinary sense) even
when each [of `r(t)` and `d(t)`] can take on only two values" (no citation is given), and
Theorem 3.8, pp. 70-71, whose transformation from PARTITION to SEQUENCING WITHIN INTERVALS uses
only the release times `0` and `⌈B/2⌉` and the deadlines `⌈(B+1)/2⌉` and `B + 1`.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Card
public import WantedExt.Complexity.NPComplete.ReleaseDeadlinesSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SequencingWithReleaseTimesAndDeadlinesTwoValues

/-!
# SEQUENCING WITH RELEASE TIMES AND DEADLINES with two release times and two deadlines is
NP-complete

INSTANCE: a set `T` of tasks and, for each task `t ∈ T`, a length `l(t) ∈ ℤ⁺`, a release time
`r(t) ∈ ℤ₀⁺`, and a deadline `d(t) ∈ ℤ⁺`, where `r(t)` takes at most two distinct values and
`d(t)` takes at most two distinct values over `T`.
QUESTION: is there a one-processor schedule for `T` that satisfies the release time constraints
and meets all the deadlines, i.e., a one-to-one function `σ : T → ℤ₀⁺`, with `σ(t) > σ(t')`
implying `σ(t) ≥ σ(t') + l(t')`, such that, for all `t ∈ T`, `σ(t) ≥ r(t)` and
`σ(t) + l(t) ≤ d(t)`?

The instance type and the question are those of
`WantedExt.Complexity.NPComplete.ReleaseDeadlinesSchedulingWanted`
(`ReleaseDeadlinesScheduling.ReleaseDeadlinesSchedulingInstance`, the list of triples
`(l(t), r(t), d(t))`, and `ReleaseDeadlinesScheduling.ReleaseDeadlinesSchedulingFeasible`: start
times with `r(t) ≤ σ(t)`, `σ(t) + l(t) ≤ d(t)`, and for every two tasks one finishing before the
other starts). Since every length is positive, that non-overlap condition is equivalent to
Garey and Johnson's: it makes `σ` one-to-one, and `σ(t) > σ(t')` forces
`σ(t) ≥ σ(t') + l(t')`. The positivity of lengths and deadlines and the bound on the number of
distinct release times and deadlines are the conditions of `WellFormed`. The problem is
NP-complete in the ordinary sense; numbers use the binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **SEQUENCING WITH RELEASE TIMES AND DEADLINES is NP-complete with two release times and two
deadlines.** Source: Garey and Johnson (1979), [SS1], comment, and Theorem 3.8. -/
public theorem_wanted sequencingWithReleaseTimesAndDeadlinesTwoValues_npComplete :
    sequencingWithReleaseTimesAndDeadlinesTwoValuesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L sequencingWithReleaseTimesAndDeadlinesTwoValuesDec

end MetaMathlibExt.Complexity.NPComplete.SequencingWithReleaseTimesAndDeadlinesTwoValues
