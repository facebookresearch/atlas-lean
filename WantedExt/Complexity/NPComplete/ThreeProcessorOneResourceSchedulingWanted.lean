/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RESOURCE CONSTRAINED SCHEDULING with one resource and three processors is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS10] RESOURCE CONSTRAINED
SCHEDULING, comment: NP-complete in the strong sense, even if `r = 1` and `m = 3`;
M. R. Garey and D. S. Johnson, "Complexity results for multiprocessor scheduling under resource
constraints", SIAM Journal on Computing 4 (1975), 397-411, doi:10.1137/0204035.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ResourceConstrainedSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeProcessorOneResourceScheduling

/-!
# RESOURCE CONSTRAINED SCHEDULING with one resource and three processors is NP-complete

INSTANCE: a set `T` of tasks, each having length `l(t) = 1`, `m = 3` processors, `r = 1`
resource with bound `B_1 ∈ ℤ⁺`, a resource requirement `R_1(t)` with `0 ≤ R_1(t) ≤ B_1` for each
task `t`, and an overall deadline `D ∈ ℤ⁺`. QUESTION: is there a 3-processor schedule `σ` for `T`
that meets the overall deadline `D` and obeys the resource constraint, i.e., such that for all
`u ≥ 0`, if `S(u)` is the set of all `t ∈ T` for which `σ(t) ≤ u < σ(t) + l(t)`, then the sum of
`R_1(t)` over all `t ∈ S(u)` is at most `B_1`?

This is the restriction of RESOURCE CONSTRAINED SCHEDULING
(`WantedExt.Complexity.NPComplete.ResourceConstrainedSchedulingWanted`) to `m = 3` and `r = 1`.
The instance type, the parent well-formedness condition and the question are that module's
(`ResourceConstrainedScheduling.ResourceConstrainedSchedulingInstance`,
`ResourceConstrainedScheduling.WellFormed`,
`ResourceConstrainedScheduling.ResourceConstrainedSchedulingFeasible`); the restriction is added
to `WellFormed`. Binary encoding of all numbers (the problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: it is a well-formed RESOURCE CONSTRAINED SCHEDULING instance
(`0 < m`, `0 < r`, `r` positive bounds, every task has `r` requirements with `R_k(t) ≤ B_k`,
`0 < D`), with `m = 3` processors and `r = 1` resource. -/
def WellFormed (i : ResourceConstrainedScheduling.ResourceConstrainedSchedulingInstance) :
    Prop :=
  ResourceConstrainedScheduling.WellFormed i ∧ i.1 = 3 ∧ i.2.1 = 1

open Classical in
/-- RESOURCE CONSTRAINED SCHEDULING with one resource and three processors as a decision problem
over bitstrings. -/
noncomputable def threeProcessorOneResourceSchedulingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ResourceConstrainedScheduling.ResourceConstrainedSchedulingInstance) x with
  | some i => decide (WellFormed i ∧
      ResourceConstrainedScheduling.ResourceConstrainedSchedulingFeasible i)
  | none => false

/-- **RESOURCE CONSTRAINED SCHEDULING is NP-complete for one resource and three processors.**
Source: Garey and Johnson (1979), [SS10], comment; Garey and Johnson (1975). -/
public theorem_wanted threeProcessorOneResourceScheduling_npComplete :
    threeProcessorOneResourceSchedulingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeProcessorOneResourceSchedulingDec

end MetaMathlibExt.Complexity.NPComplete.ThreeProcessorOneResourceScheduling
