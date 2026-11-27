/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RESOURCE CONSTRAINED SCHEDULING TO MINIMIZE TOTAL COMPLETION TIME with one resource and three
processors is NP-complete

Source:
J. Błażewicz, J. K. Lenstra and A. H. G. Rinnooy Kan, "Scheduling subject to resource
constraints: classification and complexity", Discrete Applied Mathematics 5 (1983), 11-24,
doi:10.1016/0166-218X(83)90012-4 (Section 4.1: the strong NP-hardness of
`P3 | res1··, p_j = 1 | C_max`, their Theorem 4, carries over to `ΣC_j`);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SS13] SCHEDULING TO MINIMIZE WEIGHTED
COMPLETION TIME, pp. 240-241, comment: "If resources are allowed, the same subcases mentioned
under RESOURCE CONSTRAINED SCHEDULING are NP-complete, even for equal weights [Blazewicz,
1977a]", and [SS10] RESOURCE CONSTRAINED SCHEDULING, p. 239, comment: "NP-complete in the strong
sense, even if `r = 1` and `m = 3`".
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ThreeProcessorOneResourceSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeProcessorOneResourceTotalCompletionTime

/-!
# RESOURCE CONSTRAINED SCHEDULING TO MINIMIZE TOTAL COMPLETION TIME with one resource and three
processors is NP-complete

INSTANCE: a set `T` of tasks, each having length `l(t) = 1` and weight `w(t) = 1`, `m = 3`
processors, `r = 1` resource with bound `B_1 ∈ ℤ⁺`, a resource requirement `R_1(t)` with
`0 ≤ R_1(t) ≤ B_1` for each task `t`, and a positive integer `K`.
QUESTION: is there a 3-processor schedule `σ` for `T` that obeys the resource constraint, i.e.,
such that for all `u ≥ 0`, if `S(u)` is the set of all `t ∈ T` for which
`σ(t) ≤ u < σ(t) + l(t)`, then the sum of `R_1(t)` over all `t ∈ S(u)` is at most `B_1`, and
such that the sum, over all `t ∈ T`, of `(σ(t) + l(t)) · w(t)` is no more than `K`?

This is SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME [SS13] with the resources of RESOURCE
CONSTRAINED SCHEDULING [SS10] in its subcase `r = 1`, `m = 3`, with equal weights
(Błażewicz, Lenstra and Rinnooy Kan's `P3 | res1··, p_j = 1 | ΣC_j`). With all weights equal to
some `w`, the sum is `w · ∑ (σ(t) + 1)`, so the question for `K` is the question with weights `1`
for `⌊K / w⌋`; the weights are therefore fixed to `1`.

The instance type, the well-formedness condition and the schedule notions are those of
`WantedExt.Complexity.NPComplete.ResourceConstrainedSchedulingWanted` and
`WantedExt.Complexity.NPComplete.ThreeProcessorOneResourceSchedulingWanted`
(`ResourceConstrainedScheduling.ResourceConstrainedSchedulingInstance`,
`ThreeProcessorOneResourceScheduling.WellFormed`, `ResourceConstrainedScheduling.running`,
`ResourceConstrainedScheduling.req`, `ResourceConstrainedScheduling.bound`), with one change of
reading: the last component of the instance, the overall deadline `D` there, is the bound `K`
here, and the condition `0 < D` of `WellFormed` is the positivity of `K`. The schedule has no
deadline. An `m`-processor schedule is a start time `σ(t) ∈ ℤ₀⁺` for each task such that at
every time `u` at most `m` tasks run (`|S(u)| ≤ m`). Binary encoding of all numbers (the problem
is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open ResourceConstrainedScheduling in
/-- Some `m`-processor schedule of the unit-length tasks keeps, at every time, the total
requirement of the running tasks within each resource bound, and has total completion time
`∑_t (σ(t) + 1)` at most `K` (the last component of the instance). -/
def ThreeProcessorOneResourceTotalCompletionTimeFeasible
    (i : ResourceConstrainedSchedulingInstance) : Prop :=
  ∃ σ : Task i → ℕ, (∀ u, (running i σ u).card ≤ i.1) ∧
    (∀ u, ∀ k < i.2.1, ∑ t ∈ running i σ u, req i t k ≤ bound i k) ∧
    ∑ t, (σ t + 1) ≤ i.2.2.2.2

open Classical in
/-- RESOURCE CONSTRAINED SCHEDULING TO MINIMIZE TOTAL COMPLETION TIME with one resource and
three processors as a decision problem over bitstrings. -/
noncomputable def threeProcessorOneResourceTotalCompletionTimeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ResourceConstrainedScheduling.ResourceConstrainedSchedulingInstance) x with
  | some i => decide (ThreeProcessorOneResourceScheduling.WellFormed i ∧
      ThreeProcessorOneResourceTotalCompletionTimeFeasible i)
  | none => false

/-- **RESOURCE CONSTRAINED SCHEDULING TO MINIMIZE TOTAL COMPLETION TIME is NP-complete for one
resource and three processors.** Source: Błażewicz, Lenstra and Rinnooy Kan (1983), Section
4.1; Garey and Johnson (1979), [SS13], comment. -/
public theorem_wanted threeProcessorOneResourceTotalCompletionTime_npComplete :
    threeProcessorOneResourceTotalCompletionTimeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeProcessorOneResourceTotalCompletionTimeDec

end MetaMathlibExt.Complexity.NPComplete.ThreeProcessorOneResourceTotalCompletionTime
