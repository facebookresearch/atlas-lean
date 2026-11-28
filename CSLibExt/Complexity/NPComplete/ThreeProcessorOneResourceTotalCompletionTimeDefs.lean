/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RESOURCE CONSTRAINED SCHEDULING TO MINIMIZE TOTAL COMPLETION TIME with one resource and three
processors: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ThreeProcessorOneResourceSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeProcessorOneResourceTotalCompletionTime

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

end MetaMathlibExt.Complexity.NPComplete.ThreeProcessorOneResourceTotalCompletionTime
