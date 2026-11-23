/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RESOURCE CONSTRAINED SCHEDULING with three processors and unit resources is NP-complete

Source:
J. Błażewicz, J. K. Lenstra and A. H. G. Rinnooy Kan, "Scheduling subject to resource
constraints: classification and complexity", Discrete Applied Mathematics 5 (1983), 11-24,
doi:10.1016/0166-218X(83)90012-4 (the problem `P3 | res·11, p_j = 1 | C_max`);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problems [SS10] RESOURCE CONSTRAINED SCHEDULING (parent
problem) and [GT11] PARTITION INTO TRIANGLES (source problem of the reduction below).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ResourceConstrainedSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeProcessorUnitResourceScheduling

/-!
# RESOURCE CONSTRAINED SCHEDULING with three processors and unit resources is NP-complete

INSTANCE: a set `T` of tasks, each having length `l(t) = 1`, `m = 3` processors, a number
`r ∈ ℤ⁺` of resources (part of the instance), every resource bound `B_i = 1`, a resource
requirement `R_i(t) ∈ {0, 1}` for each task `t` and resource `i`, and an overall deadline
`D ∈ ℤ⁺`.
QUESTION: is there a 3-processor schedule `σ` for `T` that meets the overall deadline `D` and
obeys the resource constraints, i.e. for all `u ≥ 0`, if `S(u)` is the set of all `t ∈ T` with
`σ(t) ≤ u < σ(t) + l(t)`, then for each resource `i` the sum of `R_i(t)` over `t ∈ S(u)` is at
most `B_i`?

This is RESOURCE CONSTRAINED SCHEDULING ([SS10],
`WantedExt.Complexity.NPComplete.ResourceConstrainedSchedulingWanted`) restricted to `m = 3`
and unit resource bounds, the case `P3 | res·11, p_j = 1 | C_max` in the notation of Błażewicz,
Lenstra and Rinnooy Kan (any number of resource types, every bound `1`, every requirement at
most `1`). The instance, the parent's well-formedness and the question are reused unchanged;
the restriction is added to well-formedness. The parent requires `R_i(t) ≤ B_i`, so bounds
equal to `1` make every requirement `0` or `1`.

Hardness (the original text was not available to us; this short reduction establishes it):
PARTITION INTO TRIANGLES ([GT11], NP-complete in the strong sense) reduces to this problem.
Given a graph `H = (V, E)` with `|V| = 3q`, take the vertices as tasks, `D = q`, and one
resource for each pair of distinct non-adjacent vertices, required by exactly those two
vertices (plus one resource required by no task, so that `r ≥ 1`). A schedule meeting `D`
puts `3q` tasks into `q` time slots of at most three tasks, hence exactly three per slot, and
the resource constraints say that the three tasks of a slot are pairwise adjacent in `H`: the
slots are a partition of `V` into triangles, and conversely.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed RESOURCE CONSTRAINED SCHEDULING instance
(`0 < m`, `0 < r`, `r` positive bounds, `r` requirements per task with `R_k(t) ≤ B_k`,
`0 < D`) with `m = 3` processors and every resource bound equal to `1`. -/
def WellFormed (i : ResourceConstrainedScheduling.ResourceConstrainedSchedulingInstance) :
    Prop :=
  ResourceConstrainedScheduling.WellFormed i ∧ i.1 = 3 ∧ ∀ b ∈ i.2.2.1, b = 1

open Classical in
/-- RESOURCE CONSTRAINED SCHEDULING with three processors and unit resources as a decision
problem over bitstrings. -/
noncomputable def threeProcessorUnitResourceSchedulingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ResourceConstrainedScheduling.ResourceConstrainedSchedulingInstance) x with
  | some i => decide (WellFormed i ∧
      ResourceConstrainedScheduling.ResourceConstrainedSchedulingFeasible i)
  | none => false

/-- **RESOURCE CONSTRAINED SCHEDULING is NP-complete for three processors and unit resources.**
Source: Błażewicz, Lenstra and Rinnooy Kan (1983); Garey and Johnson (1979), [SS10], [GT11]. -/
public theorem_wanted threeProcessorUnitResourceScheduling_npComplete :
    threeProcessorUnitResourceSchedulingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeProcessorUnitResourceSchedulingDec

end MetaMathlibExt.Complexity.NPComplete.ThreeProcessorUnitResourceScheduling
