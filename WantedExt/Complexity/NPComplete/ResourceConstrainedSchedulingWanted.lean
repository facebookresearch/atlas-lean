/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RESOURCE CONSTRAINED SCHEDULING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS10] RESOURCE CONSTRAINED
SCHEDULING;
M. R. Garey and D. S. Johnson, "Complexity results for multiprocessor scheduling under resource
constraints", SIAM Journal on Computing 4 (1975), 397-411, doi:10.1137/0204035.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ResourceConstrainedSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ResourceConstrainedScheduling

/-!
# RESOURCE CONSTRAINED SCHEDULING is NP-complete

INSTANCE: a set `T` of tasks, each having length `l(t) = 1`, a number `m ∈ ℤ⁺` of processors, a
number `r ∈ ℤ⁺` of resources, resource bounds `B_i ∈ ℤ⁺` (`1 ≤ i ≤ r`), a resource requirement
`R_i(t)` with `0 ≤ R_i(t) ≤ B_i` for each task `t` and resource `i`, and an overall deadline
`D ∈ ℤ⁺`. QUESTION: is there an `m`-processor schedule `σ` for `T` that meets the overall deadline
`D` and obeys the resource constraints, i.e., such that for all `u ≥ 0`, if `S(u)` is the set of
all `t ∈ T` for which `σ(t) ≤ u < σ(t) + l(t)`, then for each resource `i` the sum of `R_i(t)` over
all `t ∈ S(u)` is at most `B_i`?

An `m`-processor schedule is a start time `σ(t) ∈ ℤ₀⁺` for each task such that at every time `u`
at most `m` tasks run (`|S(u)| ≤ m`); it meets the deadline when `σ(t) + l(t) ≤ D` for all `t`.
Tasks are `Fin n`, one per row of the requirement table; resources are `Fin r`. Binary encoding
of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **RESOURCE CONSTRAINED SCHEDULING is NP-complete.** Source: Garey and Johnson (1979),
[SS10]; Garey and Johnson (1975). -/
public theorem_wanted resourceConstrainedScheduling_npComplete :
    resourceConstrainedSchedulingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L resourceConstrainedSchedulingDec

end MetaMathlibExt.Complexity.NPComplete.ResourceConstrainedScheduling
