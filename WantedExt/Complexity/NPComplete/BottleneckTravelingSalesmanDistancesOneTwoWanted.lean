/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BOTTLENECK TRAVELING SALESMAN with distances 1 and 2 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND24] BOTTLENECK TRAVELING SALESMAN,
comment;
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations*, Plenum (1972), 85-103, doi:10.1007/978-1-4684-2001-2_9 (HAMILTONIAN CIRCUIT).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.BottleneckTravelingSalesmanDistancesOneTwoDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BottleneckTravelingSalesmanDistancesOneTwo

/-!
# BOTTLENECK TRAVELING SALESMAN with distances 1 and 2 is NP-complete

INSTANCE: a set `C` of `m` cities, a distance `d(cᵢ, cⱼ) ∈ {1, 2}` for each pair of distinct
cities, and a positive integer `B`. QUESTION: is there a tour of `C` whose longest edge is no
longer than `B`, i.e., a permutation `⟨c_π(1), ..., c_π(m)⟩` of `C` with
`d(c_π(i), c_π(i+1)) ≤ B` for `1 ≤ i < m` and `d(c_π(m), c_π(1)) ≤ B`?

This is BOTTLENECK TRAVELING SALESMAN
(`CSLibExt.Complexity.NPComplete.BottleneckTravelingSalesmanDefs`, Garey and Johnson [ND24])
restricted as in the [ND24] comment: "Remains NP-complete even if `d(cᵢ, cⱼ) ∈ {1,2}` for all
`cᵢ, cⱼ ∈ C`." Garey and Johnson give no separate reference: the entry's transformation from
HAMILTONIAN CIRCUIT (NP-complete by Karp (1972)) already yields such instances, with distance
`1` between adjacent and `2` between non-adjacent vertices and `B = 1`, so that a tour has
longest edge at most `1` exactly when it is a Hamiltonian circuit of the graph. (For `B ≥ 2`
every instance is a yes-instance.)

The instance (city count `m`, distance matrix, bound), `BottleneckTravelingSalesman.WellFormed`
(`0 < m`, a symmetric `m × m` matrix with zero diagonal and positive off-diagonal entries,
`0 < B`) and `BottleneckTravelingSalesman.BottleneckTravelingSalesmanFeasible` are reused
unchanged; the restriction adds to well-formedness that the distance between distinct cities is
`1` or `2`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open BottleneckTravelingSalesman (BottleneckTravelingSalesmanInstance dist)

/-- **BOTTLENECK TRAVELING SALESMAN is NP-complete with distances 1 and 2.** Source: Garey and
Johnson (1979), [ND24], comment. -/
public theorem_wanted bottleneckTravelingSalesmanDistancesOneTwo_npComplete :
    bottleneckTravelingSalesmanDistancesOneTwoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L bottleneckTravelingSalesmanDistancesOneTwoDec

end MetaMathlibExt.Complexity.NPComplete.BottleneckTravelingSalesmanDistancesOneTwo
