/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM WEIGHT AND/OR GRAPH SOLUTION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MS16] MINIMUM WEIGHT
AND/OR GRAPH SOLUTION;
S. Sahni, "Computationally related problems", SIAM Journal on Computing 3 (1974),
262-279, doi:10.1137/0203021.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinimumWeightAndOrGraphSolutionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumWeightAndOrGraphSolution

/-!
# MINIMUM WEIGHT AND/OR GRAPH SOLUTION is NP-complete

INSTANCE: a directed acyclic graph `G = (V, A)` with a single vertex `s ∈ V` of in-degree `0`,
an assignment `f(v) ∈ {and, or}` for each `v ∈ V` of nonzero out-degree, a weight
`w(a) ∈ ℤ⁺` for each `a ∈ A`, and a positive integer `K`. QUESTION: is there a subgraph
`G' = (V', A')` of `G` such that `s ∈ V'`, such that if `v ∈ V'` and `f(v) = and` then every arc
leaving `v` belongs to `A'`, such that if `v ∈ V'` and `f(v) = or` then at least one arc leaving
`v` belongs to `A'`, and such that the total weight of the arcs in `A'` is at most `K`?

Vertices are `0, ..., n - 1`. Arcs are listed as `(tail, head, weight)` with distinct
`(tail, head)` pairs and are referred to by their position in the list; `A'` is a set of
positions. `f` is listed for every vertex (`true` for and, `false` for or) and is read only at
vertices with an outgoing arc. Acyclicity is the existence of a height function that increases
along every arc. Weights are natural numbers in binary.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM WEIGHT AND/OR GRAPH SOLUTION is NP-complete.** Source: Garey and Johnson (1979),
[MS16]; Sahni (1974). -/
public theorem_wanted minimumWeightAndOrGraphSolution_npComplete :
    minimumWeightAndOrGraphSolutionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumWeightAndOrGraphSolutionDec

end MetaMathlibExt.Complexity.NPComplete.MinimumWeightAndOrGraphSolution
