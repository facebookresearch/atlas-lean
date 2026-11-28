/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM WEIGHT AND/OR GRAPH SOLUTION with unit weights is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MS16] MINIMUM WEIGHT
AND/OR GRAPH SOLUTION (p. 283), comment "Remains NP-complete even if w(a) = 1 for all a ∈ A"
(credited there to Garey and Johnson, unpublished).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinimumWeightAndOrGraphSolutionUnitWeightsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumWeightAndOrGraphSolutionUnitWeights

open MetaMathlibExt.Complexity.NPComplete.MinimumWeightAndOrGraphSolution
  (MinimumWeightAndOrGraphSolutionInstance)

/-!
# MINIMUM WEIGHT AND/OR GRAPH SOLUTION with unit weights is NP-complete

INSTANCE: a directed acyclic graph `G = (V, A)` with a single vertex `s ∈ V` of in-degree `0`,
an assignment `f(v) ∈ {and, or}` for each `v ∈ V` of nonzero out-degree, the weight `w(a) = 1`
for each `a ∈ A`, and a positive integer `K`. QUESTION: is there a subgraph `G' = (V', A')` of
`G` such that `s ∈ V'`, such that if `v ∈ V'` and `f(v) = and` then every arc leaving `v`
belongs to `A'`, such that if `v ∈ V'` and `f(v) = or` then at least one arc leaving `v`
belongs to `A'`, and such that `A'` has at most `K` arcs?

This is the restriction of MINIMUM WEIGHT AND/OR GRAPH SOLUTION ([MS16],
`MinimumWeightAndOrGraphSolutionWanted`) to instances in which every arc weight is `1`, so the
weight of `A'` is its number of arcs. The instance type,
`MinimumWeightAndOrGraphSolution.WellFormed` and
`MinimumWeightAndOrGraphSolution.MinimumWeightAndOrGraphSolutionFeasible` are the parent's,
unchanged; `WellFormed` adds the unit-weight condition on the arc records. Garey and Johnson
record that the general problem is solvable in polynomial time for rooted directed trees.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM WEIGHT AND/OR GRAPH SOLUTION is NP-complete with unit weights.** Source: Garey
and Johnson (1979), [MS16], comment (Garey and Johnson, unpublished). -/
public theorem_wanted minimumWeightAndOrGraphSolutionUnitWeights_npComplete :
    minimumWeightAndOrGraphSolutionUnitWeightsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumWeightAndOrGraphSolutionUnitWeightsDec

end MetaMathlibExt.Complexity.NPComplete.MinimumWeightAndOrGraphSolutionUnitWeights
