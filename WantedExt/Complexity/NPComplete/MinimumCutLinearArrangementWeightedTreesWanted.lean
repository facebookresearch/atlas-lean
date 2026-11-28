/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM CUT LINEAR ARRANGEMENT on edge-weighted trees is NP-complete

Source:
B. Monien and I. H. Sudborough, "Min cut is NP-complete for edge weighted trees", Theoretical
Computer Science 58(1-3) (1988), 209-229, doi:10.1016/0304-3975(88)90028-X;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT44] MINIMUM CUT LINEAR ARRANGEMENT.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinimumCutLinearArrangementWeightedTreesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangementWeightedTrees

/-!
# MINIMUM CUT LINEAR ARRANGEMENT on edge-weighted trees is NP-complete

INSTANCE: a tree `T = (V, E)`, edge weights `w : E → ℤ⁺`, and a positive integer `K`.
QUESTION: is there a one-to-one function `f : V → {1, 2, …, |V|}` such that for every `i`, the
total weight of the edges `{u, v}` with `f(u) ≤ i < f(v)` is at most `K`?

This is [GT44] MINIMUM CUT LINEAR ARRANGEMENT (stated without weights in
`WantedExt.Complexity.NPComplete.MinimumCutLinearArrangementWanted`) on trees, with each edge
counted with its weight. Vertices are `0, …, n - 1` and the tree is given by a list of weighted
edges, its graph being `Cslib.Complexity.Karp.edgeGraph` and treeness Mathlib's
`SimpleGraph.IsTree` (connected and acyclic). The numbering `f` is given, as in
`MinimumCutLinearArrangementWanted`, by the positions in a permutation of `0, …, n - 1`.
Monien and Sudborough prove NP-completeness even when the weights are bounded by a polynomial in
`|V|`, so the problem is NP-complete in the strong sense; weights use the canonical binary
encoding. For unweighted trees (all weights `1`) the problem is solvable in polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM CUT LINEAR ARRANGEMENT on edge-weighted trees is NP-complete.** Source: Monien and
Sudborough (1988). -/
public theorem_wanted minimumCutLinearArrangementWeightedTrees_npComplete :
    minimumCutLinearArrangementWeightedTreesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumCutLinearArrangementWeightedTreesDec

end MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangementWeightedTrees
