/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM SUBFOREST is NP-complete

Source:
R. Shamir and D. Tsur, "The maximum subforest problem: approximation and exact algorithms",
Proceedings of the Ninth Annual ACM-SIAM Symposium on Discrete Algorithms (SODA 1998), 394-399,
doi:10.5555/314613.314769 (Section 1: the maximum subforest problem MSP; Section 1.1: "We show
that MSP is NP-hard");
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, entry MAXIMUM
SUBFOREST;
A. Abboud, A. Backurs, T. D. Hansen, V. Vassilevska Williams and O. Zamir, "Subtree isomorphism
revisited", ACM Transactions on Algorithms 14(3) (2018), 1-23, doi:10.1145/3093239 (subtree
isomorphism, used for membership in NP).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MaximumSubforestDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumSubforest

open InducedSubgraphWithPropertyPi (SimpleEdgeList)

/-!
# MAXIMUM SUBFOREST is NP-complete

INSTANCE: a tree `G = (V, E)`, a set `H` of trees, and a positive integer `K`.
QUESTION: is there a subset `E' ⊆ E` with `|E'| ≥ K` such that the subgraph `G' = (V, E')`
does not contain any subtree isomorphic to a tree from `H`?

This is the decision version of Shamir and Tsur's maximum subforest problem ("Given a tree `G`
and a set of trees `H`, find a subgraph `G'` of `G` such that `G'` does not contain a subtree
isomorphic to a tree from `H`, and the number of edges in `G'` is maximum"), in the form of the
Crescenzi-Kann compendium entry MAXIMUM SUBFOREST. Shamir and Tsur write `T ⊆ G'` when the tree
`T` is isomorphic to a subgraph of `G'`, and call `G'` `H`-free when no tree of `H` is; since a
tree's copy in `G'` is a subtree of `G'`, this is Mathlib's `SimpleGraph.Free`: `T.Free G'` says
that `G'` contains no copy of `T` (`SimpleGraph.Copy`, an injective edge-preserving map).
Shamir and Tsur show that MSP is NP-hard (Section 1.1). Membership in NP: the edge set `E'` is a
certificate, and whether a tree occurs in a tree (subtree isomorphism; see Abboud et al.) is
decided in polynomial time, so `H`-freeness of each component of `G'` is checked in polynomial
time.

Graphs are given by vertex counts and simple edge lists
(`InducedSubgraphWithPropertyPi.SimpleEdgeList`), as `Cslib.Complexity.Karp.edgeGraph` on
`Fin n`; trees are Mathlib's `SimpleGraph.IsTree` (connected, which needs a vertex, and
acyclic). `H` is a list of trees `(m, edges)`. The subset `E'` is a sublist of the edge list of
`G`, which has no duplicates, so its length is `|E'|`. The vertex counts are binary numbers, but
a tree has one vertex more than edges, so they are bounded by the input length. `K` uses the
canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MAXIMUM SUBFOREST is NP-complete.** Source: Shamir and Tsur (1998), Section 1.1
(hardness); membership in NP as in the module docstring. -/
public theorem_wanted maximumSubforest_npComplete :
    maximumSubforestDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumSubforestDec

end MetaMathlibExt.Complexity.NPComplete.MaximumSubforest
