/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH INFERENCE FROM A WALK FOR TREES OF DEGREE AT MOST 3 is NP-complete

Source:
O. Maruyama and S. Miyano, "Graph inference from a walk for trees of bounded degree 3 is
NP-complete", in *Mathematical Foundations of Computer Science 1995*, Lecture Notes in Computer
Science 969, Springer (1995), 257-266, doi:10.1007/3-540-60246-1_132 (Theorem 1; full version:
RIFIS Technical Report 94, Kyushu University (1994), https://hdl.handle.net/2324/3076);
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MINIMUM GRAPH INFERENCE.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GraphInferenceDegreeThreeTreesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphInferenceDegreeThreeTrees

/-!
# GRAPH INFERENCE FROM A WALK FOR TREES OF DEGREE AT MOST 3 is NP-complete

INSTANCE: a string `x` over a finite alphabet `Σ`, and a positive integer `K`.
QUESTION: is there a tree `G` of bounded degree 3 with at most `K` edges, together with an
edge-coloring `c : E → Σ`, that realizes a walk for `x`, that is, a walk in `G` that traverses
every edge of `G` and whose sequence of edge colors is `x`?

This is GIW(3-Deg-Tree) of Maruyama and Miyano: "Instance: A string x over a finite alphabet
Σ, and a positive integer K. Problem: Is there a graph G in C with at most K edges such that G
realizes a walk for x?", for `C` the class of trees of bounded degree 3 (their Theorem 1).
Their graphs are undirected edge-colored graphs `G = (V, E, c)` with `c : E → Σ`; a partial walk
is a walk in the graph (vertices and edges may repeat), it is a walk when it contains all the
edges, and its trace is the string of colors of the traversed edges.

Colors are natural numbers, so `x : List ℕ` and the alphabet is the finite set of symbols of
`x`. The tree is a `SimpleGraph (Fin m)` with `SimpleGraph.IsTree` and every vertex of degree at
most `3`; the coloring is a function on unordered vertex pairs, of which only the values on
edges matter. The walk is a Mathlib `SimpleGraph.Walk` from any vertex to any vertex. The number
of edges is `Set.ncard` of the edge set.

The Crescenzi-Kann entry ("a simple path in G such that the string of colors traversed in the
path is equal to x", for a class `C` given in the instance) cites this paper; the statement here
follows the paper, whose walks traverse every edge and whose class is fixed.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GRAPH INFERENCE FROM A WALK FOR TREES OF DEGREE AT MOST 3 is NP-complete.** Source:
Maruyama and Miyano (1995), Theorem 1; Crescenzi and Kann, MINIMUM GRAPH INFERENCE. -/
public theorem_wanted graphInferenceDegreeThreeTrees_npComplete :
    graphInferenceDegreeThreeTreesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L graphInferenceDegreeThreeTreesDec

end MetaMathlibExt.Complexity.NPComplete.GraphInferenceDegreeThreeTrees
