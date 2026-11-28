/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH K-COLORABILITY of circle graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY
(CHROMATIC NUMBER), p. 191 (comment: "For arbitrary `K`, the problem is NP-complete for circle
graphs and circular arc graphs (even given their representation as families of arcs)");
M. R. Garey, D. S. Johnson, G. L. Miller and C. H. Papadimitriou, "The complexity of coloring
circular arcs and chords", SIAM Journal on Algebraic and Discrete Methods 1 (1980), 216-227,
doi:10.1137/0601025.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GraphColoringCircleGraphDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoringCircleGraph

open MetaMathlibExt.Complexity.NPComplete.DominatingSetCircleGraph (circleGraph)

/-!
# GRAPH K-COLORABILITY of circle graphs is NP-complete

INSTANCE: a circle graph `G = (V, E)`, given by a chord model (a family of chords of a circle,
one per vertex, two vertices adjacent when their chords intersect), and a positive integer
`K ≤ |V|`.
QUESTION: is `G` `K`-colorable, i.e., is there a function `f : V → {1, 2, ..., K}` such that
`f(u) ≠ f(v)` whenever `{u, v} ∈ E`?

This is GRAPH K-COLORABILITY ([GT4], `GraphColoringWanted`) restricted to circle graphs, with
`K` part of the input. Garey, Johnson, Miller and Papadimitriou prove that the circle graph
coloring problem is NP-complete, and Garey and Johnson record the result for arbitrary `K`. The
problems with `K` fixed are different problems and are not stated here.

The chord model and the circle graph are those of
`WantedExt.Complexity.NPComplete.DominatingSetCircleGraphWanted`, also used by
`PartitionIntoCliquesCircleGraphWanted`: a chord is given by its two endpoints, natural numbers
`a < b` naming points in clockwise order on the circle; the endpoints of all chords are
distinct; `DominatingSetCircleGraph.circleGraph` joins two chords when their endpoints
interleave (`a < c < b < d`, symmetrized by `SimpleGraph.fromRel`), which for distinct endpoints
is exactly when they intersect. Every circle graph has such a model. The bound `0 < K ≤ |V|` is
the instance class of [GT4]. `K`-colorability is Mathlib's `SimpleGraph.Colorable`, as in
`GraphColoring.GraphColoringFeasible`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GRAPH K-COLORABILITY of circle graphs is NP-complete.** Source: Garey and Johnson (1979),
[GT4], comment; Garey, Johnson, Miller and Papadimitriou (1980). -/
public theorem_wanted graphColoringCircleGraph_npComplete :
    graphColoringCircleGraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L graphColoringCircleGraphDec

end MetaMathlibExt.Complexity.NPComplete.GraphColoringCircleGraph
