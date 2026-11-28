/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EPT GRAPH RECOGNITION is NP-complete

Source:
M. C. Golumbic and R. E. Jamison, "Edge and vertex intersection of paths in a tree", Discrete
Mathematics 55 (1985), 151-159, doi:10.1016/0012-365X(85)90043-3;
A. Boyacı, T. Ekim, M. Shalom and S. Zaks, "Graphs of edge-intersecting non-splitting paths in a
tree: representations of holes, Part I", arXiv:1309.2898, Section 1.2 ("it is shown that EPT
graph recognition is NP-complete", citing Golumbic and Jamison, Discrete Mathematics 55);
L. Alcón, M. Gutierrez and M. P. Mazzoleni, "Helly EPT graphs on bounded degree trees:
forbidden induced subgraphs and efficient recognition", arXiv:1604.08775, Section 2 (the
definition of an EPT representation used below).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.EptGraphRecognitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EptGraphRecognition

/-!
# EPT GRAPH RECOGNITION is NP-complete

INSTANCE: a graph `G = (V, E)`. QUESTION: is `G` an EPT graph, i.e. the edge intersection graph
of a family of paths in a tree?

Following Alcón, Gutierrez and Mazzoleni (Section 2): "An EPT representation of `G` is a pair
`⟨P, T⟩` where `P` is a family `(P_v)_{v ∈ V(G)}` of subpaths of the host tree `T` satisfying
that two vertices `v` and `w` of `G` are adjacent if and only if `E(P_v) ∩ E(P_w) ≠ ∅`", and `G`
is EPT if it has an EPT representation. Golumbic and Jamison proved that recognizing EPT graphs
is NP-complete (as recorded by Boyacı, Ekim, Shalom and Zaks, Section 1.2).

The graph is given by an edge list on `Fin n`. The host tree is a Mathlib `SimpleGraph` on
`Fin m` nodes for some `m` (`SimpleGraph.IsTree`); the subpath `P_v` is a walk of `T` between
two nodes that is a path (`SimpleGraph.Walk.IsPath`), and `E(P_v)` is its edge list
`(P v).edges`. Adjacency is required for distinct vertices `v ≠ w` (the graph has no loops). A
path may be a single node, with no edges; such a vertex is isolated, and an isolated vertex can
equally be given a new pendant edge of the tree, so allowing these paths does not change the
class. For the same reason isolated vertices do not change the answer, so the binary vertex
count does not make the problem succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **EPT GRAPH RECOGNITION is NP-complete.** Source: Golumbic and Jamison (1985); Boyacı, Ekim,
Shalom and Zaks, Section 1.2. -/
public theorem_wanted eptGraphRecognition_npComplete :
    eptGraphRecognitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L eptGraphRecognitionDec

end MetaMathlibExt.Complexity.NPComplete.EptGraphRecognition
