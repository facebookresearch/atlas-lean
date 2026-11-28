/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MONOPOLAR GRAPH RECOGNITION is NP-complete

Source:
A. Farrugia, "Vertex-partitioning into fixed additive induced-hereditary properties is
NP-hard", Electronic Journal of Combinatorics 11 (2004), #R46, doi:10.37236/1799
(arXiv:math/0306158; Theorem 2);
ISGCI (https://www.graphclasses.org/classes/gc_1272.html), class monopolar, problem
"Recognition": NP-complete, citing Farrugia.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MonopolarGraphRecognitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MonopolarGraphRecognition

/-!
# MONOPOLAR GRAPH RECOGNITION is NP-complete

INSTANCE: a graph `G = (V, E)`. QUESTION: is `G` monopolar, i.e., can `V` be partitioned into
sets `A` and `B` such that `G[A]` is edgeless and every connected component of `G[B]` is a
complete graph?

ISGCI (class `gc_1272`): "A monopolar graph is a graph `G` whose vertex set can be partitioned
into two sets `A` and `B`, such that `G[A]` is independent and the connected components of `G[B]`
are complete graphs." Monopolarity is the repository's existing predicate
`ThreeColorabilityMonopolar.IsMonopolar`: some vertex set `A` is independent (Mathlib's
`SimpleGraph.IsIndepSet`) and its complement induces a cluster graph
(`ClusterDeletion.IsClusterGraph`: any two distinct vertices joined by a walk are adjacent).
Either part may be empty.

Farrugia's Theorem 2: for additive induced-hereditary graph properties `P` and `Q` (closed under
vertex-disjoint unions and induced subgraphs) with `P ∘ Q` other than the bipartite graphs,
recognizing `P ∘ Q` (graphs whose vertices split into a part inducing a graph in `P` and a part
inducing a graph in `Q`) is NP-hard, and NP-complete when `P`- and `Q`-recognition are in NP.
Monopolar graphs are `P ∘ Q` for `P` the edgeless graphs and `Q` the disjoint unions of
complete graphs; both properties are additive, induced-hereditary and recognizable in polynomial
time, and the triangle is monopolar but not bipartite.

The graph is simple and given by an edge list on `Fin n`. Isolated vertices do not change the
answer (they can join `A`), so the binary vertex count does not make the problem succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MONOPOLAR GRAPH RECOGNITION is NP-complete.** Source: Farrugia (2004), Theorem 2; ISGCI,
class `gc_1272`. -/
public theorem_wanted monopolarGraphRecognition_npComplete :
    monopolarGraphRecognitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L monopolarGraphRecognitionDec

end MetaMathlibExt.Complexity.NPComplete.MonopolarGraphRecognition
