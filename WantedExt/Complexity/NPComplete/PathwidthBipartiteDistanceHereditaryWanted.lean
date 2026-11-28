/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATHWIDTH OF BIPARTITE DISTANCE-HEREDITARY GRAPHS is NP-complete

Source:
T. Kloks, H. Bodlaender, H. Müller and D. Kratsch, "Computing treewidth and minimum fill-in: all
you need are the minimal separators", Proc. 1st European Symposium on Algorithms (ESA '93),
Lecture Notes in Computer Science 726, Springer (1993), 260-271, doi:10.1007/3-540-57273-2_61
(the original was not available to us; the result and its attribution are recorded by
Wikipedia, "Pathwidth": determining whether the pathwidth is at most `k` "remains NP-complete when
`G` is restricted to ... bipartite distance-hereditary graphs", citing this paper; R. Mihai and
I. Todinca, "Pathwidth is NP-hard for weighted trees", FAW 2009, LNCS 5598, 181-195,
doi:10.1007/978-3-642-02270-8_20, also credit it with NP-hardness for distance-hereditary
graphs);
E. Howorka, "A characterization of distance-hereditary graphs", Quarterly Journal of
Mathematics 28 (1977), 417-420, doi:10.1093/qmath/28.4.417 (the graph class).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PathwidthBipartiteDistanceHereditaryDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathwidthBipartiteDistanceHereditary

open PathwidthChordalGraphs (PathwidthChordalGraphsInstance Graph IsPathDecomposition
  PathwidthChordalGraphsFeasible)

/-!
# PATHWIDTH OF BIPARTITE DISTANCE-HEREDITARY GRAPHS is NP-complete

INSTANCE: a graph `G = (V, E)` that is bipartite and distance-hereditary, and a positive integer
`K`.
QUESTION: does `G` have pathwidth at most `K`, i.e. is there a path decomposition of `G` (a
sequence of bags covering every vertex and edge, the bags containing any one vertex consecutive)
with every bag of size at most `K + 1`?

This is PATHWIDTH (`PathwidthChordalGraphsWanted`, which states it for chordal graphs) restricted
to bipartite distance-hereditary graphs. The instance type (vertex count, edge list, bound), the
graph (`edgeGraph`), path decompositions (`IsPathDecomposition`) and the question
(`PathwidthChordalGraphsFeasible`, some path decomposition with all bags of size at most `K + 1`)
are reused from that module; only the graph class differs.

Distance-hereditary (Howorka, 1977): every connected induced subgraph preserves distances, i.e.
for every vertex set `S` inducing a connected subgraph (Mathlib's `G.induce S`, `Connected`) and
any two vertices of `S`, their distance in `G[S]` equals their distance in `G` (Mathlib's
`SimpleGraph.dist`); equivalently, every induced path is a shortest path. For a disconnected
graph this says that every connected component is distance-hereditary. Bipartite is Mathlib's
`SimpleGraph.IsBipartite` (2-colorable). Both, and `0 < K` as in the source, are conjuncts of
`WellFormed`, together with the simple-edge-list condition of PATHWIDTH.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PATHWIDTH OF BIPARTITE DISTANCE-HEREDITARY GRAPHS is NP-complete.** Source: Kloks,
Bodlaender, Müller and Kratsch (1993). -/
public theorem_wanted pathwidthBipartiteDistanceHereditary_npComplete :
    pathwidthBipartiteDistanceHereditaryDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pathwidthBipartiteDistanceHereditaryDec

end MetaMathlibExt.Complexity.NPComplete.PathwidthBipartiteDistanceHereditary
