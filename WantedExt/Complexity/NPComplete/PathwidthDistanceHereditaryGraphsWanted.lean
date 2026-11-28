/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATHWIDTH OF DISTANCE-HEREDITARY GRAPHS is NP-complete

Source:
T. Kloks, H. L. Bodlaender, H. Müller, and D. Kratsch, "Computing treewidth and minimum fill-in:
all you need are the minimal separators", Algorithms - ESA '93, Lecture Notes in Computer Science
726 (1993), 260-271, doi:10.1007/3-540-57273-2_61 (pathwidth is NP-complete on bipartite
distance-hereditary graphs);
I. Adler, M. M. Kanté, and O. Kwon, "Linear rank-width of distance-hereditary graphs I. A
polynomial-time algorithm", Algorithmica 78 (2017), 342-377, doi:10.1007/s00453-016-0164-5,
arXiv:1403.1081 (records that computing the pathwidth of distance-hereditary graphs is NP-hard);
E. Howorka, "A characterization of distance-hereditary graphs", The Quarterly Journal of
Mathematics 28 (1977), 417-420, doi:10.1093/qmath/28.4.417 (the definition).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PathwidthDistanceHereditaryGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathwidthDistanceHereditaryGraphs

open MetaMathlibExt.Complexity.NPComplete.PathwidthChordalGraphs
  (PathwidthChordalGraphsInstance Graph PathwidthChordalGraphsFeasible)

/-!
# PATHWIDTH OF DISTANCE-HEREDITARY GRAPHS is NP-complete

INSTANCE: a distance-hereditary graph `G = (V, E)` and a positive integer `K`.
QUESTION: does `G` have pathwidth at most `K`?

A graph is distance-hereditary (Howorka) if every connected induced subgraph is isometric: for
every set `S` of vertices inducing a connected subgraph and all `u, v ∈ S`, the distance between
`u` and `v` in `G[S]` equals their distance in `G` (Mathlib's `SimpleGraph.induce` and
`SimpleGraph.dist`). Kloks, Bodlaender, Müller, and Kratsch prove that PATHWIDTH is NP-complete on
bipartite distance-hereditary graphs, a subclass, as Adler, Kanté, and Kwon record. Membership in
NP: a path decomposition is a polynomial certificate.

A path decomposition of `G` is a sequence of bags `X 0, …, X (r - 1)` of vertices such that every
vertex lies in some bag, both ends of every edge lie in a common bag, and the bags containing any
one vertex are consecutive; the pathwidth of `G` is at most `K` exactly when some path decomposition
has all bags of size at most `K + 1`. The instance type, the graph, the path decompositions and the
question are reused from `PathwidthChordalGraphsWanted`
(`PathwidthChordalGraphs.PathwidthChordalGraphsInstance`, `PathwidthChordalGraphs.Graph`,
`PathwidthChordalGraphs.IsPathDecomposition`,
`PathwidthChordalGraphs.PathwidthChordalGraphsFeasible`, which says only that the pathwidth is at
most `K`); this module replaces chordality by its own graph class.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PATHWIDTH OF DISTANCE-HEREDITARY GRAPHS is NP-complete.** Source: Kloks, Bodlaender, Müller,
and Kratsch (1993); Adler, Kanté, and Kwon (2017); Howorka (1977). -/
public theorem_wanted pathwidthDistanceHereditaryGraphs_npComplete :
    pathwidthDistanceHereditaryGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pathwidthDistanceHereditaryGraphsDec

end MetaMathlibExt.Complexity.NPComplete.PathwidthDistanceHereditaryGraphs
