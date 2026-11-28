/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CATERPILLAR ARBORICITY AT MOST 2 is NP-complete

Source:
T. C. Shermer, "On rectangle visibility graphs III. External visibility and complexity",
Proceedings of the 8th Canadian Conference on Computational Geometry (CCCG '96), Ottawa (1996),
234-239 (Section 1: definitions of caterpillars, caterpillar forests and caterpillar arboricity;
Theorem 3.2: "Caterpillar Arboricity 2 is NP-complete");
ISGCI (Information System on Graph Classes and their Inclusions), class "caterpillar
arboricity <= 2" (gc_732), problem Recognition, NP-complete, citing Shermer.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CaterpillarArboricityTwoDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CaterpillarArboricityTwo

/-!
# CATERPILLAR ARBORICITY AT MOST 2 is NP-complete

INSTANCE: a graph `G = (V, E)`. QUESTION: is the caterpillar arboricity of `G` at most `2`, that
is, can `G` be decomposed into at most two caterpillar forests?

Shermer (Section 1): "A caterpillar is a tree containing a simple path `P(a, b)` such that every
vertex not on `P(a, b)` is distance one from `P(a, b)`. A caterpillar forest is a forest, where
each tree of the forest is a caterpillar." The caterpillar arboricity of `G` is "the minimum `k`
such that the graph can be decomposed into `k` … caterpillar forests". ISGCI (gc_732): "A graph
has caterpillar arboricity <= 2 if it can be decomposed into (is the union of) at most 2 forests
whose connected components are caterpillar[s]". Shermer's Theorem 3.2 calls the problem
"determining if a given graph has caterpillar arboricity 2" (in NP, NP-hardness by reduction
from LINEAR ARBORICITY 2). Whether a graph is a caterpillar forest (caterpillar arboricity at
most `1`) is decidable in polynomial time, so "exactly 2" and "at most 2" (ISGCI's class, stated
here) are polynomially equivalent questions.

`IsCaterpillarForest H`: `H` is acyclic (Mathlib's `SimpleGraph.IsAcyclic`, a forest), and every
connected component `c` (Mathlib's `SimpleGraph.ConnectedComponent`, whose induced subgraph is a
tree of the forest) contains a path `p` (a walk with `SimpleGraph.Walk.IsPath`) such that every
vertex of `c` is on `p` or adjacent to a vertex of `p`. The path lies in `c`, since `c` is
nonempty and its vertices are on or next to `p`. The decomposition is two spanning subgraphs
`H₁, H₂` of `G` with disjoint edge sets (`Disjoint H₁ H₂`) whose union is `G` (`H₁ ⊔ H₂ = G`);
"at most 2" allows `H₂ = ⊥`, the edgeless graph, which is a caterpillar forest. The graph is
given by an edge list on `Fin n` (`Cslib.Complexity.Karp.edgeGraph`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CATERPILLAR ARBORICITY AT MOST 2 is NP-complete.** Source: Shermer (1996), Theorem 3.2;
ISGCI gc_732. -/
public theorem_wanted caterpillarArboricityTwo_npComplete :
    caterpillarArboricityTwoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L caterpillarArboricityTwoDec

end MetaMathlibExt.Complexity.NPComplete.CaterpillarArboricityTwo
