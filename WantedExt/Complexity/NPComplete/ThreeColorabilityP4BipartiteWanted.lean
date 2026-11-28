/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-COLORABILITY OF P_4-BIPARTITE GRAPHS is NP-complete

Source:
M. Barbato and D. Bezzi, "Monopolar graphs: complexity of computing classical graph
parameters", Discrete Applied Mathematics 291 (2021), 277-285, doi:10.1016/j.dam.2020.12.023
(Section 2.1, Proposition 2.8 in the authors' version: "The 3-Colorability problem on monopolar
graphs is NP-complete."; monopolar graphs are `P_4`-bipartite);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (the parent
problem);
ISGCI, *Information System on Graph Classes and their Inclusions*, class "`P_4`-bipartite" (gc_5),
problem 3-Colourability: NP-complete, recording "NP-complete on monopolar" with the reference to
Barbato and Bezzi (2021).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ThreeColorabilityP4BipartiteDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityP4Bipartite

open GraphColoring (GraphColoringInstance Graph GraphColoringFeasible)

/-!
# 3-COLORABILITY OF P_4-BIPARTITE GRAPHS is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` that is `P_4`-bipartite. QUESTION: is
`G` properly 3-colorable, i.e., is there a map `c : V → {1, 2, 3}` with `c(u) ≠ c(v)` for every
edge `uv`?

This is GRAPH COLORING (`GraphColoringWanted`, [GT4]) with the bound fixed to `K = 3`, restricted
to `P_4`-bipartite graphs. ISGCI: "A graph is `P_4`-bipartite if its vertex set can be
partitioned in two subsets, each of which induces a `P_4`-free graph." The parts are a set `A`
and its complement `Aᶜ` (either may be empty), the induced subgraphs Mathlib's `G.induce A` and
`G.induce Aᶜ`, and `P_4`-free means no induced path on four vertices (Mathlib's
`(SimpleGraph.pathGraph 4).IsIndContained` fails), as in `AchromaticNumberCographsWanted`.

Barbato and Bezzi prove 3-colorability NP-complete on monopolar graphs, those whose vertex set
splits into a stable set and a set inducing a union of vertex-disjoint cliques. Both parts of
such a split are `P_4`-free: an induced subgraph of a stable set has no edge, and an induced
subgraph of a union of vertex-disjoint cliques is again one, while a path on four vertices has an
edge and is connected but not complete. So every monopolar graph is `P_4`-bipartite, and
3-colorability is NP-hard on `P_4`-bipartite graphs (ISGCI records it for this class as
"NP-complete on monopolar"). Membership in NP holds for all graphs.

The instance type is a vertex count and an edge list; `withThreeColors` pairs it with the bound
`3` to reuse GRAPH COLORING's graph (`Graph`, a simple graph on `Fin n`), well-formedness
(simple edge list) and question (`Colorable 3`), as in `ThreeColorabilityDiameterThreeWanted`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **3-COLORABILITY OF P_4-BIPARTITE GRAPHS is NP-complete.** Source: Barbato and Bezzi (2021), via
monopolar graphs; Garey and Johnson (1979), [GT4] (parent problem); ISGCI, class
"`P_4`-bipartite". -/
public theorem_wanted threeColorabilityP4Bipartite_npComplete :
    threeColorabilityP4BipartiteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeColorabilityP4BipartiteDec

end MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityP4Bipartite
