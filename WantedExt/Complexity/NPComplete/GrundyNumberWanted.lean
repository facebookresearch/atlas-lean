/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRUNDY NUMBER is NP-complete

Source:
M. Zaker, "Results on the Grundy chromatic number of graphs", Discrete Mathematics 306 (2006),
3166-3173, doi:10.1016/j.disc.2005.06.044 (Grundy colorings and `Γ(G)`; deciding `Γ(G) ≥ k` is
NP-complete, even for complements of bipartite graphs).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GrundyNumberDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GrundyNumber

open GraphColoring (GraphColoringInstance Graph)

/-!
# GRUNDY NUMBER is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` and a positive integer `K`.
QUESTION: is the Grundy (chromatic) number `Γ(G)` at least `K`?

Following Zaker (2006), a Grundy `k`-coloring of `G` is a proper `k`-vertex coloring of `G` such
that for each two colors `i < j`, every vertex of color `j` has a neighbor of color `i`; `Γ(G)` is
the maximum `k` for which a Grundy `k`-coloring exists, equivalently the maximum number of colors
the first-fit greedy coloring uses over all orderings of `V`. Zaker proves that deciding
`Γ(G) ≥ K` is NP-complete even for complements of bipartite graphs; this is the problem on all
graphs, which contains that class, and membership in NP holds for all graphs (a Grundy coloring is
a certificate, and `Γ(G) ≤ |V|`).

The colors are `1, …, k`; a `k`-coloring uses every one of them (`IsGrundyColoring`), and
properness is Mathlib's `SimpleGraph.Coloring`. The instance type (vertex count, simple edge list,
bound `K`), the graph and the well-formedness of the edge list are those of GRAPH K-COLORABILITY
(`GraphColoringWanted`), reused unchanged; `WellFormed` adds `0 < K`. Numbers use the binary
encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GRUNDY NUMBER is NP-complete.** Source: Zaker (2006). -/
public theorem_wanted grundyNumber_npComplete :
    grundyNumberDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L grundyNumberDec

end MetaMathlibExt.Complexity.NPComplete.GrundyNumber
