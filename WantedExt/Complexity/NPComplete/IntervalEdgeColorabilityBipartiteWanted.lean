/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTERVAL EDGE-COLORABILITY OF BIPARTITE GRAPHS is NP-complete

Source:
S. V. Sevast'janov, "Interval colorability of the edges of a bipartite graph", Metody
Diskretnogo Analiza 50 (1990), 61-72 (in Russian; not available);
C. J. Casselgren and P. A. Petrosyan, "Improper interval edge colorings of graphs", Discrete
Applied Mathematics 305 (2021), 164-178, doi:10.1016/j.dam.2021.08.038 (Section 1: the definition
of an interval coloring, and "it is an NP-complete problem to determine whether a bipartite graph
has an interval coloring", citing Sevast'janov);
A. S. Asratian and R. R. Kamalian, "Investigation on interval edge-colorings of graphs", Journal
of Combinatorial Theory, Series B 62 (1994), 34-43, doi:10.1006/jctb.1994.1053 (the notion of an
interval edge coloring).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.IntervalEdgeColorabilityBipartiteDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntervalEdgeColorabilityBipartite

/-!
# INTERVAL EDGE-COLORABILITY OF BIPARTITE GRAPHS is NP-complete

INSTANCE: a bipartite graph `G = (V, E)`.
QUESTION: does `G` have an interval coloring, that is, for some `t ≥ 1` a proper edge coloring
with the colors `1, …, t`, each used, such that the colors of the edges incident to each vertex
form a set of consecutive integers?

Casselgren and Petrosyan (Section 1): "A proper `t`-edge coloring of a graph `G` is called an
interval `t`-coloring if the colors of the edges incident to every vertex `v` of `G` form an
interval of integers", a notion due to Asratian and Kamalian, whose interval `t`-colorings use
the colors `1, …, t` and use all of them; deciding whether a bipartite graph has an interval
coloring (an interval `t`-coloring for some `t`) is NP-complete (Sevast'janov 1990, whose paper
was not available). The number `t` of colors is not part of the instance.

The graph is given by an edge list on `Fin n`, and the restriction is Mathlib's
`SimpleGraph.IsBipartite`. A proper edge coloring with `t` colors is a Mathlib coloring of the
line graph `(Graph i).lineGraph.Coloring (Fin t)` (two distinct edges sharing an endpoint get
distinct colors), as in `TotalColoringWanted`; the color `k : Fin t` stands for `k + 1`, and
"each color is used" is surjectivity. "Form an interval" is Mathlib's `Set.OrdConnected` for the
set of colors of the edges at `v` (the order of `Fin t` is that of the integers); a vertex
without edges has the empty set, which imposes no condition. As `t ≥ 1` and every color is used,
a graph without edges has no interval coloring. Membership in NP: every color is used by an edge,
so `t ≤ |E|` and the coloring is a certificate of size polynomial in the length of the edge list;
isolated vertices impose no condition, so the binary vertex count does not make the problem
succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **INTERVAL EDGE-COLORABILITY OF BIPARTITE GRAPHS is NP-complete.** Source: Sevast'janov
(1990), as recorded by Casselgren and Petrosyan (2021). -/
public theorem_wanted intervalEdgeColorabilityBipartite_npComplete :
    intervalEdgeColorabilityBipartiteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L intervalEdgeColorabilityBipartiteDec

end MetaMathlibExt.Complexity.NPComplete.IntervalEdgeColorabilityBipartite
