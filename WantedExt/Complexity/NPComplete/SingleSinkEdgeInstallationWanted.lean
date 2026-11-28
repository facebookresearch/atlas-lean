/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SINGLE-SINK EDGE INSTALLATION is NP-complete

Source:
F. S. Salman, J. Cheriyan, R. Ravi and S. Subramanian, "Approximating the single-sink
link-installation problem in network design", SIAM Journal on Optimization 11 (2001), 595-610,
doi:10.1137/S1052623497321432 (conference version: "Buy-at-bulk network design: approximating
the single-sink edge installation problem", SODA 1997, 619-628);
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), problem MINIMUM SINGLE-SINK EDGE INSTALLATION (decision version);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SingleSinkEdgeInstallationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SingleSinkEdgeInstallation

/-!
# SINGLE-SINK EDGE INSTALLATION is NP-complete

INSTANCE: a graph `G = (V, E)`, a length function `l : E → ℕ`, a set of sources `S ⊆ V`, a sink
`t ∈ V`, a demand function `d : S → ℤ⁺`, a finite set of cable types, each specified by its
capacity and its cost per unit length, and a positive integer `K`.
QUESTION: is there a network of cables in the graph, consisting of an integral number of each
cable type for each edge of `G`, that routes all the demands at the sources to the sink, the
demand of each source following a single path from the source to the sink, whose total cost is
at most `K`?

This is the decision version of the compendium's MINIMUM SINGLE-SINK EDGE INSTALLATION, the
single-sink link-installation (buy-at-bulk) problem of Salman, Cheriyan, Ravi and Subramanian,
who call it NP-hard. The total cost of the network is the sum over the edges `e` of `l(e)`
times the costs per unit length of the cables installed on `e`, and the cables on `e` must
carry the demands of all sources whose path uses `e`. With a single cable type of cost `1`
per unit length and capacity at least the total demand, the least cost of a network is the least
total length of a subgraph connecting `S ∪ {t}`, so the problem contains STEINER TREE IN
GRAPHS ([ND12]).

The vertices are `0, …, n - 1`; the edges are a list of triples `(u, v, l)`, an edge `{u, v}`
of length `l`, whose endpoint pairs form a simple edge list (no loops, no repeated edge in
either orientation, endpoints below `n`); the sources are a list of pairs `(v, d)` of a vertex
`v` with demand `d > 0`, with pairwise distinct vertices; the cable types are a list of pairs
`(u, c)` of a capacity `u > 0` and a cost `c` per unit length. A path from a source to the sink
is a list of distinct vertices that starts at the source, ends at `t`, and joins consecutive
vertices by an edge (`List.IsChain`); a source at the sink takes the one-vertex path `[t]`. A
path uses the edge `{u, v}` when `u` and `v` are consecutive on it, in either order. A network
installs `x(e, c) ∈ ℕ` cables of type `c` on edge `e`; on each edge, the summed demand of the
sources whose path uses the edge is at most the installed capacity `∑_c x(e, c) · u_c`, and the
total cost is `∑_e l(e) · ∑_c x(e, c) · c_c`. `WellFormed` requires `0 < K` (the compendium's
decision versions take a positive integer `K`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SINGLE-SINK EDGE INSTALLATION is NP-complete.** Source: Salman, Cheriyan, Ravi and
Subramanian (2001); Crescenzi and Kann, MINIMUM SINGLE-SINK EDGE INSTALLATION; Garey and Johnson
(1979), [ND12]. -/
public theorem_wanted singleSinkEdgeInstallation_npComplete :
    singleSinkEdgeInstallationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L singleSinkEdgeInstallationDec

end MetaMathlibExt.Complexity.NPComplete.SingleSinkEdgeInstallation
