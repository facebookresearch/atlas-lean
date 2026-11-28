/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONNECTED DOMINATING SET on bipartite graphs is NP-complete

Source:
H. Müller and A. Brandstädt, "The NP-completeness of Steiner tree and dominating set for chordal
bipartite graphs", Theoretical Computer Science 53 (1987), 257-265,
doi:10.1016/0304-3975(87)90067-3 (connected domination is NP-complete for chordal bipartite
graphs, as recorded by T. Liu, Z. Lu and K. Xu, "Tractable connected domination for restricted
bipartite graphs", Journal of Combinatorial Optimization 29 (2015), 247-256,
doi:10.1007/s10878-014-9729-x);
J. Pfaff, R. Laskar and S. T. Hedetniemi, "NP-completeness of total and connected domination and
irredundance for bipartite graphs", Technical Report 428, Department of Mathematical Sciences,
Clemson University (1983) (the bipartite case; the report was not available);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), CONNECTED DOMINATING SET.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ConnectedDominatingSetBipartiteDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConnectedDominatingSetBipartite

open MetaMathlibExt.Complexity.NPComplete.ConnectedDominatingSet
  (ConnectedDominatingSetInstance Graph ConnectedDominatingSetFeasible)

/-!
# CONNECTED DOMINATING SET on bipartite graphs is NP-complete

INSTANCE: a bipartite graph `G = (V, E)` and a positive integer `K ≤ |V|`.
QUESTION: is there a dominating set `V' ⊆ V` with `|V'| ≤ K` (every vertex not in `V'` has a
neighbor in `V'`) such that the subgraph `G[V']` induced by `V'` is connected?

This is CONNECTED DOMINATING SET (`ConnectedDominatingSetWanted`) restricted to bipartite graphs.
The instance type, the graph and the question are the parent's
(`ConnectedDominatingSet.ConnectedDominatingSetInstance`, `ConnectedDominatingSet.Graph`,
`ConnectedDominatingSet.ConnectedDominatingSetFeasible`: a simple graph on `Fin n` given by an
edge list, and a set `S` of at most `K` vertices that dominates `G` and induces a connected
subgraph). `WellFormed` is the parent's plus the restriction, Mathlib's
`SimpleGraph.IsBipartite` (`Colorable 2`: the vertices split into two sets with every edge
between them), and Garey and Johnson's bounds `0 < K ≤ |V|`.

Hardness: Müller and Brandstädt (1987) prove connected domination NP-complete already for
chordal bipartite graphs, which are bipartite; the bipartite case is credited to the technical
report of Pfaff, Laskar and Hedetniemi (1983). Membership in NP: the certificate is `S`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CONNECTED DOMINATING SET on bipartite graphs is NP-complete.** Source: Müller and
Brandstädt (1987); Pfaff, Laskar and Hedetniemi (1983). -/
public theorem_wanted connectedDominatingSetBipartite_npComplete :
    connectedDominatingSetBipartiteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L connectedDominatingSetBipartiteDec

end MetaMathlibExt.Complexity.NPComplete.ConnectedDominatingSetBipartite
