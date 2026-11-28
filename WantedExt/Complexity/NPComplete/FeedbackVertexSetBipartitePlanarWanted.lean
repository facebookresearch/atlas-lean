/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET on planar bipartite graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT7] FEEDBACK VERTEX SET, the problem
restricted here;
A. Takaoka, S. Tayu and S. Ueno, "On minimum feedback vertex sets in bipartite graphs and
degree-constraint graphs", IEICE Transactions on Information and Systems E96-D(11) (2013),
2327-2332, doi:10.1587/transinf.E96.D.2327, Theorem 2 (conference version: "On minimum feedback
vertex sets in graphs", Third International Conference on Networking and Computing (ICNC 2012),
429-434, doi:10.1109/ICNC.2012.81).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.FeedbackVertexSetBipartitePlanarDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetBipartitePlanar

open MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSet

/-!
# FEEDBACK VERTEX SET on planar bipartite graphs is NP-complete

INSTANCE: a planar bipartite graph `G = (V, E)` (finite, simple, undirected) and a nonnegative
integer `K`.
QUESTION: is there a set `V' ⊆ V` with `|V'| ≤ K` such that `G - V'` is a forest, that is,
`V'` meets every cycle of `G`?

This is FEEDBACK VERTEX SET on bipartite graphs
(`WantedExt.Complexity.NPComplete.FeedbackVertexSetBipartiteWanted`) restricted to planar graphs
(ISGCI class `bipartite ∩ planar`, `gc_1069`). Its instance (a simple graph on `Fin n` given by an
edge list, and the bound `K`), its well-formedness `FeedbackVertexSetBipartite.WellFormed` (a
simple edge list and a bipartite graph, Mathlib's `SimpleGraph.IsBipartite`) and the question
`FeedbackVertexSet.FeedbackVertexSetFeasible` (at most `K` vertices whose removal leaves an
acyclic induced subgraph, Mathlib's `SimpleGraph.IsAcyclic`) are reused. The restriction adds
that the graph is planar, as MathlibExt's `SimpleGraph.IsPlanar`: a crossing-free straight-line
drawing in the real plane, which by Fáry's theorem exists exactly for the planar graphs.

Takaoka, Tayu and Ueno, Theorem 2: "FEEDBACK VERTEX SET is NP-complete even for planar
bigraphs", by a reduction from VERTEX COVER on planar graphs that replaces every edge `uv` by a
4-cycle `u, x_uv, v, y_uv`; its outputs are planar bipartite graphs, so it is a reduction to this
problem. Membership in NP: the certificate is `V'` (acyclicity of `G - V'` is checked in
polynomial time); bipartiteness is checked in linear time, and planarity in linear time by
Hopcroft and Tarjan ("Efficient planarity testing", Journal of the ACM 21 (1974), 549-568,
doi:10.1145/321850.321852).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **FEEDBACK VERTEX SET on planar bipartite graphs is NP-complete.** Source: Garey and Johnson
(1979), [GT7]; Takaoka, Tayu and Ueno (2013), Theorem 2. -/
public theorem_wanted feedbackVertexSetBipartitePlanar_npComplete :
    feedbackVertexSetBipartitePlanarDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L feedbackVertexSetBipartitePlanarDec

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetBipartitePlanar
