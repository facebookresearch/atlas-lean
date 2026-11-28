/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET on edge digraphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT7] FEEDBACK VERTEX SET, comment on
p. 192 ("for edge digraphs [Gavril, 1977a]");
F. Gavril, "Some NP-complete problems on graphs", Proc. 11th Conference on Information Sciences
and Systems, Johns Hopkins University, Baltimore, MD (1977), 91-95;
F. Harary and R. Z. Norman, "Some properties of line digraphs", Rendiconti del Circolo
Matematico di Palermo 9 (1960), 161-168, doi:10.1007/BF02854581 (edge digraphs).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.FeedbackVertexSetEdgeDigraphDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetEdgeDigraph

/-!
# FEEDBACK VERTEX SET on edge digraphs is NP-complete

INSTANCE: a directed graph `G = (V, A)` that is an edge digraph, and a positive integer
`K ≤ |V|`.
QUESTION: is there a subset `V' ⊆ V` with `|V'| ≤ K` such that `V'` contains at least one vertex
from every directed cycle in `G`?

The edge digraph (line digraph) `L(D)` of a directed graph `D` has one vertex for each arc of
`D`, and an arc from the vertex of `(u, v)` to the vertex of `(w, x)` exactly when `v = w`
(Harary and Norman 1960). `IsEdgeDigraph n A` says that the digraph on `Fin n` with arc list `A`
is `L(D)` for a directed graph `D` on `Fin m` without multiple arcs: vertex `a` is the arc
`(tail a, head a)` of `D`, distinct vertices are distinct arcs, and `(a, b)` is an arc exactly
when `head a = tail b`. `D` has no loops either: a loop `tail a = head a` would make `(a, a)` an
arc of `G`, which `WellFormed` excludes.

A directed cycle is MathlibExt's `SimpleGraph.IsDirectedCycle` on the arc relation: a closed
directed walk `f 0 → f 1 → ⋯ → f (m + 1) = f 0` of positive length. A vertex set meets every
closed directed walk of positive length exactly when it meets every directed cycle, since every
such walk contains a directed cycle and every directed cycle is such a walk.

Garey and Johnson record the result for edge digraphs, attributed to Gavril (1977); that paper
was not available. It also follows from FEEDBACK ARC SET ([GT8], Karp 1972): an arc set of `D`
meets every directed cycle of `D` exactly when the corresponding vertex set of `L(D)` meets
every directed cycle of `L(D)`, so `(D, K) ↦ (L(D), K)` is a reduction. Membership in NP:
isolated vertices lie on no directed cycle, and `G` is an edge digraph exactly when `G` without
its isolated vertices is one (an isolated vertex is an arc between two fresh vertices of `D`).
The certificate is `V'` restricted to the vertices that occur in arcs, together with `tail` and
`head` on those vertices, with values below twice their number; it is checked in polynomial time
in `|A|`, acyclicity of `G - V'` by a topological sort.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **FEEDBACK VERTEX SET on edge digraphs is NP-complete.** Source: Garey and Johnson (1979),
[GT7]; Gavril (1977). -/
public theorem_wanted feedbackVertexSetEdgeDigraph_npComplete :
    feedbackVertexSetEdgeDigraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L feedbackVertexSetEdgeDigraphDec

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetEdgeDigraph
