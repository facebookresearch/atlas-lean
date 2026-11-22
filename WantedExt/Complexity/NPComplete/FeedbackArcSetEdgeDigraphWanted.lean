/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK ARC SET on edge digraphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT8] FEEDBACK ARC SET, comment on
p. 192 ("for edge digraphs [Gavril, 1977a]");
F. Gavril, "Some NP-complete problems on graphs", Proc. 11th Conference on Information Sciences
and Systems, Johns Hopkins University, Baltimore, MD (1977), 91-95;
F. Harary and R. Z. Norman, "Some properties of line digraphs", Rendiconti del Circolo
Matematico di Palermo 9 (1960), 161-168, doi:10.1007/BF02854581 (edge digraphs).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.FeedbackArcSetWanted
public import WantedExt.Complexity.NPComplete.FeedbackVertexSetEdgeDigraphWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackArcSetEdgeDigraph

open MetaMathlibExt.Complexity.NPComplete.FeedbackArcSet
  (FeedbackArcSetInstance FeedbackArcSetFeasible)
open MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetEdgeDigraph (IsEdgeDigraph)

/-!
# FEEDBACK ARC SET on edge digraphs is NP-complete

INSTANCE: a directed graph `G = (V, A)` that is an edge digraph, and a positive integer
`K ≤ |A|`.
QUESTION: is there a subset `A' ⊆ A` with `|A'| ≤ K` such that `A'` contains at least one arc
from every directed cycle in `G`?

The instance and the question are those of FEEDBACK ARC SET
(`WantedExt.Complexity.NPComplete.FeedbackArcSetWanted`: a directed graph on `Fin n` given by a
list of distinct arcs without loops, and the bound `K`; the question asks for a vertex ordering
with at most `K` backward arcs, which is the same as `K` arcs meeting every directed cycle,
since the backward arcs of an ordering meet every directed cycle and a digraph without directed
cycles has a topological ordering). The restriction adds that `G` is an edge digraph,
`IsEdgeDigraph` from `WantedExt.Complexity.NPComplete.FeedbackVertexSetEdgeDigraphWanted`: the
line digraph `L(D)` of a directed graph `D` without multiple arcs (Harary and Norman 1960), with
one vertex for each arc of `D` and an arc from the vertex of `(u, v)` to the vertex of `(w, x)`
exactly when `v = w`. As in the source, `0 < K ≤ |A|`; the arc list has no duplicates, so its
length is `|A|`.

Garey and Johnson record the result for edge digraphs, attributed to Gavril (1977); that paper
was not available. Membership in NP: isolated vertices meet no arc, and `G` is an edge digraph
exactly when `G` without its isolated vertices is one (an isolated vertex is an arc between two
fresh vertices of `D`), so the certificate is the ordering of the vertices that occur in arcs
together with `tail` and `head` on those vertices, with values below twice their number,
checked in polynomial time in `|A|`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed FEEDBACK ARC SET instance whose digraph is an
edge digraph, with `0 < K ≤ |A|`. -/
def WellFormed (i : FeedbackArcSetInstance) : Prop :=
  FeedbackArcSet.WellFormed i ∧ IsEdgeDigraph i.1 i.2.1 ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.2.1.length

open Classical in
/-- FEEDBACK ARC SET on edge digraphs as a decision problem over bitstrings. -/
noncomputable def feedbackArcSetEdgeDigraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FeedbackArcSetInstance) x with
  | some i => decide (WellFormed i ∧ FeedbackArcSetFeasible i)
  | none => false

/-- **FEEDBACK ARC SET on edge digraphs is NP-complete.** Source: Garey and Johnson (1979),
[GT8]; Gavril (1977). -/
public theorem_wanted feedbackArcSetEdgeDigraph_npComplete :
    feedbackArcSetEdgeDigraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L feedbackArcSetEdgeDigraphDec

end MetaMathlibExt.Complexity.NPComplete.FeedbackArcSetEdgeDigraph
