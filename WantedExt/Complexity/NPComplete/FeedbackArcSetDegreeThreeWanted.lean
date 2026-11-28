/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK ARC SET with total degree at most 3 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT8] FEEDBACK ARC SET, comment on
p. 192 ("Remains NP-complete for digraphs in which no vertex has total in-degree and out-degree
more than 3, and for edge digraphs [Gavril, 1977a]");
F. Gavril, "Some NP-complete problems on graphs", Proc. 11th Conference on Information Sciences
and Systems, Johns Hopkins University, Baltimore, MD (1977), 91-95.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.FeedbackArcSetDegreeThreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackArcSetDegreeThree

open MetaMathlibExt.Complexity.NPComplete.FeedbackArcSet
  (FeedbackArcSetInstance FeedbackArcSetFeasible)

/-!
# FEEDBACK ARC SET with total degree at most 3 is NP-complete

INSTANCE: a directed graph `G = (V, A)` in which no vertex has total in-degree and out-degree
more than 3, and a positive integer `K ≤ |A|`.
QUESTION: is there a subset `A' ⊆ A` with `|A'| ≤ K` such that `A'` contains at least one arc
from every directed cycle in `G`?

The instance and the question are those of FEEDBACK ARC SET
(`WantedExt.Complexity.NPComplete.FeedbackArcSetWanted`: a directed graph on `Fin n` given by a
list of distinct arcs without loops, and the bound `K`; the question asks for a vertex ordering
with at most `K` backward arcs, which is the same as `K` arcs meeting every directed cycle,
since the backward arcs of an ordering meet every directed cycle and a digraph without directed
cycles has a topological ordering). The restriction adds that every vertex `v` has in-degree
(arcs `(u, v)`) plus out-degree (arcs `(v, w)`) at most 3; the arc list has no duplicates, so
these counts are the degrees and its length is `|A|`. As in the source, `0 < K ≤ |A|`.

Garey and Johnson record the result, attributed to Gavril (1977); that paper was not available.
It is consistent with the FEEDBACK VERTEX SET restriction to in- and out-degree at most 2 in the
same book ([GT7]): splitting every vertex `v` into `v⁻ → v⁺`, with each arc `(u, v)` replaced by
`(u⁺, v⁻)`, gives total degree at most 3, and a feedback arc set can use split arcs only (the
only arc leaving `v⁻` is `(v⁻, v⁺)`). Membership in NP: the certificate is the ordering of the
vertices that occur in arcs, checked in polynomial time in `|A|`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **FEEDBACK ARC SET with total degree at most 3 is NP-complete.** Source: Garey and Johnson
(1979), [GT8]; Gavril (1977). -/
public theorem_wanted feedbackArcSetDegreeThree_npComplete :
    feedbackArcSetDegreeThreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L feedbackArcSetDegreeThreeDec

end MetaMathlibExt.Complexity.NPComplete.FeedbackArcSetDegreeThree
