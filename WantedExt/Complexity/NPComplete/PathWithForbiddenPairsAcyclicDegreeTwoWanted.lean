/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATH WITH FORBIDDEN PAIRS on acyclic digraphs of in- and out-degree at most 2 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT54] PATH WITH FORBIDDEN PAIRS,
p. 203 (comment: "Remains NP-complete even if `G` is acyclic with no in- or out-degree
exceeding 2.");
H. N. Gabow, S. N. Maheshwari and L. J. Osterweil, "On two problems in the generation of
program test paths", IEEE Transactions on Software Engineering SE-2 (1976), 227-231,
doi:10.1109/TSE.1976.233819.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PathWithForbiddenPairsAcyclicDegreeTwoDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathWithForbiddenPairsAcyclicDegreeTwo

/-!
# PATH WITH FORBIDDEN PAIRS on acyclic digraphs of in- and out-degree at most 2 is NP-complete

INSTANCE: a directed graph `G = (V, A)` that is acyclic and has no vertex of in-degree or
out-degree exceeding 2, specified vertices `s, t ∈ V`, and a collection
`C = {(a₁, b₁), ..., (aₙ, bₙ)}` of pairs of vertices from `V`. QUESTION: is there a directed
path from `s` to `t` in `G` that contains at most one vertex from each pair in `C`?

This is the restriction of PATH WITH FORBIDDEN PAIRS ([GT54], `PathWithForbiddenPairsWanted`)
named in the first sentence of the entry's comment. The instance type,
`PathWithForbiddenPairs.WellFormed` and `PathWithForbiddenPairs.PathWithForbiddenPairsFeasible`
are the parent's, unchanged; `WellFormed` adds the two restrictions, stated as in
`PathWithDisjointForbiddenPairsWanted` (which also requires the pairs to be disjoint, the
comment's last sentence, and is a different problem):

* acyclic: no vertex reaches itself along one or more arcs (`Relation.TransGen`);
* degree: each vertex `v` has at most 2 distinct in-neighbours `u` (`(u, v)` an arc) and at
  most 2 distinct out-neighbours, counted as sets so that a repeated arc in the list is one
  arc.

The pairs are unrestricted, as in the parent. The arc-pair variant in the same comment is a
different problem and is not stated here.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PATH WITH FORBIDDEN PAIRS is NP-complete on acyclic digraphs with in- and out-degree at
most 2.** Source: Garey and Johnson (1979), [GT54], comment; Gabow, Maheshwari and Osterweil
(1976). -/
public theorem_wanted pathWithForbiddenPairsAcyclicDegreeTwo_npComplete :
    pathWithForbiddenPairsAcyclicDegreeTwoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pathWithForbiddenPairsAcyclicDegreeTwoDec

end MetaMathlibExt.Complexity.NPComplete.PathWithForbiddenPairsAcyclicDegreeTwo
