/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-DIMENSIONAL MATCHING for pairwise consistent triples is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP1] 3-DIMENSIONAL MATCHING, comment,
and the transformation from 3SAT in Section 3.1.2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ThreeDimensionalMatchingPairwiseConsistentDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalMatchingPairwiseConsistent

/-!
# 3-DIMENSIONAL MATCHING for pairwise consistent triples is NP-complete

INSTANCE: a set `M ⊆ W × X × Y`, where `W`, `X`, and `Y` are disjoint sets having the same
number `q` of elements, such that `M` is pairwise consistent: for all elements `a`, `b`, `c`,
whenever there exist elements `w`, `x`, and `y` such that `(a, b, w) ∈ M`, `(a, x, c) ∈ M`, and
`(y, b, c) ∈ M`, then `(a, b, c) ∈ M`. QUESTION: does `M` contain a matching, i.e., a subset
`M' ⊆ M` such that `|M'| = q` and no two elements of `M'` agree in any coordinate?

This is 3-DIMENSIONAL MATCHING (`WantedExt.Complexity.NPComplete.ThreeDimensionalMatchingWanted`,
Garey and Johnson [SP1]) restricted as in the [SP1] comment: "Remains NP-complete if `M` is
'pairwise consistent,' ... (this follows from the proof of Theorem 3.1.2)", that is, from the
transformation from 3SAT in Section 3.1.2, whose triples are pairwise consistent. Garey and
Johnson give no other reference; their entry is the literature record. (Their comment prints
"elements `w`, `z`, and `y`"; the `z` is a misprint for the `x` of `(a, x, c)`.)

The instance (`q` and the list of triples, the three coordinates ranging over `0, …, q - 1`),
`ThreeDimensionalMatching.WellFormed` and
`ThreeDimensionalMatching.ThreeDimensionalMatchingFeasible` are reused unchanged; pairwise
consistency is added to well-formedness, with the three witnesses as list entries
`t₁ = (a, b, w)`, `t₂ = (a, x, c)` and `t₃ = (y, b, c)`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open ThreeDimensionalMatching (ThreeDimensionalMatchingInstance)

/-- **3-DIMENSIONAL MATCHING is NP-complete for pairwise consistent triples.** Source: Garey and
Johnson (1979), [SP1], comment, and Section 3.1.2. -/
public theorem_wanted threeDimensionalMatchingPairwiseConsistent_npComplete :
    threeDimensionalMatchingPairwiseConsistentDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeDimensionalMatchingPairwiseConsistentDec

end MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalMatchingPairwiseConsistent
