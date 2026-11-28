/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-DIMENSIONAL MATCHING with at most three occurrences per element is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP1] 3-DIMENSIONAL MATCHING, p. 221,
comment: "Also remains NP-complete if no element occurs in more than three triples, but is
solvable in polynomial time if no element occurs in more than two triples [Garey and Johnson,
——]" (unpublished; the result and its attribution are those recorded by Garey and Johnson);
M. E. Dyer and A. M. Frieze, "Planar 3DM is NP-complete", Journal of Algorithms 7(2) (1986),
174-184, doi:10.1016/0196-6774(86)90002-7.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ThreeDimensionalMatchingThreeOccurrencesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalMatchingThreeOccurrences

open MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalMatching
  (ThreeDimensionalMatchingInstance ThreeDimensionalMatchingFeasible)

/-!
# 3-DIMENSIONAL MATCHING with at most three occurrences per element is NP-complete

INSTANCE: a set `M ⊆ W × X × Y`, where `W`, `X` and `Y` are disjoint sets having the same
number `q` of elements, such that no element of `W ∪ X ∪ Y` occurs in more than three triples
of `M`. QUESTION: does `M` contain a matching, that is, a subset `M' ⊆ M` with `|M'| = q` such
that no two elements of `M'` agree in any coordinate?

The instance, its well-formedness and the matching question are those of
`WantedExt.Complexity.NPComplete.ThreeDimensionalMatchingWanted` (elements `0, …, q - 1` of each
of `W`, `X`, `Y`; triples as a list). Here the triples are distinct (`M` is a set), so the
number of triples of `M` in which an element occurs is the number of list entries with that
element in its coordinate; it is at most 3 for every element of each of `W`, `X` and `Y`.

The [SP1] comment records the result as unpublished work of Garey and Johnson. Dyer and Frieze
prove 3-DIMENSIONAL MATCHING NP-complete for planar instances in which every element occurs in
at most three triples (`PlanarThreeDimensionalMatchingWanted`); those instances belong to this
class, so their reduction is also a reduction to this problem. Membership in NP is inherited:
the matching is a certificate.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **3-DIMENSIONAL MATCHING with at most three occurrences per element is NP-complete.**
Source: Garey and Johnson (1979), [SP1], comment; Dyer and Frieze (1986). -/
public theorem_wanted threeDimensionalMatchingThreeOccurrences_npComplete :
    threeDimensionalMatchingThreeOccurrencesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeDimensionalMatchingThreeOccurrencesDec

end MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalMatchingThreeOccurrences
