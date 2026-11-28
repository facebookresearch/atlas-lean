/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EXACT COVER BY 3-SETS with at most three occurrences per element is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 221, problem [SP2] EXACT COVER BY 3-SETS
(X3C) (comment: remains NP-complete if no element occurs in more than three subsets
[Garey and Johnson, unpublished]);
T. F. Gonzalez, "Clustering to minimize the maximum intercluster distance", Theoretical
Computer Science 38 (1985), 293-306, doi:10.1016/0304-3975(85)90224-5 (NP-completeness when
every element occurs in exactly three subsets).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ExactCoverBy3SetsThreeOccurrencesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ExactCoverBy3SetsThreeOccurrences

open MetaMathlibExt.Complexity.NPComplete.ExactCoverBy3Sets

/-!
# EXACT COVER BY 3-SETS with at most three occurrences per element is NP-complete

INSTANCE: a set `X` with `|X| = 3q` and a collection `C` of 3-element subsets of `X`, such that
no element of `X` occurs in more than three subsets in `C`.
QUESTION: does `C` contain an exact cover for `X`, i.e., a subcollection `C' ⊆ C` such that
every element of `X` occurs in exactly one member of `C'`?

This is the restriction of `WantedExt.Complexity.NPComplete.ExactCoverBy3SetsWanted` ([SP2])
to instances in which every element occurs in at most three members of `C`. The instance type,
the parent well-formedness condition and the question are that module's
(`ExactCoverBy3SetsInstance`, `ExactCoverBy3Sets.WellFormed`, `ExactCoverBy3SetsFeasible`):
`X = {0, ..., 3q - 1}`, every member of `C` is a duplicate-free list of three elements of `X`,
and the question asks for a sublist of `C` covering every element of `X` exactly once.
`WellFormed` adds that every member of `C` is listed in increasing order and no member is
listed twice, so that the list entries are exactly the members of `C`, one entry each, and the
number of entries containing an element `x` is the number of members of `C` containing `x`;
and it adds the restriction that this number is at most three for every `x ∈ X`.

Gonzalez (1985) proves NP-completeness for the instances in which every element occurs in
exactly three members of `C`; these are instances of this problem, so the restriction stated
here is NP-hard as well, and membership in NP is inherited from [SP2].

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **EXACT COVER BY 3-SETS with at most three occurrences per element is NP-complete.**
Source: Garey and Johnson (1979), [SP2]; Gonzalez (1985). -/
public theorem_wanted exactCoverBy3SetsThreeOccurrences_npComplete :
    exactCoverBy3SetsThreeOccurrencesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L exactCoverBy3SetsThreeOccurrencesDec

end MetaMathlibExt.Complexity.NPComplete.ExactCoverBy3SetsThreeOccurrences
