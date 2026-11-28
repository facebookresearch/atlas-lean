/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM TEST SET with unions of tests is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP6] MINIMUM TEST SET, p. 222,
comment: the variant in which `C'` can contain unions of subsets in `C` as well as subsets in
`C` is also NP-complete (reference: T. Ibaraki, T. Kameda, and S. Toida, "NP-complete diagnosis
problems on system graphs", unpublished manuscript (1977)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinimumTestSetUnionsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumTestSetUnions

open MetaMathlibExt.Complexity.NPComplete.MinimumTestSet

/-!
# MINIMUM TEST SET with unions of tests is NP-complete

INSTANCE: a collection `C` of subsets of a finite set `S`, and a positive integer `K ≤ |C|`.
QUESTION: is there a collection `C'` with `|C'| ≤ K`, each member of which is a member of `C` or
a union of members of `C` (the comment's variant: `C'` can contain unions of subsets in `C` as
well as subsets in `C`), such that for each pair of distinct elements `u, v ∈ S` there is some
set `c ∈ C'` that contains exactly one of `u` and `v`?

The instance is that of `MinimumTestSetWanted`: `S = {0, …, n - 1}`, and `C` is a list of
duplicate-free lists of elements of `S`. A test of `C'` is given by the sublist `t` of `C` whose
union it is (a single member of `C` is the union of a one-element sublist); an element lies in
that test when it lies in some member of `t`. `WellFormed` adds that the members of `C` are
distinct as sets (so the list length is `|C|`) and Garey and Johnson's bound `0 < K ≤ |C|`,
neither of which the parent module imposes.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM TEST SET with unions of tests is NP-complete.** Source: Garey and Johnson (1979),
[SP6], comment (Ibaraki, Kameda, and Toida, 1977). -/
public theorem_wanted minimumTestSetUnions_npComplete :
    minimumTestSetUnionsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumTestSetUnionsDec

end MetaMathlibExt.Complexity.NPComplete.MinimumTestSetUnions
