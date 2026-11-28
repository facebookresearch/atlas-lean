/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAX CARDINALITY SMTI (maximum stable marriage with ties and incomplete lists) is NP-complete

Source:
D. F. Manlove, R. W. Irving, K. Iwama, S. Miyazaki, and Y. Morita, "Hard variants of stable
marriage", Theoretical Computer Science 276(1-2) (2002), 261-279,
doi:10.1016/S0304-3975(01)00206-7, Section 2 (problem MAX CARDINALITY SMTI; Lemma 2.1 and
Theorem 2.2: NP-complete, even with ties on one side only);
K. Iwama, D. Manlove, S. Miyazaki, and Y. Morita, "Stable marriage with incomplete lists and
ties", Proc. ICALP 1999, Lecture Notes in Computer Science 1644 (1999), 443-452,
doi:10.1007/3-540-48523-6_41.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MaxCardinalitySMTIDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaxCardinalitySMTI

/-!
# MAX CARDINALITY SMTI is NP-complete

INSTANCE: `n` men and `n` women, a preference list of women for each man and a preference list
of men for each woman, each list possibly incomplete and possibly with ties, and an integer
`K ∈ ℤ⁺`. QUESTION: does the instance admit a stable matching `M` with `|M| ≥ K`?

Person `p` is acceptable to `q` if `p` appears on `q`'s list. A matching is a set of
(man, woman) pairs, each person in at most one pair, such that in every pair each finds the
other acceptable. It is (weakly) stable if there is no pair `(m, w)` each of whom is either
unmatched and finds the other acceptable, or strictly prefers the other to their partner.

The men and the women are `Fin n`. A preference list is a list of ties, each tie a list of
people in the tie, best first: `p` is acceptable to `q` iff `p` is in some tie of `q`'s list,
and `q` strictly prefers `p` to `p'` iff `p` is acceptable to `q` and lies in an earlier tie
than `p'`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MAX CARDINALITY SMTI is NP-complete.** Source: Manlove, Irving, Iwama, Miyazaki, and
Morita (2002), Lemma 2.1; Iwama, Manlove, Miyazaki, and Morita (1999). -/
public theorem_wanted maxCardinalitySMTI_npComplete :
    maxCardinalitySMTIDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maxCardinalitySMTIDec

end MetaMathlibExt.Complexity.NPComplete.MaxCardinalitySMTI
