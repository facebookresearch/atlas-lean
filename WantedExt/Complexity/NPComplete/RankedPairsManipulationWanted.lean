/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RANKED PAIRS MANIPULATION (single manipulator, co-winner) is NP-complete

Source:
L. Xia, M. Zuckerman, A. D. Procaccia, V. Conitzer and J. S. Rosenschein, "Complexity of unweighted
coalitional manipulation under some common voting rules", Proceedings of the 21st International
Joint Conference on Artificial Intelligence (IJCAI 2009), 348-353, Section 2 (ranked pairs,
Definition 2.1 and the co-winner formulation) and Theorem 4.1;
L. Xia, V. Conitzer, A. D. Procaccia and J. S. Rosenschein, "Complexity of unweighted coalitional
manipulation under some common voting rules", 2nd International Workshop on Computational Social
Choice (COMSOC 2008), Theorem 2 and its proof ("The UCMU and UCMC problems under ranked pairs are
NP-complete, even when there is only one manipulator"),
https://research.illc.uva.nl/COMSOC/2008/papers/PDF/35-xia.pdf.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.RankedPairsManipulationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RankedPairsManipulation

open MathlibExt.GameTheory.SocialChoice.ArrowWanted (Profile)
open MathlibExt.GameTheory.SocialChoice.CondorcetCycle (supporters)
open MetaMathlibExt.Complexity.NPComplete.SecondOrderCopelandManipulation
  (SecondOrderCopelandManipulationInstance WellFormed Candidate)

/-!
# RANKED PAIRS MANIPULATION (single manipulator, co-winner) is NP-complete

INSTANCE: a set `C` of candidates, a distinguished candidate `p ∈ C`, and a collection `V` of
sincere votes, each a linear order on `C`.
QUESTION: is there a linear order on `C` for one additional voter (the manipulator) such that
`p` is among the ranked-pairs winners of the election with votes `V` and the manipulator's vote?

Ranked pairs (Xia et al. 2009, Section 2, after Tideman): "This rule first creates an entire
ranking of all the candidates, as follows. ... In each step, we consider a pair of candidates
`cᵢ, cⱼ` that we have not previously considered (as a pair): specifically, we choose the remaining
pair with the highest `adv_P(cᵢ, cⱼ)`. We then fix the order `cᵢ ≻ cⱼ`, unless this contradicts
previous orders that we fixed (that is, it violates transitivity). We continue until we have
considered all pairs of candidates (hence, in the end, we have a full ranking). The candidate at
the top of the ranking wins." Here `adv_P(cᵢ, cⱼ)`, the advantage of `cᵢ` over `cⱼ`, is "the
number of votes in `P` that rank `cᵢ` ahead of `cⱼ`" (Section 2, maximin), counted over all votes,
the manipulator's included. "All
of these rules allow for the possibility that multiple candidates end up tied for the win.
Technically, therefore, they are really voting correspondences": the source fixes no
tie-breaking, and its proof of Theorem 2 lets ties among pairs fall either way ("no matter how
ties are broken"; "We now construct a way to fix the pairwise rankings such that `c` is not the
winner"). So a candidate is a winner when it is at the top of the ranking built from some order of
consideration allowed by the rule (`IsConsiderationOrder`): each pair is considered once, in its
orientation with the larger number of votes (either orientation when the two numbers are equal),
and these numbers never increase along the order. `lockedPairs` fixes the pairs in that order,
skipping a pair `(a, b)` when `b` is already above `a` through fixed pairs, and `IsTop` says that
`p` is above every other candidate through fixed pairs.

This is the co-winner formulation ("we require that `c ∈ r(P_NM ∪ P_M)`") with a single
manipulator. Xia et al. prove both formulations NP-complete for one manipulator (COMSOC 2008,
Theorem 2: UCMU and UCMC; IJCAI 2009, Theorem 4.1 and "Our results hold for the co-winner
formulation as well"). The co-winner form is in NP with this tie handling: the manipulator's
vote and an order of consideration are a certificate, checked in polynomial time. The
unique-winner form is not formalized here: with ties broken every possible way, its membership in
NP is not established by these sources.

As in `WantedExt.Complexity.NPComplete.SecondOrderCopelandManipulationWanted`, whose instance
type, `WellFormed` and candidate type are reused: candidates are distinct natural numbers listed
in `C`, a sincere vote is a permutation of `C` from most to least preferred, `V` is a list (equal
votes may repeat), voters are numbered in the order of `V` and the manipulator is the last voter,
whose vote is any strict total order on `C` (`MathlibExt.GameTheory.SocialChoice.ArrowWanted
.Profile`). The number of votes ranking `a` ahead of `b` is the size of
`MathlibExt.GameTheory.SocialChoice.CondorcetCycle.supporters`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **RANKED PAIRS MANIPULATION (single manipulator, co-winner) is NP-complete.** Source: Xia,
Zuckerman, Procaccia, Conitzer and Rosenschein (2009), Theorem 4.1; Xia, Conitzer, Procaccia and
Rosenschein (2008), Theorem 2. -/
public theorem_wanted rankedPairsManipulation_npComplete :
    rankedPairsManipulationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L rankedPairsManipulationDec

end MetaMathlibExt.Complexity.NPComplete.RankedPairsManipulation
