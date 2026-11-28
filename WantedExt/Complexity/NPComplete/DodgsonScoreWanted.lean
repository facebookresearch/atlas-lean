/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DODGSON SCORE is NP-complete

Source:
J. J. Bartholdi III, C. A. Tovey and M. A. Trick, "Voting schemes for which it can be difficult
to tell who won the election", Social Choice and Welfare 6 (1989), 157-165,
doi:10.1007/BF00303169;
E. Hemaspaandra, L. A. Hemaspaandra and J. Rothe, "Exact analysis of Dodgson elections: Lewis
Carroll's 1876 voting system is complete for parallel access to NP", Journal of the ACM 44
(1997), 806-825, doi:10.1145/268999.269002 (arXiv:cs/9907036), Section 3 (the decision problem
DodgsonScore and its NP-completeness, due to Bartholdi, Tovey and Trick).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DodgsonScoreDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DodgsonScore

open MathlibExt.GameTheory.SocialChoice.ArrowWanted (Profile)
open MathlibExt.GameTheory.SocialChoice.CondorcetCycle (MajorityPrefers)

/-!
# DODGSON SCORE is NP-complete

INSTANCE: a set `C` of candidates, a candidate `c ∈ C`, a multiset `V` of voters' preference
orders on `C` (strict, transitive and complete; coded as a list), and a positive integer `k`.
QUESTION: is the Dodgson score of `c` at most `k`, i.e., can `c` be made a Condorcet winner by at
most `k` sequential switches, where a switch exchanges two adjacent candidates in one voter's
preference order, and a Condorcet winner is preferred to each other candidate by strictly more
than half of the voters?

Candidates are `0, …, m - 1`, and each voter's preference order is a list of all candidates,
each once, most preferred first. A switch `(v, p)` exchanges the candidates at positions `p` and
`p + 1` of voter `v`'s list. The resulting lists are read as a profile of strict total orders
(`MathlibExt`'s `Profile`, the encoding of Arrow's theorem), and pairwise majority is
`MathlibExt`'s `MajorityPrefers` (strictly more than half of the voters strictly prefer one
candidate to the other). Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DODGSON SCORE is NP-complete.** Source: Bartholdi, Tovey and Trick (1989); Hemaspaandra,
Hemaspaandra and Rothe (1997), Section 3. -/
public theorem_wanted dodgsonScore_npComplete :
    dodgsonScoreDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dodgsonScoreDec

end MetaMathlibExt.Complexity.NPComplete.DodgsonScore
