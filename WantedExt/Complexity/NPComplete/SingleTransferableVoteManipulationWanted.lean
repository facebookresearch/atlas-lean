/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SINGLE TRANSFERABLE VOTE MANIPULATION is NP-complete

Source:
J. J. Bartholdi III and J. B. Orlin, "Single transferable vote resists strategic voting",
Social Choice and Welfare 8 (1991), 341-354, doi:10.1007/BF00183045
(Theorem 1: EFFECTIVE PREFERENCE is NP-complete under Successive Elimination).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SingleTransferableVoteManipulationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SingleTransferableVoteManipulation

/-!
# SINGLE TRANSFERABLE VOTE MANIPULATION is NP-complete

Bartholdi and Orlin's EFFECTIVE PREFERENCE problem for single-winner STV:
"GIVEN: A set `C` of candidates; a distinguished candidate `c`; and the set `V` of sincere,
transitive, strict, and complete preferences of the voters. QUESTION: Is there a preference
ordering on `C` that when tallied with the preferences of `V` will ensure the election of `c`?"

Single-winner STV is the voting scheme of the source's Theorem 1, "successively eliminating a
candidate with the fewest votes and reallocating his support": each ballot counts for its most
preferred candidate that has not been eliminated, a candidate with the fewest such votes is
eliminated, and this repeats until one candidate, the winner, remains. (A candidate with more
than half of the ballots is never one with the fewest votes while two or more remain, so the
source's early election of a candidate reaching the quota `⌊|V| / 2⌋ + 1` elects the same
winner.) Ties for the fewest votes are broken by a fixed order of the candidates: the instance
lists the candidates, and among the tied candidates the one listed first is eliminated. The
source leaves tie-breaking open and observes that the election is in NP because a preference
"can be verified in polynomial time by tallying the election", which needs a deterministic
tally.

Candidates are natural-number names listed without repetition; a preference is a list of all
candidates, most preferred first (a permutation of the candidate list). The strategic voter's
preference is a permutation of the candidate list as well, tallied together with `V`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SINGLE TRANSFERABLE VOTE MANIPULATION is NP-complete.** Source: Bartholdi and Orlin
(1991), Theorem 1. -/
public theorem_wanted singleTransferableVoteManipulation_npComplete :
    singleTransferableVoteManipulationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L singleTransferableVoteManipulationDec

end MetaMathlibExt.Complexity.NPComplete.SingleTransferableVoteManipulation
