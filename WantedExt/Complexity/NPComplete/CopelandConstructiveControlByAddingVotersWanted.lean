/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COPELAND^α CONSTRUCTIVE CONTROL BY ADDING VOTERS is NP-complete

Source:
P. Faliszewski, E. Hemaspaandra, L. A. Hemaspaandra and J. Rothe, "Llull and Copeland voting
computationally resist bribery and constructive control", Journal of Artificial Intelligence
Research 35 (2009), 275-341, doi:10.1613/jair.2697 (Definition 2.1; problem E-CCAV, Section 2.3;
Theorem 4.17: for each rational `α` with `0 ≤ α ≤ 1`, Copeland^α is resistant to constructive
control via adding voters in the unique-winner model).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CopelandConstructiveControlByAddingVotersDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CopelandConstructiveControlByAddingVoters

open CondorcetConstructiveControlByAddingVoters
  (CondorcetConstructiveControlByAddingVotersInstance profile)
open MathlibExt.GameTheory.SocialChoice.CondorcetCycle (MajorityPrefers)

/-!
# COPELAND^α CONSTRUCTIVE CONTROL BY ADDING VOTERS is NP-complete

Fix a rational `α` with `0 ≤ α ≤ 1`.
INSTANCE: a set `C` of candidates, two disjoint collections of voters `V` (registered) and `W`
(unregistered), represented via preference lists over `C`, a distinguished candidate `p`, and a
nonnegative integer `k`.
QUESTION: is there a subset `Q` of the voters in `W` with `‖Q‖ ≤ k` such that `p` is the unique
Copeland^α winner of the election with voters `V ∪ Q`?

Copeland^α (Faliszewski, Hemaspaandra, Hemaspaandra and Rothe, Definition 2.1): in each
head-to-head contest between two distinct candidates, a candidate preferred by a majority of the
voters obtains one point and the other none, and if neither is preferred by a majority (a tie)
both obtain `α` points; the Copeland^α score of a candidate is the sum of its points, and `p` is
the unique winner when its score exceeds that of every other candidate.

Representation, shared with `CondorcetConstructiveControlByAddingVotersWanted`: the candidates
are `C = {0, ..., m - 1}`; a vote is a list of candidates, best first, and a well-formed vote
lists every candidate exactly once (rational voters with strict linear preferences); `V` and `W`
are lists of votes (two voters may cast the same vote), and the added voters `Q` are a sublist
of `W`. The election `V ++ Q` is turned into a profile of the repository's social-choice
library by `CondorcetConstructiveControlByAddingVoters.profile`, and "preferred by a majority"
is that library's `CondorcetCycle.MajorityPrefers` (strictly more than half of the voters).
The parameter `α` is fixed, as in the source, so there is one decision problem for each `α`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **COPELAND^α CONSTRUCTIVE CONTROL BY ADDING VOTERS is NP-complete for every rational
`0 ≤ α ≤ 1`.** Source: Faliszewski, Hemaspaandra, Hemaspaandra and Rothe (2009),
Theorem 4.17. -/
public theorem_wanted copelandConstructiveControlByAddingVoters_npComplete (α : ℚ) (h₀ : 0 ≤ α)
    (h₁ : α ≤ 1) :
    copelandConstructiveControlByAddingVotersDec α ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (copelandConstructiveControlByAddingVotersDec α)

end MetaMathlibExt.Complexity.NPComplete.CopelandConstructiveControlByAddingVoters
