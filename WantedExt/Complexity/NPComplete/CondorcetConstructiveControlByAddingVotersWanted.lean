/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONDORCET CONSTRUCTIVE CONTROL BY ADDING VOTERS is NP-complete

Source:
J. J. Bartholdi III, C. A. Tovey, and M. A. Trick, "How hard is it to control an election?",
Mathematical and Computer Modelling 16 (1992), 27-40, doi:10.1016/0895-7177(92)90085-Y;
E. Hemaspaandra, L. A. Hemaspaandra, and J. Rothe, "Anyone but him: The complexity of
precluding an alternative", Proceedings of the 20th National Conference on Artificial
Intelligence (AAAI 2005), 95-101 (Table 1 records the Bartholdi-Tovey-Trick result).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CondorcetConstructiveControlByAddingVotersDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CondorcetConstructiveControlByAddingVoters

/-!
# CONDORCET CONSTRUCTIVE CONTROL BY ADDING VOTERS is NP-complete

INSTANCE: a set `C` of candidates and a distinguished candidate `c ∈ C`, a set `V` of registered
voters, an additional set `W` of yet unregistered voters (both `V` and `W` have preferences over
`C`), and a positive integer `k ≤ ‖W‖`. QUESTION: are there `k` or fewer voters from `W` whose
registration would make `c` the (unique) Condorcet winner, i.e., for each candidate `d ≠ c`, a
strict majority of the voters prefers `c` to `d`?

Representation. The candidates are `C = {0, ..., m - 1}`. A vote is a list of candidates, best
first; a well-formed vote lists every candidate exactly once (`List.Perm` of
`List.range m`), so voters have strict, complete and transitive preferences. `V` and `W` are lists
of votes (two voters may cast the same vote), and the voters added from `W` are a sublist of `W`.
The election `V ++ W'` is turned into a profile `Fin |V ++ W'| → StrictTotalOrder (Fin m)` of the
repository's social-choice library (`MathlibExt.GameTheory.SocialChoice`), and "strict
majority" is that library's `CondorcetCycle.MajorityPrefers`. A Condorcet winner is unique
whenever it exists, so "the unique winner" and "a Condorcet winner" coincide.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CONDORCET CONSTRUCTIVE CONTROL BY ADDING VOTERS is NP-complete.** Source: Bartholdi,
Tovey, and Trick (1992). -/
public theorem_wanted condorcetConstructiveControlByAddingVoters_npComplete :
    condorcetConstructiveControlByAddingVotersDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L condorcetConstructiveControlByAddingVotersDec

end MetaMathlibExt.Complexity.NPComplete.CondorcetConstructiveControlByAddingVoters
