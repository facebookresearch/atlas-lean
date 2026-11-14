/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONDORCET CONSTRUCTIVE CONTROL BY DELETING VOTERS is NP-complete

Source:
J. J. Bartholdi III, C. A. Tovey, and M. A. Trick, "How hard is it to control an election?",
Mathematical and Computer Modelling 16 (1992), 27-40, doi:10.1016/0895-7177(92)90085-Y;
E. Hemaspaandra, L. A. Hemaspaandra, and J. Rothe, "Anyone but him: The complexity of
precluding an alternative", Proceedings of the 20th National Conference on Artificial
Intelligence (AAAI 2005), 95-101 (Table 1 records the Bartholdi-Tovey-Trick result).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.CondorcetConstructiveControlByAddingVotersWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CondorcetConstructiveControlByDeletingVoters

/-!
# CONDORCET CONSTRUCTIVE CONTROL BY DELETING VOTERS is NP-complete

INSTANCE: a set `C` of candidates, a distinguished candidate `c ∈ C`, a set `V` of voters with
preferences over `C`, and a positive integer `k ≤ ‖V‖`. QUESTION: are there `k` or fewer voters
in `V` whose disenfranchisement would make `c` the (unique) Condorcet winner, i.e., for each
candidate `d ≠ c`, a strict majority of the remaining voters prefers `c` to `d`?

The votes, the profile of an election and the Condorcet winner are those of
`WantedExt.Complexity.NPComplete.CondorcetConstructiveControlByAddingVotersWanted`
(`CondorcetConstructiveControlByAddingVoters.voteOrder`,
`CondorcetConstructiveControlByAddingVoters.profile`,
`CondorcetConstructiveControlByAddingVoters.IsCondorcetWinner`, built on
`MathlibExt.GameTheory.SocialChoice.CondorcetCycle.MajorityPrefers`): the candidates are
`C = {0, ..., m - 1}`, a vote is a list of all candidates, best first, and `V` is a list of votes.
The voters who keep their vote are a sublist `V'` of `V`, and at most `k` are deleted when
`‖V‖ ≤ ‖V'‖ + k`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `m` of candidates, the votes `V`, the distinguished candidate `c`,
and the bound `k`. -/
abbrev CondorcetConstructiveControlByDeletingVotersInstance := ℕ × List (List ℕ) × ℕ × ℕ

/-- Well-formedness of an instance: every vote is a strict ranking of all `m` candidates, `c` is
a candidate, and `0 < k ≤ ‖V‖`. -/
def WellFormed (i : CondorcetConstructiveControlByDeletingVotersInstance) : Prop :=
  (∀ v ∈ i.2.1, v.Perm (List.range i.1)) ∧ i.2.2.1 < i.1 ∧ 0 < i.2.2.2 ∧
    i.2.2.2 ≤ i.2.1.length

/-- At most `k` voters of `V` whose deletion makes `c` the Condorcet winner of the remaining
votes `V'`. -/
def CondorcetConstructiveControlByDeletingVotersFeasible
    (i : CondorcetConstructiveControlByDeletingVotersInstance) : Prop :=
  ∃ V' : List (List ℕ), V'.Sublist i.2.1 ∧ i.2.1.length ≤ V'.length + i.2.2.2 ∧
    CondorcetConstructiveControlByAddingVoters.IsCondorcetWinner i.1 V' i.2.2.1

open Classical in
/-- CONDORCET CONSTRUCTIVE CONTROL BY DELETING VOTERS as a decision problem over bitstrings. -/
noncomputable def condorcetConstructiveControlByDeletingVotersDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CondorcetConstructiveControlByDeletingVotersInstance) x with
  | some i => decide (WellFormed i ∧ CondorcetConstructiveControlByDeletingVotersFeasible i)
  | none => false

/-- **CONDORCET CONSTRUCTIVE CONTROL BY DELETING VOTERS is NP-complete.** Source: Bartholdi,
Tovey, and Trick (1992). -/
public theorem_wanted condorcetConstructiveControlByDeletingVoters_npComplete :
    condorcetConstructiveControlByDeletingVotersDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L condorcetConstructiveControlByDeletingVotersDec

end MetaMathlibExt.Complexity.NPComplete.CondorcetConstructiveControlByDeletingVoters
