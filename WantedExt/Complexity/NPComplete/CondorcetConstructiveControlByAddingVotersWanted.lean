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
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.GameTheory.SocialChoice.CondorcetCycle

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

/-- An instance: the number `m` of candidates, the registered votes `V`, the unregistered votes
`W`, the distinguished candidate `c`, and the bound `k`. -/
abbrev CondorcetConstructiveControlByAddingVotersInstance :=
  ℕ × List (List ℕ) × List (List ℕ) × ℕ × ℕ

/-- The strict preference of a vote `v` on the candidates `Fin m`: `a` is preferred to `b` when
`a` occurs before `b` in `v`. Positions are compared with `List.idxOf`, and equal positions (which
occur only for candidates missing from `v`, never in a well-formed vote) are broken by index, so
the relation is a strict total order for every list. -/
def voteOrder {m : ℕ} (v : List ℕ) : MathlibExt.Order.StrictTotalOrder (Fin m) where
  lt a b := v.idxOf (a : ℕ) < v.idxOf (b : ℕ) ∨
    (v.idxOf (a : ℕ) = v.idxOf (b : ℕ) ∧ (a : ℕ) < b)
  irrefl a h := by omega
  trans h₁ h₂ := by omega
  total {a b} hab := by
    have : (a : ℕ) ≠ b := fun h => hab (Fin.ext h)
    omega

/-- The profile of an election given as a list of votes: voter `j` has the preference of the
`j`-th vote. -/
def profile (m : ℕ) (E : List (List ℕ)) :
    MathlibExt.GameTheory.SocialChoice.ArrowWanted.Profile (Fin m) (Fin E.length) :=
  fun j => voteOrder E[j]

/-- Candidate `c` is the Condorcet winner of the election `E`: for each candidate `d ≠ c`, a
strict majority of the voters of `E` prefers `c` to `d`. -/
def IsCondorcetWinner (m : ℕ) (E : List (List ℕ)) (c : ℕ) : Prop :=
  ∀ a d : Fin m, (a : ℕ) = c → d ≠ a →
    MathlibExt.GameTheory.SocialChoice.CondorcetCycle.MajorityPrefers (profile m E) a d

/-- Well-formedness of an instance: every registered and unregistered vote is a strict ranking
of all `m` candidates, `c` is a candidate, and `0 < k ≤ ‖W‖`. -/
def WellFormed (i : CondorcetConstructiveControlByAddingVotersInstance) : Prop :=
  (∀ v ∈ i.2.1, v.Perm (List.range i.1)) ∧ (∀ v ∈ i.2.2.1, v.Perm (List.range i.1)) ∧
    i.2.2.2.1 < i.1 ∧ 0 < i.2.2.2.2 ∧ i.2.2.2.2 ≤ i.2.2.1.length

/-- At most `k` voters `W' ⊆ W` whose registration makes `c` the Condorcet winner of
`V ++ W'`. -/
def CondorcetConstructiveControlByAddingVotersFeasible
    (i : CondorcetConstructiveControlByAddingVotersInstance) : Prop :=
  ∃ W' : List (List ℕ), W'.Sublist i.2.2.1 ∧ W'.length ≤ i.2.2.2.2 ∧
    IsCondorcetWinner i.1 (i.2.1 ++ W') i.2.2.2.1

open Classical in
/-- CONDORCET CONSTRUCTIVE CONTROL BY ADDING VOTERS as a decision problem over bitstrings. -/
noncomputable def condorcetConstructiveControlByAddingVotersDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CondorcetConstructiveControlByAddingVotersInstance) x with
  | some i => decide (WellFormed i ∧ CondorcetConstructiveControlByAddingVotersFeasible i)
  | none => false

/-- **CONDORCET CONSTRUCTIVE CONTROL BY ADDING VOTERS is NP-complete.** Source: Bartholdi,
Tovey, and Trick (1992). -/
public theorem_wanted condorcetConstructiveControlByAddingVoters_npComplete :
    condorcetConstructiveControlByAddingVotersDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L condorcetConstructiveControlByAddingVotersDec

end MetaMathlibExt.Complexity.NPComplete.CondorcetConstructiveControlByAddingVoters
