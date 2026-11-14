/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TOURNAMENT FIXING (balanced knockout tournaments) is NP-complete

Source:
H. Aziz, S. Gaspers, S. Mackenzie, N. Mattei, P. Stursberg and T. Walsh, "Fixing a balanced
knockout tournament", Proceedings of the Twenty-Eighth AAAI Conference on Artificial
Intelligence (AAAI 2014), 552-558, doi:10.1609/aaai.v28i1.8805, Theorem 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BalancedKnockoutTournamentFixing

/-!
# TOURNAMENT FIXING (balanced knockout tournaments) is NP-complete

The TOURNAMENT FIXING PROBLEM (TFP). INSTANCE: a player set `N = [n]` with `n = 2^c` for some
integer `c`, a deterministic pairwise comparison matrix `P` (for distinct players `j` and `k`,
exactly one of them beats the other), and a distinguished player `i*`. QUESTION: does there
exist a draw for `N` for which `i*` is the winner of the balanced knockout tournament?

A balanced knockout tournament is a balanced binary tree with `n` leaves labelled by the
players. Players at sibling leaves play a match against each other, the winner proceeds up the
tree to the next round, and the winner of the tournament is the player who reaches the root.
The question is equivalent to asking for a seeding (a labelling of the leaves) under which `i*`
wins, which is how it is stated here: a seeding is the list of the players in leaf order, a
permutation of `0, ..., n - 1`; the first round pairs the leaves `(0, 1), (2, 3), ...`, and the
tournament on `2^(r + 1)` leaves is the final between the winners of the tournaments on its two
halves of `2^r` leaves.

The instance gives `c`, the comparison matrix as the list of the pairs `(j, k)` such that `j`
beats `k`, and `i*`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `c` of rounds (there are `2^c` players `0, ..., 2^c - 1`), the pairs
`(j, k)` such that player `j` beats player `k`, and the distinguished player `i*`. -/
abbrev BalancedKnockoutTournamentFixingInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: the listed pairs, without repetition, name two distinct
players, at most one of `(j, k)` and `(k, j)` is listed, every two distinct players are listed
in one of the two orders, and `i*` is a player. -/
def WellFormed (i : BalancedKnockoutTournamentFixingInstance) : Prop :=
  i.2.1.Nodup ∧
    (∀ e ∈ i.2.1, e.1 < 2 ^ i.1 ∧ e.2 < 2 ^ i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (∀ j < 2 ^ i.1, ∀ k < 2 ^ i.1, j ≠ k → (j, k) ∈ i.2.1 ∨ (k, j) ∈ i.2.1) ∧
    i.2.2 < 2 ^ i.1

/-- The winner of the balanced knockout tournament with `r` rounds whose leaves, in order, are
labelled by the list `s` of `2^r` players: for `r = 0` the single player, and for `r + 1` the
winner of the final between the winners of the first and the second `2^r` leaves (the first
finalist proceeds when it beats the second, otherwise the second does). -/
def knockoutWinner (i : BalancedKnockoutTournamentFixingInstance) : ℕ → List ℕ → ℕ
  | 0, s => s.headD 0
  | r + 1, s =>
    let x := knockoutWinner i r (s.take (2 ^ r))
    let y := knockoutWinner i r (s.drop (2 ^ r))
    if (x, y) ∈ i.2.1 then x else y

/-- Some seeding of the `2^c` players makes `i*` the winner of the balanced knockout
tournament. -/
def BalancedKnockoutTournamentFixingFeasible (i : BalancedKnockoutTournamentFixingInstance) :
    Prop :=
  ∃ s : List ℕ, s.Perm (List.range (2 ^ i.1)) ∧ knockoutWinner i i.1 s = i.2.2

open Classical in
/-- TOURNAMENT FIXING (balanced knockout tournaments) as a decision problem over bitstrings. -/
noncomputable def balancedKnockoutTournamentFixingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BalancedKnockoutTournamentFixingInstance) x with
  | some i => decide (WellFormed i ∧ BalancedKnockoutTournamentFixingFeasible i)
  | none => false

/-- **TOURNAMENT FIXING (balanced knockout tournaments) is NP-complete.** Source: Aziz,
Gaspers, Mackenzie, Mattei, Stursberg and Walsh (2014), Theorem 1. -/
public theorem_wanted balancedKnockoutTournamentFixing_npComplete :
    balancedKnockoutTournamentFixingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L balancedKnockoutTournamentFixingDec

end MetaMathlibExt.Complexity.NPComplete.BalancedKnockoutTournamentFixing
