/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PROPORTIONAL APPROVAL VOTING WINNER DETERMINATION is NP-complete

Source:
H. Aziz, S. Gaspers, J. Gudmundsson, S. Mackenzie, N. Mattei and T. Walsh, "Computational
aspects of multi-winner approval voting", Proceedings of the 14th International Conference on
Autonomous Agents and Multiagent Systems (AAMAS 2015), 107-115, doi:10.65109/nhty2001,
Theorem 2 and Corollary 1 (reduction from INDEPENDENT SET).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.NumberTheory.Harmonic.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ProportionalApprovalVotingWinner

/-!
# PROPORTIONAL APPROVAL VOTING WINNER DETERMINATION is NP-complete

This is the score-threshold decision version of PAV winner determination.

INSTANCE: a set `C` of `m` candidates, approval ballots `A₁, …, Aₙ ⊆ C` (one per agent), a
committee size `k` with `1 ≤ k ≤ m`, and a nonnegative rational bound `s`.
QUESTION: is there a committee `W ⊆ C` with `|W| = k` whose PAV score
`PAV(W) = ∑ᵢ r(|W ∩ Aᵢ|)` is at least `s`, where `r(p) = 1 + 1/2 + ⋯ + 1/p`?

The source defines PAV winner determination (PAV–WD) as computing a winning set of size `k`
(a maximizer of `PAV`, with lexicographic tie-breaking). Its NP-hardness proof (the reduction
of Theorem 2, from INDEPENDENT SET, which gives Corollary 1) shows that the constructed
instance "has a winning set of size k = t scoring a total approval of at least s = deg(G)·t if
and only if G has an independent set of size t", which is NP-hardness of the threshold question
stated here; membership in NP is immediate (a committee is the certificate).

The candidates are `0, …, m - 1`, a ballot is the list of the candidates it approves (without
repetition), and `s = p / q` with `q > 0` (a negative bound would be met by every committee;
the source's bound `deg(G)·t` is a positive integer). The weight `r(p)` is Mathlib's
`harmonic p`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `m` of candidates, the ballots, the committee size `k`, and the
nonnegative bound `s` as (numerator, denominator). -/
abbrev ProportionalApprovalVotingWinnerInstance := ℕ × List (List ℕ) × ℕ × ℕ × ℕ

/-- The PAV score of the committee `W`: each agent contributes `harmonic |W ∩ Aᵢ|`. -/
def pavScore (i : ProportionalApprovalVotingWinnerInstance) (W : Finset (Fin i.1)) : ℚ :=
  (i.2.1.map fun A => harmonic (W.filter fun c : Fin i.1 => (c : ℕ) ∈ A).card).sum

/-- Well-formedness of an instance: every ballot lists distinct candidates, `1 ≤ k ≤ m`, and
the denominator of `s` is positive. -/
def WellFormed (i : ProportionalApprovalVotingWinnerInstance) : Prop :=
  (∀ A ∈ i.2.1, A.Nodup ∧ ∀ c ∈ A, c < i.1) ∧ 0 < i.2.2.1 ∧ i.2.2.1 ≤ i.1 ∧ 0 < i.2.2.2.2

/-- Some committee of `k` candidates has PAV score at least `s`. -/
def ProportionalApprovalVotingWinnerFeasible (i : ProportionalApprovalVotingWinnerInstance) :
    Prop :=
  ∃ W : Finset (Fin i.1), W.card = i.2.2.1 ∧
    ((i.2.2.2.1 : ℚ) / i.2.2.2.2) ≤ pavScore i W

open Classical in
/-- PROPORTIONAL APPROVAL VOTING WINNER DETERMINATION as a decision problem over bitstrings. -/
noncomputable def proportionalApprovalVotingWinnerDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ProportionalApprovalVotingWinnerInstance) x with
  | some i => decide (WellFormed i ∧ ProportionalApprovalVotingWinnerFeasible i)
  | none => false

/-- **PROPORTIONAL APPROVAL VOTING WINNER DETERMINATION is NP-complete.** Source: Aziz, Gaspers,
Gudmundsson, Mackenzie, Mattei and Walsh (2015), Theorem 2 and Corollary 1. -/
public theorem_wanted proportionalApprovalVotingWinner_npComplete :
    proportionalApprovalVotingWinnerDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L proportionalApprovalVotingWinnerDec

end MetaMathlibExt.Complexity.NPComplete.ProportionalApprovalVotingWinner
