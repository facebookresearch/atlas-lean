/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PROPORTIONAL APPROVAL VOTING WINNER DETERMINATION: definitions

Source:
H. Aziz, S. Gaspers, J. Gudmundsson, S. Mackenzie, N. Mattei and T. Walsh, "Computational
aspects of multi-winner approval voting", Proceedings of the 14th International Conference on
Autonomous Agents and Multiagent Systems (AAMAS 2015), 107-115, doi:10.65109/nhty2001,
Theorem 2 and Corollary 1 (reduction from INDEPENDENT SET).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.NumberTheory.Harmonic.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ProportionalApprovalVotingWinner

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

end MetaMathlibExt.Complexity.NPComplete.ProportionalApprovalVotingWinner
