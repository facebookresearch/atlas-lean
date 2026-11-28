/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMAX APPROVAL VOTING: definitions

Source:
R. LeGrand, "Analysis of the minimax procedure", Technical Report WUCSE-2004-67, Department of
Computer Science and Engineering, Washington University in St. Louis (2004),
doi:10.7936/K78S4N92 (NP-completeness, by a reduction from VERTEX COVER);
R. LeGrand, E. Markakis and A. Mehta, "Some results on approximating the minimax solution in
approval voting", Proceedings of the 6th International Joint Conference on Autonomous Agents and
Multiagent Systems (AAMAS 2007), doi:10.1145/1329125.1329365 (problem FSM(k); NP-hardness);
M. Cygan, Ł. Kowalik, A. Socała and K. Sornat, "Approximation and parameterized complexity of
minimax approval voting", Proceedings of the 31st AAAI Conference on Artificial Intelligence
(AAAI-17), doi:10.1609/aaai.v31i1.10575 (definition of the decision problem).
-/
module

public import Mathlib.InformationTheory.Hamming
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimaxApprovalVoting

/-- An instance: the number `m` of candidates, the votes (`0`-`1` strings of length `m`), the
committee size `k` and the distance bound `d`. -/
abbrev MinimaxApprovalVotingInstance := ℕ × List (List Bool) × ℕ × ℕ

/-- Well-formedness of an instance: every vote has length `m`. -/
def WellFormed (i : MinimaxApprovalVotingInstance) : Prop :=
  ∀ v ∈ i.2.1, v.length = i.1

/-- Some string `s ∈ {0, 1}ᵐ` with exactly `k` ones is within Hamming distance `d` of every
vote. -/
def MinimaxApprovalVotingFeasible (i : MinimaxApprovalVotingInstance) : Prop :=
  ∃ s : Fin i.1 → Bool, (Finset.univ.filter fun j => s j = true).card = i.2.2.1 ∧
    ∀ v ∈ i.2.1, hammingDist s (fun j : Fin i.1 => v.getD j false) ≤ i.2.2.2

open Classical in
/-- MINIMAX APPROVAL VOTING as a decision problem over bitstrings. -/
noncomputable def minimaxApprovalVotingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimaxApprovalVotingInstance) x with
  | some i => decide (WellFormed i ∧ MinimaxApprovalVotingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimaxApprovalVoting
