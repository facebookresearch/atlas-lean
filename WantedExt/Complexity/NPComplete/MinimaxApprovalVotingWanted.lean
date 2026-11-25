/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMAX APPROVAL VOTING is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.InformationTheory.Hamming
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimaxApprovalVoting

/-!
# MINIMAX APPROVAL VOTING is NP-complete

INSTANCE: a multiset `S = {s₁, …, sₙ}` of `0`-`1` strings of length `m` (votes; the `j`-th
coordinate of a vote is `1` when the voter approves candidate `j`), and two integers `k` and `d`.
QUESTION: is there a string `s ∈ {0, 1}ᵐ` with exactly `k` ones (a committee of `k` candidates)
such that the Hamming distance `H(s, sᵢ) ≤ d` for every `i = 1, …, n`?

This is the decision problem as defined by Cygan, Kowalik, Socała and Sornat. LeGrand proves
NP-completeness by a reduction from VERTEX COVER; LeGrand, Markakis and Mehta, who call the
optimization problem FSM(k), record that reduction and give a second proof of NP-hardness. The
problem is in NP: when there are no votes the question only asks whether `k ≤ m`, and otherwise
`m` is at most the length of the input, so the string `s` is a certificate of polynomial size.

A string of length `m` is a function `Fin m → Bool` (`true` for `1`), and the Hamming distance is
Mathlib's `hammingDist`. The instance lists `m`, the votes (each a `List Bool` of length `m`, read
as the function `j ↦ sᵢ[j]`), `k` and `d`; two voters may cast the same vote. `m`, `k` and `d`
use the canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **MINIMAX APPROVAL VOTING is NP-complete.** Source: LeGrand (2004); LeGrand, Markakis and
Mehta (2007); problem as defined by Cygan, Kowalik, Socała and Sornat (2017). -/
public theorem_wanted minimaxApprovalVoting_npComplete :
    minimaxApprovalVotingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimaxApprovalVotingDec

end MetaMathlibExt.Complexity.NPComplete.MinimaxApprovalVoting
