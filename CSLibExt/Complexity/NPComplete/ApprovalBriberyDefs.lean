/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# APPROVAL BRIBERY: definitions

Source:
P. Faliszewski, E. Hemaspaandra and L. A. Hemaspaandra, "How hard is bribery in elections?",
Journal of Artificial Intelligence Research 35 (2009), 485-532, doi:10.1613/jair.2676,
Theorem 4.2 (approval-bribery is NP-complete).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ApprovalBribery

/-- An instance: the number `c` of candidates, the voters' approval vectors, the distinguished
candidate `p`, and the bribe limit `k`. -/
abbrev ApprovalBriberyInstance := ℕ × List (List Bool) × ℕ × ℕ

/-- The number of approvals of candidate `x` in the votes `V`. -/
def approvals (V : List (List Bool)) (x : ℕ) : ℕ :=
  V.countP fun v => v.getD x false

/-- Candidate `p` is a winner of the approval election with `c` candidates and votes `V`: no
candidate has more approvals than `p`. -/
def IsApprovalWinner (c : ℕ) (V : List (List Bool)) (p : ℕ) : Prop :=
  ∀ x < c, approvals V x ≤ approvals V p

/-- Well-formedness of an instance: every approval vector has one entry per candidate, and `p`
is a candidate. -/
def WellFormed (i : ApprovalBriberyInstance) : Prop :=
  (∀ v ∈ i.2.1, v.length = i.1) ∧ i.2.2.1 < i.1

/-- The approval vectors of at most `k` voters can be changed so that `p` becomes a winner. -/
def ApprovalBriberyFeasible (i : ApprovalBriberyInstance) : Prop :=
  ∃ V' : List (List Bool), V'.length = i.2.1.length ∧ (∀ v ∈ V', v.length = i.1) ∧
    (i.2.1.zip V').countP (fun q => decide (q.1 ≠ q.2)) ≤ i.2.2.2 ∧
    IsApprovalWinner i.1 V' i.2.2.1

open Classical in
/-- APPROVAL BRIBERY as a decision problem over bitstrings. -/
noncomputable def approvalBriberyDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ApprovalBriberyInstance) x with
  | some i => decide (WellFormed i ∧ ApprovalBriberyFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ApprovalBribery
