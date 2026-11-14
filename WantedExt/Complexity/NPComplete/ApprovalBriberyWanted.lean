/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# APPROVAL BRIBERY is NP-complete

Source:
P. Faliszewski, E. Hemaspaandra and L. A. Hemaspaandra, "How hard is bribery in elections?",
Journal of Artificial Intelligence Research 35 (2009), 485-532, doi:10.1613/jair.2676,
Theorem 4.2 (approval-bribery is NP-complete).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ApprovalBribery

/-!
# APPROVAL BRIBERY is NP-complete

INSTANCE: a set `C` of candidates, a collection `V` of voters specified by their approval
vectors (each voter approves or disapproves of each candidate), a distinguished candidate
`p ∈ C`, and a nonnegative integer `k`. QUESTION: is it possible to make `p` a winner of the
approval election by changing the approval vectors of at most `k` voters? In approval voting
the candidates with the most approvals win; `p` is a winner when no candidate has more
approvals than `p` (the nonunique-winner model, the paper's default). A bribed voter's approval
vector may be replaced by any approval vector. Voters are unweighted and unpriced.

The candidates are `0, ..., c - 1`, and an approval vector is a list of `c` Booleans, entry `x`
being `true` when the voter approves of candidate `x`. `V` is a list (a multiset: equal votes
may repeat), and the voters whose vectors change are the positions at which the new list
differs from the old one.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **APPROVAL BRIBERY is NP-complete.** Source: Faliszewski, Hemaspaandra and Hemaspaandra
(2009), Theorem 4.2. -/
public theorem_wanted approvalBribery_npComplete :
    approvalBriberyDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L approvalBriberyDec

end MetaMathlibExt.Complexity.NPComplete.ApprovalBribery
