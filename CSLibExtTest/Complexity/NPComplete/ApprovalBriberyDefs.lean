/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ApprovalBriberyDefs

namespace MetaMathlibExt.Complexity.NPComplete.ApprovalBribery

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

/-- The four approval vectors over two candidates. -/
private abbrev vectors : List (List Bool) :=
  [[false, false], [false, true], [true, false], [true, true]]

private theorem mem_vectors : ∀ v : List Bool, v.length = 2 → v ∈ vectors
  | [a, b], _ => by cases a <;> cases b <;> decide

/-- With three voters and two candidates, bribed profiles range over finitely many vectors. -/
private theorem feasible_iff (V : List (List Bool)) (hV : V.length = 3) (p k : ℕ) :
    ApprovalBriberyFeasible (2, V, p, k) ↔ ∃ x ∈ vectors, ∃ y ∈ vectors, ∃ z ∈ vectors,
      (V.zip [x, y, z]).countP (fun q => decide (q.1 ≠ q.2)) ≤ k ∧
        IsApprovalWinner 2 [x, y, z] p := by
  constructor
  · rintro ⟨V', hlen, hv, hk, hw⟩
    have h3 : V'.length = 3 := hlen.trans hV
    obtain ⟨x, y, z, rfl⟩ : ∃ x y z, V' = [x, y, z] := by
      rcases V' with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, t⟩⟩⟩⟩ <;>
        first | exact ⟨_, _, _, rfl⟩ | exact absurd h3 (by simp)
    exact ⟨x, mem_vectors x (hv x (by simp)), y, mem_vectors y (hv y (by simp)),
      z, mem_vectors z (hv z (by simp)), hk, hw⟩
  · rintro ⟨x, hx, y, hy, z, hz, hk, hw⟩
    refine ⟨[x, y, z], by simp [hV], ?_, hk, hw⟩
    have hlen2 : ∀ u ∈ vectors, u.length = 2 := by decide
    intro v hv
    show v.length = 2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact hlen2 _ hx
    · exact hlen2 _ hy
    · exact hlen2 _ hz

/-- Two voters approve only candidate `0`; one bribe may let candidate `1` catch up. -/
private abbrev yes : ApprovalBriberyInstance := (2, [[true, false], [true, false]], 1, 1)

/-- Three voters approve only candidate `0`; after one bribe `0` keeps two approvals and `1`
has at most one. -/
private abbrev no : ApprovalBriberyInstance :=
  (2, [[true, false], [true, false], [true, false]], 1, 1)

/-- The decision problem accepts `yes`: bribing the first voter to approve only `1` ties the
candidates. -/
example : approvalBriberyDec (bitEncode yes) = true := by
  have hw : WellFormed yes := by unfold WellFormed; decide
  have hf : ApprovalBriberyFeasible yes :=
    ⟨[[false, true], [true, false]], rfl, by decide, by decide, by unfold IsApprovalWinner; decide⟩
  simp [approvalBriberyDec, bitDecode_bitEncode, hw, hf]

/-- Without a bribe, candidate `1` is not a winner of `yes`. -/
example : ¬ IsApprovalWinner 2 [[true, false], [true, false]] 1 := by
  unfold IsApprovalWinner; decide

/-- The decision problem rejects the well-formed instance `no`. -/
example : WellFormed no ∧ approvalBriberyDec (bitEncode no) = false := by
  have hf : ¬ ApprovalBriberyFeasible no := by
    rw [feasible_iff _ rfl]
    unfold IsApprovalWinner
    decide
  exact ⟨by unfold WellFormed; decide, by simp [approvalBriberyDec, bitDecode_bitEncode, hf]⟩

/-- A distinguished candidate outside `0, 1` is malformed, although with no voters every bound
on its approvals holds. -/
example :
    ApprovalBriberyFeasible ((2, [], 2, 0) : ApprovalBriberyInstance) ∧
      approvalBriberyDec (bitEncode ((2, [], 2, 0) : ApprovalBriberyInstance)) = false := by
  have hw : ¬ WellFormed ((2, [], 2, 0) : ApprovalBriberyInstance) := by unfold WellFormed; decide
  exact ⟨⟨[], rfl, by simp, by decide, by unfold IsApprovalWinner; decide⟩,
    by simp [approvalBriberyDec, bitDecode_bitEncode, hw]⟩

/-- A lone continuation bit is a truncated instance encoding. -/
example : approvalBriberyDec [true] = false := by
  have h : bitDecode (α := ApprovalBriberyInstance) [true] = none := rfl
  simp [approvalBriberyDec, h]

end MetaMathlibExt.Complexity.NPComplete.ApprovalBribery
