/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ShapleyShubikVotingPowerDefs

namespace MetaMathlibExt.Complexity.NPComplete.ShapleyShubikVotingPower

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : ShapleyShubikVotingPowerInstance) :
    shapleyShubikVotingPowerDec (bitEncode i) = true ↔
      WellFormed i ∧ ShapleyShubikVotingPowerFeasible i := by
  simp [shapleyShubikVotingPowerDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : shapleyShubikVotingPowerDec [true] = false := by
  have h : bitDecode (α := ShapleyShubikVotingPowerInstance) [true] = none := rfl
  simp [shapleyShubikVotingPowerDec, h]

/-- A rearrangement of a list of two distinct entries is one of its two orders. -/
private theorem perm_two {α : Type} {s : List α} {x y : α} (hxy : x ≠ y) (h : s.Perm [x, y]) :
    s = [x, y] ∨ s = [y, x] := by
  have hlen := h.length_eq
  have hnd : s.Nodup := h.nodup_iff.2 (by simp [hxy])
  match s, hlen with
  | [a, b], _ =>
    have ha : a ∈ [x, y] := h.subset (by simp)
    have hb : b ∈ [x, y] := h.subset (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    have hab : a ≠ b := by simpa using hnd
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all

/-- With three voters of one vote each and quota `2`, voter `0` is pivotal in the order
`1, 0, 2`: one vote before it, two once it joins. -/
example : shapleyShubikVotingPowerDec
    (bitEncode (([1, 1, 1], 2) : ShapleyShubikVotingPowerInstance)) = true := by
  refine (accepts_encoding _).2
    ⟨by unfold WellFormed; decide, [1, 0, 2], ?_, 1, rfl, by decide, by decide⟩
  exact List.Perm.swap 0 1 [2]

/-- With votes `1, 3` and quota `3`, voter `0` is a dummy: first it brings only `1` vote, and
second the quota is already met before it joins. -/
example : shapleyShubikVotingPowerDec
    (bitEncode (([1, 3], 3) : ShapleyShubikVotingPowerInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, π, hπ, j, hj, hlt, hge⟩ := (accepts_encoding _).1 h
  have hπ' : π.Perm [0, 1] := hπ
  rcases perm_two (by decide) hπ' with rfl | rfl <;> rcases j with _ | _ | j <;> simp_all

/-- A voter with no votes makes the instance malformed. -/
example : shapleyShubikVotingPowerDec
    (bitEncode (([0, 3], 3) : ShapleyShubikVotingPowerInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  exact absurd (((accepts_encoding _).1 h).1.2.1 0 (by simp)) (by decide)

end MetaMathlibExt.Complexity.NPComplete.ShapleyShubikVotingPower
