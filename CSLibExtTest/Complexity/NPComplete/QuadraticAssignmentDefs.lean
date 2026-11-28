/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.QuadraticAssignmentDefs

namespace MetaMathlibExt.Complexity.NPComplete.QuadraticAssignment

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : QuadraticAssignmentInstance) :
    quadraticAssignmentDec (bitEncode i) = true ↔
      WellFormed i ∧ QuadraticAssignmentFeasible i := by
  simp [quadraticAssignmentDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : quadraticAssignmentDec [true] = false := by
  have h : bitDecode (α := QuadraticAssignmentInstance) [true] = none := rfl
  simp [quadraticAssignmentDec, h]

/-- The single flow from facility `0` to facility `1` costs one under the identity placement,
since location `0` is at distance one from location `1`. -/
example :
    quadraticAssignmentDec
      (bitEncode ((2, [[0, 1], [0, 0]], [[0, 1], [5, 0]], 1) : QuadraticAssignmentInstance)) =
        true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, [0, 1], by decide, by decide⟩

/-- Both placements of the two facilities cost at least one, above the bound zero. -/
example :
    quadraticAssignmentDec
      (bitEncode ((2, [[0, 1], [0, 0]], [[0, 1], [5, 0]], 0) : QuadraticAssignmentInstance)) =
        false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨perm, hp, hcost⟩ := ((accepts_encoding _).1 h).2
  have hlen : perm.length = 2 := by simpa using hp.length_eq
  rcases perm with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> simp at hlen
  have ha : a ∈ List.range 2 := hp.subset (by simp)
  have hb : b ∈ List.range 2 := hp.subset (by simp)
  have hab : [a, b].Nodup := hp.nodup_iff.2 List.nodup_range
  simp only [List.mem_range, List.nodup_cons, List.mem_singleton, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at ha hb hab
  rcases (by omega : a = 0 ∧ b = 1 ∨ a = 1 ∧ b = 0) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    revert hcost <;> decide

/-- A flow matrix with a missing row is malformed. -/
example :
    quadraticAssignmentDec
      (bitEncode ((2, [[0, 1]], [[0, 1], [5, 0]], 9) : QuadraticAssignmentInstance)) =
        false := by
  rw [Bool.eq_false_iff]
  intro h
  have hw := ((accepts_encoding _).1 h).1
  revert hw
  unfold WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.QuadraticAssignment
