/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.KSupplierDefs

namespace MetaMathlibExt.Complexity.NPComplete.KSupplier

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : KSupplierInstance) :
    kSupplierDec (bitEncode i) = true ↔ WellFormed i ∧ KSupplierFeasible i := by
  simp [kSupplierDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := KSupplierInstance) bits = none) :
    kSupplierDec bits = false := by
  simp [kSupplierDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : kSupplierDec [true] = false :=
  rejects_undecodable [true] rfl

/-- Two vertices at distance `3`, each costing `2`: building both (cost `4`) serves each vertex
at weighted distance `0`. -/
example :
    kSupplierDec (bitEncode
      ((2, [[0, 3], [3, 0]], [2, 2], [1, 1], 4, 1) : KSupplierInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed distance; decide, {0, 1}, by decide, by decide, ?_⟩
  unfold distance
  decide

/-- With budget `2` only one supplier can be built, and the other vertex is at weighted
distance `3 > 2`. -/
example :
    kSupplierDec (bitEncode
      ((2, [[0, 3], [3, 0]], [2, 2], [1, 1], 2, 2) : KSupplierInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, S, hlt, hcost, hserve⟩
  have hin : ∀ v < 2, v ∈ S := by
    intro v hv
    obtain ⟨s, hs, hd⟩ := hserve v hv
    have := hlt s hs
    unfold distance at hd
    rcases v with _ | _ | v <;> rcases s with _ | _ | s <;> simp at hd <;> omega
  have hsub : ({0, 1} : Finset ℕ) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hin 0 (by decide)
    · exact hin 1 (by decide)
  have := Finset.sum_sdiff (f := fun s => [2, 2].getD s 0) hsub
  simp only at hcost this
  rw [Finset.sum_pair (by decide)] at this
  simp only [List.getD_cons_zero, List.getD_cons_succ] at this
  omega

/-- A zero radius bound is malformed. -/
example :
    kSupplierDec (bitEncode
      ((2, [[0, 3], [3, 0]], [2, 2], [1, 1], 4, 0) : KSupplierInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨⟨-, -, -, -, -, -, -, h⟩, -⟩
  exact absurd h (by decide)

end MetaMathlibExt.Complexity.NPComplete.KSupplier
