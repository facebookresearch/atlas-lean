/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ShikakuDefs

namespace MetaMathlibExt.Complexity.NPComplete.Shikaku

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : ShikakuInstance) :
    shikakuDec (bitEncode i) = true ↔ WellFormed i ∧ ShikakuFeasible i := by
  simp [shikakuDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : shikakuDec [true] = false := by
  have h : bitDecode (α := ShikakuInstance) [true] = none := rfl
  simp [shikakuDec, h]

/-- The `2 × 2` grid with a `2` in each row's first cell splits into the two rows, each a
`1 × 2` rectangle around its `2`. -/
example : shikakuDec (bitEncode ([[2, 0], [2, 0]] : ShikakuInstance)) = true := by
  refine (accepts_encoding _).2 ⟨⟨by decide, by decide, by decide⟩, [(0, 0, 1, 2), (1, 0, 1, 2)],
    ?_, ?_, ?_⟩ <;> decide

/-- In the `1 × 2` grid `1 0`, the empty cell must lie in a rectangle with exactly one number:
alone it has none, and with its neighbor it has area `2 ≠ 1`. -/
example : shikakuDec (bitEncode ([[1, 0]] : ShikakuInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, R, hin, hcov, hnum⟩ := (accepts_encoding _).1 h
  have hpos : 0 < (R.filter fun q => ((0 : ℕ), (1 : ℕ)) ∈ cells q).length := by
    rw [hcov 0 (by decide) 1 (by decide)]
    exact Nat.one_pos
  obtain ⟨q, hqR⟩ := List.exists_mem_of_length_pos hpos
  rw [List.mem_filter, decide_eq_true_eq] at hqR
  obtain ⟨hqR, hq01⟩ := hqR
  have hbox := hin q hqR
  have hnq := hnum q hqR
  obtain ⟨r, c, hgt, w⟩ := q
  simp only [cells, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq] at hq01
  obtain ⟨a, ha, b, hb, hra, hcb⟩ := hq01
  simp only [rows, cols, List.length_cons, List.length_nil, List.headD_cons] at hbox
  obtain ⟨rfl, rfl⟩ : r = 0 ∧ hgt = 1 := by omega
  rcases (by omega : (c = 0 ∧ w = 2) ∨ (c = 1 ∧ w = 1)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    revert hnq <;> decide

/-- Rows of different lengths make the grid malformed. -/
example : shikakuDec (bitEncode ([[1], [1, 0]] : ShikakuInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  exact absurd (((accepts_encoding _).1 h).1.2.2 [1, 0] (by simp)) (by decide)

end MetaMathlibExt.Complexity.NPComplete.Shikaku
