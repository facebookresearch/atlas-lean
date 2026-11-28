/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.KMedianDefs

namespace MetaMathlibExt.Complexity.NPComplete.KMedian

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : KMedianInstance) :
    kMedianDec (bitEncode i) = true ↔ WellFormed i ∧ KMedianFeasible i := by
  simp [kMedianDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := KMedianInstance) bits = none) :
    kMedianDec bits = false := by
  simp [kMedianDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : kMedianDec [true] = false :=
  rejects_undecodable [true] rfl

/-- Opening locations `0` and `1` gives total cost `1 + 1 + 1 = 3`. -/
example :
    kMedianDec (bitEncode (([[1, 5], [5, 1], [1, 4]], 2, 3) : KMedianInstance)) = true := by
  apply (accepts_encoding _).2
  exact ⟨by unfold WellFormed; decide, [0, 1], by decide, by decide, by decide,
    [0, 1, 0], rfl, by decide, by decide⟩

/-- One location costs `7` (location `0`) or `10` (location `1`), above the budget `6`. -/
example :
    kMedianDec (bitEncode (([[1, 5], [5, 1], [1, 4]], 1, 6) : KMedianInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, fs, -, hlen, hlt, assign, -, hmem, hsum⟩
  rcases fs with _ | ⟨x, _ | ⟨y, fs⟩⟩
  · simpa using hmem 0 (by decide)
  · have hx : x < 2 := hlt x (by simp)
    have h0 : assign.getD 0 0 = x := by simpa using hmem 0 (by decide)
    have h1 : assign.getD 1 0 = x := by simpa using hmem 1 (by decide)
    have h2 : assign.getD 2 0 = x := by simpa using hmem 2 (by decide)
    simp only [List.length_cons, List.length_nil, zero_add, Finset.sum_range_succ,
      Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ, h0, h1, h2] at hsum
    rcases x with _ | _ | x
    · simp at hsum
    · simp at hsum
    · omega
  · simp at hlen

/-- Rows of different lengths are malformed. -/
example :
    kMedianDec (bitEncode (([[0], [0, 0]], 1, 0) : KMedianInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨h, -⟩
  exact absurd (h [0] (by simp) [0, 0] (by simp)) (by decide)

end MetaMathlibExt.Complexity.NPComplete.KMedian
