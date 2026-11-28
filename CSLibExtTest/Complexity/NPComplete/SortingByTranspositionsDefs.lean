/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.SortingByTranspositionsDefs

namespace MetaMathlibExt.Complexity.NPComplete.SortingByTranspositions

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : SortingByTranspositionsInstance) :
    sortingByTranspositionsDec (bitEncode i) = true ↔
      WellFormed i ∧ SortingByTranspositionsFeasible i := by
  simp [sortingByTranspositionsDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : sortingByTranspositionsDec [true] = false := by
  have h : bitDecode (α := SortingByTranspositionsInstance) [true] = none := rfl
  simp [sortingByTranspositionsDec, h]

private theorem wellFormed_0213 : WellFormed ([0, 2, 1, 3], 0) := by
  refine ⟨by decide, ?_, rfl, rfl⟩
  exact List.Perm.cons _ (List.Perm.swap _ _ _)

/-- `[0, 2, 1, 3]` is sorted by the single transposition `τ_{1,2,3}`, which exchanges the factors
`[2]` and `[1]`. -/
example : sortingByTranspositionsDec
    (bitEncode (([0, 2, 1, 3], 1) : SortingByTranspositionsInstance)) = true := by
  refine (accepts_encoding _).2 ⟨wellFormed_0213, [(1, 2, 3)], le_rfl, by decide, by decide⟩

/-- With budget `0`, the unsorted permutation `[0, 2, 1, 3]` is a no-instance. -/
example : sortingByTranspositionsDec
    (bitEncode (([0, 2, 1, 3], 0) : SortingByTranspositionsInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, ops, hlen, -, hsort⟩ := (accepts_encoding _).1 h
  obtain rfl : ops = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
  exact absurd hsort (by decide)

/-- A permutation that does not fix `0` is malformed. -/
example : sortingByTranspositionsDec
    (bitEncode (([1, 0], 5) : SortingByTranspositionsInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  exact absurd ((accepts_encoding _).1 h).1.2.2.1 (by decide)

end MetaMathlibExt.Complexity.NPComplete.SortingByTranspositions
