/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.DistinguishingSubstringSelectionDefs

namespace MetaMathlibExt.Complexity.NPComplete.DistinguishingSubstringSelection

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open ClosestSubstring (substringAt)

private theorem accepts_encoding (i : DistinguishingSubstringSelectionInstance) :
    distinguishingSubstringSelectionDec (bitEncode i) = true ↔
      WellFormed i ∧ DistinguishingSubstringSelectionFeasible i := by
  simp [distinguishingSubstringSelectionDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : distinguishingSubstringSelectionDec [true] = false := by
  have h : bitDecode (α := DistinguishingSubstringSelectionInstance) [true] = none := rfl
  simp [distinguishingSubstringSelectionDec, h]

/-- Bad string `01`, good string `11`, `L = 1`, `k_b = 0`, `k_g = 1`: the letter `0` occurs in
the bad string and differs from every letter of the good string. -/
example :
    distinguishingSubstringSelectionDec
      (bitEncode ((2, 1, [[0, 1]], [[1, 1]], 0, 1) :
        DistinguishingSubstringSelectionInstance)) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide, fun _ => 0,
    fun _ => Nat.two_pos, ?_, ?_⟩
  · intro s hs
    obtain rfl := List.mem_singleton.1 hs
    exact ⟨0, by decide, Nat.le_of_eq (hammingDist_eq_zero.2 (funext fun k => by
      rw [Fin.fin_one_eq_zero k]; rfl))⟩
  · intro s hs j hj
    obtain rfl := List.mem_singleton.1 hs
    have hj' : j = 0 ∨ j = 1 := by simp at hj; omega
    refine Nat.one_le_iff_ne_zero.2 fun h0 => ?_
    have e := congrFun (hammingDist_eq_zero.1 h0) 0
    rcases hj' with rfl | rfl <;> simp [substringAt] at e

/-- Bad and good string both `0`, `L = 1`, `k_b = 0`, `k_g = 1`: the only center close to the
bad string is `0`, which is a substring of the good string. -/
example :
    distinguishingSubstringSelectionDec
      (bitEncode ((2, 1, [[0]], [[0]], 0, 1) :
        DistinguishingSubstringSelectionInstance)) = false := by
  cases h : distinguishingSubstringSelectionDec
      (bitEncode ((2, 1, [[0]], [[0]], 0, 1) : DistinguishingSubstringSelectionInstance)) with
  | false => rfl
  | true =>
    obtain ⟨-, t, -, hbad, hgood⟩ := (accepts_encoding _).1 h
    obtain ⟨j, hj, hd⟩ := hbad [0] (List.mem_singleton_self _)
    obtain rfl : j = 0 := by simp at hj; omega
    have := hgood [0] (List.mem_singleton_self _) 0 (by decide)
    rw [hammingDist_eq_zero.1 (Nat.le_zero.1 hd), hammingDist_self] at this
    exact absurd this (by decide)

end MetaMathlibExt.Complexity.NPComplete.DistinguishingSubstringSelection
