/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ConsensusPatternsDefs

namespace MetaMathlibExt.Complexity.NPComplete.ConsensusPatterns

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open ClosestSubstring (ClosestSubstringInstance substringAt)

private theorem accepts_encoding (i : ClosestSubstringInstance) :
    consensusPatternsDec (bitEncode i) = true ↔ WellFormed i ∧ ConsensusPatternsFeasible i := by
  simp [consensusPatternsDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : consensusPatternsDec [true] = false := by
  have h : bitDecode (α := ClosestSubstringInstance) [true] = none := rfl
  simp [consensusPatternsDec, h]

/-- The strings `01` and `11` share the letter `1`: the median `1` at start positions `1` and
`0` has total distance zero. -/
example :
    consensusPatternsDec
      (bitEncode ((2, [[0, 1], [1, 1]], 1, 0) : ClosestSubstringInstance)) = true := by
  refine (accepts_encoding _).2 ⟨?_, fun _ => 1, fun _ => Nat.one_lt_two, [1, 0], rfl, ?_, ?_⟩
  · unfold WellFormed ClosestSubstring.WellFormed
    decide
  · decide
  · exact Nat.le_refl 0

/-- The strings `0` and `1` are well formed, but no median of length one is at total distance
zero from both. -/
example :
    consensusPatternsDec
      (bitEncode ((2, [[0], [1]], 1, 0) : ClosestSubstringInstance)) = false := by
  cases h : consensusPatternsDec
      (bitEncode ((2, [[0], [1]], 1, 0) : ClosestSubstringInstance)) with
  | false => rfl
  | true =>
    obtain ⟨-, t, -, js, hlen, hpos, hsum⟩ := (accepts_encoding _).1 h
    match js, hlen with
    | [j₀, j₁], _ =>
      have h₀ : j₀ = 0 := by have := hpos ([0], j₀) (by simp); simp at this; omega
      have h₁ : j₁ = 0 := by have := hpos ([1], j₁) (by simp); simp at this; omega
      subst h₀ h₁
      simp only [List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero, Nat.le_zero, Nat.add_eq_zero_iff,
        hammingDist_eq_zero] at hsum
      have e := congrFun (hsum.1.symm.trans hsum.2) 0
      simp [substringAt] at e

end MetaMathlibExt.Complexity.NPComplete.ConsensusPatterns
