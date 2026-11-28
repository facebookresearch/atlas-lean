/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ShortestCommonSupersequenceFiveLettersDefs

namespace MetaMathlibExt.Complexity.NPComplete.ShortestCommonSupersequenceFiveLetters

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : ShortestCommonSupersequenceFiveLettersInstance) :
    shortestCommonSupersequenceFiveLettersDec (bitEncode i) = true ↔
      WellFormed i ∧ ShortestCommonSupersequenceFiveLettersFeasible i := by
  simp [shortestCommonSupersequenceFiveLettersDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : shortestCommonSupersequenceFiveLettersDec [true] = false := by
  have h : bitDecode (α := ShortestCommonSupersequenceFiveLettersInstance) [true] = none := rfl
  simp [shortestCommonSupersequenceFiveLettersDec, h]

/-- The strings `04` and `40` are both subsequences of `040`. -/
example : shortestCommonSupersequenceFiveLettersDec
    (bitEncode (([[0, 4], [4, 0]], 3) : ShortestCommonSupersequenceFiveLettersInstance)) =
      true := by
  refine (accepts_encoding _).2 ⟨⟨by decide, by decide⟩, [0, 4, 0], by decide, by decide, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by decide, by decide⟩

/-- No string of length `2` has both `04` and `40` as subsequences: it would have to equal each
of them. -/
example : shortestCommonSupersequenceFiveLettersDec
    (bitEncode (([[0, 4], [4, 0]], 2) : ShortestCommonSupersequenceFiveLettersInstance)) =
      false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, w, -, hlen, hsub⟩ := (accepts_encoding _).1 h
  have h1 : [0, 4].Sublist w := hsub _ (by simp)
  have h2 : [4, 0].Sublist w := hsub _ (by simp)
  have hw : w.length = 2 := le_antisymm hlen (by simpa using h1.length_le)
  have e1 := h1.eq_of_length (by simp [hw])
  have e2 := h2.eq_of_length (by simp [hw])
  simp [← e1] at e2

/-- The symbol `5` lies outside the five-letter alphabet, so the instance is malformed even
though the bound is generous. -/
example : shortestCommonSupersequenceFiveLettersDec
    (bitEncode (([[5]], 3) : ShortestCommonSupersequenceFiveLettersInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  exact absurd (((accepts_encoding _).1 h).1.1 [5] (by simp) 5 (by simp)) (by decide)

end MetaMathlibExt.Complexity.NPComplete.ShortestCommonSupersequenceFiveLetters
