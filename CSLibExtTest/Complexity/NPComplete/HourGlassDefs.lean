/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.HourGlassDefs

namespace MetaMathlibExt.Complexity.NPComplete.HourGlass

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : HourGlassInstance) :
    hourGlassDec (bitEncode i) = true ↔ WellFormed i ∧ HourGlassFeasible i := by
  simp [hourGlassDec, bitDecode_bitEncode]

/-- The width-two hour-glass with rows `[1, 2]`, `[3]`, `[4, 5]`. -/
private abbrev glass : List (List ℕ) := [[1, 2], [3], [4, 5]]

private theorem wellFormed_glass (t : ℕ) : WellFormed (2, glass, t) :=
  (by decide : 0 < 2 ∧ glass.length = 2 * 2 - 1 ∧
    ∀ r < glass.length, (glass.getD r []).length = if r < 2 then 2 - r else r + 2 - 2)

/-- A lone continuation bit is a truncated instance encoding. -/
example : hourGlassDec [true] = false := by
  have h : bitDecode (α := HourGlassInstance) [true] = none := rfl
  simp [hourGlassDec, h]

/-- The path through cells `0, 0, 1` collects `1 + 3 + 5 = 9`. -/
example : hourGlassDec (bitEncode ((2, glass, 9) : HourGlassInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨wellFormed_glass 9, fun r => if r = 2 then 1 else 0, ?_, ?_, ?_⟩
  · intro r hr
    have : r = 0 ∨ r = 1 ∨ r = 2 := by simp at hr; omega
    rcases this with rfl | rfl | rfl <;> decide
  · intro r hr
    have : r = 0 ∨ r = 1 := by simp at hr; omega
    rcases this with rfl | rfl <;> decide
  · decide

/-- Every path collects between `8` and `10`, so the target `7` is unreachable although it is
below the largest path sum. -/
example : hourGlassDec (bitEncode ((2, glass, 7) : HourGlassInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro hacc
  obtain ⟨-, p, hp, hstep, hsum⟩ := (accepts_encoding _).1 hacc
  have h0 := hp 0 (by decide)
  have h1 := hp 1 (by decide)
  have h2 := hp 2 (by decide)
  simp only [List.getD_cons_zero, List.getD_cons_succ, List.length_cons,
    List.length_nil] at h0 h1 h2
  simp only [glass, List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero] at hsum
  have hp1 : p 1 = 0 := by omega
  have hp0 : p 0 = 0 ∨ p 0 = 1 := by omega
  have hp2 : p 2 = 0 ∨ p 2 = 1 := by omega
  rw [hp1] at hsum
  rcases hp0 with hp0 | hp0 <;> rcases hp2 with hp2 | hp2 <;> simp [hp0, hp2] at hsum

/-- The no-instance above is well formed, so it is rejected for infeasibility. -/
example : WellFormed (2, glass, 7) :=
  wellFormed_glass 7

end MetaMathlibExt.Complexity.NPComplete.HourGlass
