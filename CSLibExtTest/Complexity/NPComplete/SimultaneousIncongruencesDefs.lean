/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.SimultaneousIncongruencesDefs

namespace MetaMathlibExt.Complexity.NPComplete.SimultaneousIncongruences

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : SimultaneousIncongruencesInstance) :
    simultaneousIncongruencesDec (bitEncode i) = true ↔
      WellFormed i ∧ SimultaneousIncongruencesFeasible i := by
  simp [simultaneousIncongruencesDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : simultaneousIncongruencesDec [true] = false := by
  have h : bitDecode (α := SimultaneousIncongruencesInstance) [true] = none := rfl
  simp [simultaneousIncongruencesDec, h]

/-- `x = 0` avoids `1 (mod 2)` and `2 (mod 3)`. -/
example : simultaneousIncongruencesDec
    (bitEncode ([(1, 2), (2, 3)] : SimultaneousIncongruencesInstance)) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide, 0, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by decide, by decide⟩

/-- Every integer is `1` or `2` modulo `2`, so `1 (mod 2)` and `2 (mod 2)` cannot both be
avoided. -/
example : simultaneousIncongruencesDec
    (bitEncode ([(1, 2), (2, 2)] : SimultaneousIncongruencesInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, x, hx⟩ := (accepts_encoding _).1 h
  have h1 := hx (1, 2) (by simp)
  have h2 := hx (2, 2) (by simp)
  simp only [Int.ModEq, Nat.cast_ofNat] at h1 h2
  omega

/-- A residue `0` is outside the well-formed range `0 < aᵢ`. -/
example : simultaneousIncongruencesDec
    (bitEncode ([(0, 2)] : SimultaneousIncongruencesInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  exact absurd (((accepts_encoding _).1 h).1 (0, 2) (by simp)).1 (by decide)

end MetaMathlibExt.Complexity.NPComplete.SimultaneousIncongruences
