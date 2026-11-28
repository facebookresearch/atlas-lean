/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.OpenHemisphereDefs

namespace MetaMathlibExt.Complexity.NPComplete.OpenHemisphere

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : OpenHemisphereInstance) :
    openHemisphereDec (bitEncode i) = true ↔ WellFormed i ∧ OpenHemisphereFeasible i := by
  simp [openHemisphereDec, bitDecode_bitEncode]

/-- The one-dimensional points `1`, `2` and `-1`. -/
private abbrev points : List (List (ℕ × ℕ)) := [[(1, 0)], [(2, 0)], [(0, 1)]]

/-- A lone continuation bit is a truncated instance encoding. -/
example : openHemisphereDec [true] = false := by
  have h : bitDecode (α := OpenHemisphereInstance) [true] = none := rfl
  simp [openHemisphereDec, h]

/-- The direction `y = 1` has positive inner product with the two points `1` and `2`. -/
example : openHemisphereDec (bitEncode ((1, points, 2) : OpenHemisphereInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed intOf; decide, fun _ => 1, ?_⟩
  simp [intOf]

/-- No direction is positive on both `1` and `-1`, so all three points never fit in one open
hemisphere. -/
example : openHemisphereDec (bitEncode ((1, points, 3) : OpenHemisphereInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro hacc
  obtain ⟨-, y, hK⟩ := (accepts_encoding _).1 hacc
  by_cases h₁ : (0 : ℚ) < y 0 <;> by_cases h₂ : (0 : ℚ) < 2 * y 0 <;>
    by_cases h₃ : (0 : ℚ) < -y 0 <;> simp [intOf, h₁, h₂, h₃] at hK

/-- The no-instance above is well formed, so it is rejected for infeasibility. -/
example : WellFormed ((1, points, 3) : OpenHemisphereInstance) :=
  by unfold WellFormed intOf; decide

end MetaMathlibExt.Complexity.NPComplete.OpenHemisphere
