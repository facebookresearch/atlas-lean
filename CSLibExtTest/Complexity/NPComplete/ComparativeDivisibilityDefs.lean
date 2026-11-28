/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ComparativeDivisibilityDefs

namespace MetaMathlibExt.Complexity.NPComplete.ComparativeDivisibility

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : ComparativeDivisibilityInstance) :
    comparativeDivisibilityDec (bitEncode i) = true ↔
      WellFormed i ∧ ComparativeDivisibilityFeasible i := by
  simp [comparativeDivisibilityDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : comparativeDivisibilityDec [true] = false := by
  have h : bitDecode (α := ComparativeDivisibilityInstance) [true] = none := rfl
  simp [comparativeDivisibilityDec, h]

/-- Two divides both entries `2` and `4` of the first sequence and not the entry `3` of the
second. -/
example : comparativeDivisibilityDec (bitEncode (([2, 4], [3]) : ComparativeDivisibilityInstance)) =
    true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide, 2, by decide, by decide⟩

/-- Every divisor of `3` also divides `6`, so no positive integer divides more entries of `[3]`
than of `[6]`. -/
example : comparativeDivisibilityDec (bitEncode (([3], [6]) : ComparativeDivisibilityInstance)) =
    false := by
  rw [Bool.eq_false_iff, Ne, accepts_encoding]
  rintro ⟨-, c, -, h⟩
  by_cases h3 : c ∣ 3
  · have h6 : c ∣ 6 := dvd_trans h3 ⟨2, rfl⟩
    simp [h3, h6] at h
  · simp [h3] at h

end MetaMathlibExt.Complexity.NPComplete.ComparativeDivisibility
