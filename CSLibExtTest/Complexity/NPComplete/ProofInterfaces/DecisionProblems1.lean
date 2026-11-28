/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ComparativeDivisibilityDistinctDefs

namespace MetaMathlibExt.Complexity.NPComplete.ComparativeDivisibilityDistinct

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open ComparativeDivisibility (ComparativeDivisibilityInstance)

private theorem accepts_encoding (i : ComparativeDivisibilityInstance) :
    comparativeDivisibilityDistinctDec (bitEncode i) = true ↔
      WellFormed i ∧ ComparativeDivisibility.ComparativeDivisibilityFeasible i := by
  simp [comparativeDivisibilityDistinctDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : comparativeDivisibilityDistinctDec [true] = false := by
  have h : bitDecode (α := ComparativeDivisibilityInstance) [true] = none := rfl
  simp [comparativeDivisibilityDistinctDec, h]

/-- Two divides the left-hand entry but not the right-hand entry. -/
example :
    comparativeDivisibilityDistinctDec
      (bitEncode (([2], [3]) : ComparativeDivisibilityInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨?_, 2, by decide, by decide⟩
  unfold WellFormed ComparativeDivisibility.WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.ComparativeDivisibilityDistinct
