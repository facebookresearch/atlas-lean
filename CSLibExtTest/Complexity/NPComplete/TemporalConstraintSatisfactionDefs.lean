/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.TemporalConstraintSatisfactionDefs

namespace MetaMathlibExt.Complexity.NPComplete.TemporalConstraintSatisfaction

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : TemporalConstraintSatisfactionInstance) :
    temporalConstraintSatisfactionDec (bitEncode i) = true ↔
      WellFormed i ∧ TemporalConstraintSatisfactionFeasible i := by
  simp [temporalConstraintSatisfactionDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : temporalConstraintSatisfactionDec [true] = false := by
  have h : bitDecode (α := TemporalConstraintSatisfactionInstance) [true] = none := rfl
  simp [temporalConstraintSatisfactionDec, h]

/-- `X₀ ∈ [0, 0]` and `X₁ - X₀ ∈ [1, 2]` hold at `X₀ = 0`, `X₁ = 1`. -/
example :
    temporalConstraintSatisfactionDec
      (bitEncode ((2, [(0, [((0, 0, 1), (0, 0, 1))])], [(0, 1, [((1, 0, 1), (2, 0, 1))])]) :
        TemporalConstraintSatisfactionInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨?_, fun k => (k : ℝ), ?_, ?_⟩
  · simp only [WellFormed, IntervalOK, Endpoint.val]
    refine ⟨?_, ?_⟩ <;> intro c hc <;> simp at hc <;> subst hc <;> norm_num
  · simp [InSome, Endpoint.val]
  · simp [InSome, Endpoint.val]

/-- `X₁ - X₀ ∈ [1, 2]` and `X₀ - X₁ ∈ [1, 2]` contradict each other: the two differences
sum to zero. -/
example :
    temporalConstraintSatisfactionDec
      (bitEncode ((2, [], [(0, 1, [((1, 0, 1), (2, 0, 1))]), (1, 0, [((1, 0, 1), (2, 0, 1))])]) :
        TemporalConstraintSatisfactionInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, X, -, hX⟩
  have h01 := hX (0, 1, [((1, 0, 1), (2, 0, 1))]) (by simp)
  have h10 := hX (1, 0, [((1, 0, 1), (2, 0, 1))]) (by simp)
  simp [InSome, Endpoint.val] at h01 h10
  have h := add_le_add h01.1 h10.1
  norm_num at h
  exact absurd h (by norm_num)

/-- The rejected network is well formed, so the rejection comes from inconsistency. -/
example :
    WellFormed ((2, [], [(0, 1, [((1, 0, 1), (2, 0, 1))]), (1, 0, [((1, 0, 1), (2, 0, 1))])]) :
      TemporalConstraintSatisfactionInstance) := by
  simp only [WellFormed, IntervalOK, Endpoint.val]
  refine ⟨?_, ?_⟩ <;> intro c hc <;> simp at hc
  rcases hc with rfl | rfl <;> norm_num

end MetaMathlibExt.Complexity.NPComplete.TemporalConstraintSatisfaction
