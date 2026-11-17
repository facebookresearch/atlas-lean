/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Numerical.SaturatingRoundHalfUp

@[expose] public section

namespace MathlibExtTest.Analysis.Numerical.SaturatingRoundHalfUp

open MathlibExt.Analysis.Numerical.SaturatingRoundHalfUp

/-- Both full-scale endpoints are fixed points. -/
example : quantize 1 0 7 0 = 0 := by
  simpa using quantize_codePoint (Δ := (1 : ℝ)) (k := 0) one_pos (by norm_num) (by norm_num)

example : quantize 1 0 7 7 = 7 := by
  simpa using quantize_codePoint (Δ := (1 : ℝ)) (k := 7) one_pos (by norm_num) (by norm_num)

/-- Every in-range code point is a fixed point. -/
example (k : ℤ) (h0 : 0 <= k) (h7 : k <= 7) :
    quantize 1 0 7 (k : ℝ) = (k : ℝ) := by
  simpa using quantize_codePoint (Δ := (1 : ℝ)) (k := k) one_pos h0 h7

/-- A positive half-step tie rounds toward `+∞`. -/
example : quantize 1 0 7 (5 / 2 : ℝ) = 3 := by
  norm_num [quantize, code, round_eq]

/-- A negative half-step tie also rounds toward `+∞`. -/
example : quantize 1 (-4) 3 (-5 / 2 : ℝ) = -2 := by
  norm_num [quantize, code, round_eq]

/-- A one-code range is constant. -/
example (x : ℝ) : quantize 2 5 5 x = 10 := by
  have h := code_mem_Icc (kmin := 5) (kmax := 5) le_rfl 2 x
  have hc : code 2 5 5 x = 5 := le_antisymm h.2 h.1
  norm_num [quantize, hc]

/-- The input `10` is clipped into the one-code range `{0}`. -/
example : IsClipped 1 0 0 10 := by
  norm_num [IsClipped, round_eq]

/-- Clipping alone does not decide the `Delta / 2` bound: this clipped
input still meets it, with error exactly `Delta / 2`. -/
example : IsClipped 1 0 0 (1 / 2 : ℝ)
    ∧ |quantize 1 0 0 (1 / 2 : ℝ) - 1 / 2| ≤ 1 / 2 := by
  refine ⟨?_, ?_⟩ <;> norm_num [IsClipped, quantize, code, round_eq]

/-- A clipped example refutes the blanket `Delta / 2` claim. -/
example : ¬ |quantize 1 0 0 10 - 10| ≤ (1 : ℝ) / 2 := by
  norm_num [quantize, code, round_eq]

/-- Out-of-range inputs saturate to the endpoints. -/
example : quantize 1 0 7 25 = 7 := by
  norm_num [quantize, code, round_eq]

example : quantize 1 0 7 (-3 : ℝ) = 0 := by
  norm_num [quantize, code, round_eq]

/-- Three-bit signed code boundaries. -/
example : signedMinCode 3 = -4 ∧ signedMaxCode 3 = 3 := by
  refine ⟨?_, ?_⟩ <;> norm_num [signedMinCode, signedMaxCode]

example : quantize 1 (signedMinCode 3) (signedMaxCode 3) (7 / 2 : ℝ) = 3 := by
  norm_num [signedMinCode, signedMaxCode, quantize, code, round_eq]

example : quantize 1 (signedMinCode 3) (signedMaxCode 3) (-9 / 2 : ℝ) = -4 := by
  norm_num [signedMinCode, signedMaxCode, quantize, code, round_eq]

/-- An in-range instance of the `Delta / 2` bound, through the public API. -/
example : |quantize 1 0 7 (13 / 4 : ℝ) - 13 / 4| ≤ 1 / 2 :=
  abs_quantize_sub_le_of_mem_Icc one_pos (by norm_num)

/-- A signed-code instance of the in-range bound, through the public API. -/
example : |quantize 2 (signedMinCode 3) (signedMaxCode 3) (1 : ℝ) - 1| ≤ 1 := by
  have h := abs_quantize_signed_sub_le_of_mem_Icc (Δ := 2) (w := 3)
    (x := (1 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num [signedMinCode, signedMaxCode])
  norm_num at h
  exact h

/-- An instance of monotonicity through the public API. -/
example : quantize 1 0 7 (1 / 3 : ℝ) ≤ quantize 1 0 7 (5 / 3 : ℝ) :=
  quantize_mono one_pos 0 7 (by norm_num)

/-- The global bound on a clipped input: the distance to the full-scale
interval (`3`, through `Set.projIcc`) plus `Delta / 2`. The bound is not
attained here; the exact saturated error is the distance itself, as the
next example records. -/
example : |quantize 1 0 7 10 - 10|
    ≤ |10 - (Set.projIcc (0 : ℝ) 7 (by norm_num) 10 : ℝ)| + 1 / 2 := by
  have h := abs_quantize_sub_le (Δ := (1 : ℝ)) (kmin := 0) (kmax := 7)
    one_pos (by norm_num) 10
  norm_num [fullScale_le, Set.coe_projIcc] at h ⊢
  exact h

/-- Outside the full-scale interval on the saturated high side, the
error equals the interval distance exactly: both sides are `3`. -/
example : |quantize 1 0 7 10 - 10|
    = |10 - (Set.projIcc (0 : ℝ) 7 (by norm_num) 10 : ℝ)| := by
  norm_num [quantize, code, round_eq, Set.coe_projIcc]

end MathlibExtTest.Analysis.Numerical.SaturatingRoundHalfUp
