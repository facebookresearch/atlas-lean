/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.AlternatingSeriesContinuedFraction

open MetaMathlibExt

-- A varying coefficient sequence distinguishes the first two three-step blocks.
example : (List.range 8).map (threeStepPatternDen 0 (fun n => n + 2)) =
    [1, 2, 3, 5, 18, 23, 41, 187] := by
  decide

-- For the two-step recurrence the coefficients occur one position earlier.
example : (List.range 6).map (twoStepPatternDen 0 (fun n => n + 2)) =
    [1, 2, 3, 11, 14, 67] := by
  decide

-- At exponent zero the coefficient in the second block is independent of its denominator.
example :
    let q := threeStepPatternDen 0 (fun n => n + 2)
    let x := ∑' i : ℕ, (-1 : ℝ) ^ i / ((q i : ℝ) * q (i + 1))
    (GenContFract.of x).partDens.get? 6 = some 4 := by
  simpa using ((threeStepPattern_alternatingSeries_contFract 0 (fun n => n + 2)
    (fun _ => by omega)).2.2.2 1).2.2

-- With exponent two the first non-unit block coefficient includes the square of q₂.
example :
    let q := threeStepPatternDen 2 (fun n => n + 1)
    let x := ∑' i : ℕ, (-1 : ℝ) ^ i / ((q i : ℝ) * q (i + 1))
    (GenContFract.of x).partDens.get? 3 = some 8 := by
  have h := ((threeStepPattern_alternatingSeries_contFract 2 (fun n => n + 1)
    Nat.zero_lt_succ).2.2.2 0).2.2
  norm_num [threeStepPatternDen] at h ⊢
  exact h
