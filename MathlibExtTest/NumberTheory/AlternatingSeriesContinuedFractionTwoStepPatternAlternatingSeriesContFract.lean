/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.AlternatingSeriesContinuedFractionTwoStepPatternAlternatingSeriesContFract

/-!
# Tests for the two-step pattern as an alternating series

Concrete partial quotients for small exponents and coefficient sequences, proved from
`MetaMathlibExt.twoStepPattern_alternatingSeries_contFract`.
-/

namespace MathlibExtTest.NumberTheory.AlternatingSeriesContinuedFractionTwoStepPatternAlternatingSeriesContFract

open MetaMathlibExt

/-- The head partial quotient is `ω 0`. -/
theorem test_head :
    let q := twoStepPatternDen 0 (fun n => n + 2)
    let x := ∑' i : ℕ, (-1 : ℝ) ^ i / ((q i : ℝ) * q (i + 1))
    (GenContFract.of x).partDens.get? 0 = some 2 := by
  simpa using (twoStepPattern_alternatingSeries_contFract 0 (fun n => n + 2)
    (fun _ => by omega)).2.2.1

/-- The partial quotient at index 3 is a unit. -/
theorem test_unit :
    let q := twoStepPatternDen 1 (fun _ => 1)
    let x := ∑' i : ℕ, (-1 : ℝ) ^ i / ((q i : ℝ) * q (i + 1))
    (GenContFract.of x).partDens.get? 3 = some 1 := by
  simpa using ((twoStepPattern_alternatingSeries_contFract 1 (fun _ => 1)
    (fun _ => Nat.zero_lt_one)).2.2.2 1).1

/-- At exponent zero the coefficient is independent of its denominator. -/
theorem test_zero_exponent :
    let q := twoStepPatternDen 0 (fun n => n + 2)
    let x := ∑' i : ℕ, (-1 : ℝ) ^ i / ((q i : ℝ) * q (i + 1))
    (GenContFract.of x).partDens.get? 4 = some 4 := by
  simpa using ((twoStepPattern_alternatingSeries_contFract 0 (fun n => n + 2)
    (fun _ => by omega)).2.2.2 1).2

/-- With exponent two the block coefficient includes the square of `q 3 = 5`. -/
theorem test_exponent_two :
    let q := twoStepPatternDen 2 (fun n => n + 1)
    let x := ∑' i : ℕ, (-1 : ℝ) ^ i / ((q i : ℝ) * q (i + 1))
    (GenContFract.of x).partDens.get? 4 = some 75 := by
  have h := ((twoStepPattern_alternatingSeries_contFract 2 (fun n => n + 1)
    Nat.zero_lt_succ).2.2.2 1).2
  norm_num [twoStepPatternDen] at h ⊢
  exact h

/-- The alternating series over two-step denominators is summable to its tsum. -/
theorem test_hasSum :
    let q := twoStepPatternDen 1 (fun _ => 1)
    let x := ∑' i : ℕ, (-1 : ℝ) ^ i / ((q i : ℝ) * q (i + 1))
    HasSum (fun i : ℕ => (-1 : ℝ) ^ i / ((q i : ℝ) * q (i + 1))) x :=
  (twoStepPattern_alternatingSeries_contFract 1 (fun _ => 1)
    (fun _ => Nat.zero_lt_one)).1.hasSum

end MathlibExtTest.NumberTheory.AlternatingSeriesContinuedFractionTwoStepPatternAlternatingSeriesContFract
