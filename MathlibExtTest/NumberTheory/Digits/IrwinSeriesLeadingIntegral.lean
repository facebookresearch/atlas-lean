/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.IrwinSeriesLeadingIntegral
import Mathlib.Tactic.NormNum

open MetaMathlibExt MeasureTheory

namespace IrwinSeriesLeadingIntegralTest

/-- Restating the source's exact statement, for the test below. -/
private theorem exactSource (b d : ℕ) (hb : 1 < b) (hd : d < b) (n k : ℕ) (hn : 0 < n) :
    HasSum (leadingReciprocalTerm b d (digitCount b d n + k) n)
      (∫ x in Set.Ico (0 : ℝ) 1, ((n : ℝ) + x)⁻¹ ∂irwinMeasure b d k hd) :=
  integral_eq_leadingReciprocal_hasSum b d hb hd n k hn

-- The prefix-restricted reciprocal terms are summable: the integral identity
-- gives their sum, and every `HasSum` is summable.
example : Summable (leadingReciprocalTerm 10 9 (digitCount 10 9 19 + 0) 19) :=
  (exactSource 10 9 (by norm_num) (by norm_num) 19 0 (by norm_num)).summable

-- The sum of the terms is the integral against the Irwin measure.
example (n : ℕ) (hn : 0 < n) : HasSum
    (leadingReciprocalTerm 10 0 (digitCount 10 0 n + 1) n)
    (∫ x in Set.Ico (0 : ℝ) 1, ((n : ℝ) + x)⁻¹ ∂irwinMeasure 10 0 1 (by norm_num)) :=
  exactSource 10 0 (by norm_num) (by norm_num) n 1 hn

end IrwinSeriesLeadingIntegralTest
