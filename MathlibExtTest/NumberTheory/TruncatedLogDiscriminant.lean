/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum.Prime
import MathlibExt.NumberTheory.TruncatedLogDiscriminant

open MetaMathlibExt

example : truncatedLogPolynomial 0 = 1 := by
  simp [truncatedLogPolynomial]

example : ¬ IsSquare (truncatedLogPolynomial 6).discr :=
  not_isSquare_discr_truncatedLog_three_five_seven_mul (q := 2) (hq := by decide)
    (hn := Or.inl rfl)

example : ¬ IsSquare (truncatedLogPolynomial 25).discr :=
  not_isSquare_discr_truncatedLog_three_five_seven_mul (q := 5) (hq := by decide)
    (hn := Or.inr (Or.inl rfl))

example : ¬ IsSquare (truncatedLogPolynomial 15005).discr :=
  not_isSquare_discr_truncatedLog_three_five_seven_mul (q := 3001) (hq := by norm_num)
    (hn := Or.inr (Or.inl rfl))

example : ¬ IsSquare (truncatedLogPolynomial 77).discr :=
  not_isSquare_discr_truncatedLog_three_five_seven_mul (q := 11) (hq := by decide)
    (hn := Or.inr (Or.inr rfl))
