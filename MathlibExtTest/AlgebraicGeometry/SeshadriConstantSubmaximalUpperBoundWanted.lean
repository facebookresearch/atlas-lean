/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.SeshadriConstantSubmaximalUpperBoundWanted
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Real.Sqrt

@[expose] public section

namespace MathlibExtTest.AlgebraicGeometry.SeshadriConstantSubmaximalUpperBoundWanted

open MathlibExt.AlgebraicGeometry.SeshadriConstant
open MathlibExt.AlgebraicGeometry.SeshadriConstantWanted

/-!
# Tests for the submaximal upper bound

A numeric corollary of `submaximalUpperBound_wanted`.
-/

theorem seshadriConstant10_lt_one_third : seshadriConstant10 < 1 / 3 := by
  have hsq : (Real.sqrt 10) ^ 2 = 10 := Real.sq_sqrt (by positivity)
  have hnn : 0 ≤ Real.sqrt 10 := Real.sqrt_nonneg 10
  have h3 : (3 : ℝ) < Real.sqrt 10 := by
    by_contra hcon
    push Not at hcon
    have hle : (Real.sqrt 10) ^ 2 ≤ (3 : ℝ) ^ 2 := pow_le_pow_left₀ hnn hcon 2
    rw [hsq] at hle
    norm_num at hle
  have hdiv : 1 / Real.sqrt 10 < 1 / 3 :=
    one_div_lt_one_div_of_lt (by norm_num) h3
  calc seshadriConstant10 ≤ 1 / Real.sqrt 10 := submaximalUpperBound_wanted
    _ < 1 / 3 := hdiv

end MathlibExtTest.AlgebraicGeometry.SeshadriConstantSubmaximalUpperBoundWanted
