/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GoldenRatioLeftFactorialLambertKurepaPartialIntegralGoldenFactorialExponentBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.NumberTheory.Real.GoldenRatio
import MathlibExt.NumberTheory.GoldenRatioLambertSequence

/-!
# Tests for left factorial bounds at the golden factorial exponent

We specialize the bounds at two and derive that the left factorial deficit lies
strictly between zero and one.
-/

namespace MathlibExtTest.NumberTheory

namespace GoldenRatioLeftFactorialLambertKurepaPartialIntegralGoldenFactorialExponentBounds

open MetaMathlibExt

example : kurepaPartialIntegral 2 2 < 2 ∧ 2 < kurepaPartialIntegral 2 2 + 1 := by
  have hs : (∑ k ∈ Finset.range 2, (k.factorial : ℝ)) = 2 := by
    norm_num [Finset.sum_range_succ]
  simpa only [goldenFactorialExponent_two, Nat.cast_ofNat, hs] using
    kurepaPartialIntegral_goldenFactorialExponent_bounds 2 (by norm_num)

example (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.range n, (k.factorial : ℝ)) -
      kurepaPartialIntegral n (goldenFactorialExponent n) ∈ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨hl, hu⟩ := kurepaPartialIntegral_goldenFactorialExponent_bounds n hn
  constructor <;> linarith

end GoldenRatioLeftFactorialLambertKurepaPartialIntegralGoldenFactorialExponentBounds

end MathlibExtTest.NumberTheory
