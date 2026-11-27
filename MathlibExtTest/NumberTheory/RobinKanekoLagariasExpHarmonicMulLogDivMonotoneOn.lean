/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RobinKanekoLagariasExpHarmonicMulLogDivMonotoneOn
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Primorial

/-!
# Tests for monotonicity of the exponential harmonic expression

Concrete comparisons and a lower bound from the second term exercise
`MetaMathlibExt.exp_harmonic_mul_log_div_monotoneOn`.
-/

namespace MathlibExtTest.NumberTheory.RobinKanekoLagariasExpHarmonicMulLogDivMonotoneOn

open Real

example : exp (harmonic 2 : ℝ) * log (harmonic 2 : ℝ) / 2 ≤
    exp (harmonic 3 : ℝ) * log (harmonic 3 : ℝ) / 3 :=
  MetaMathlibExt.exp_harmonic_mul_log_div_monotoneOn (by norm_num) (by norm_num) (by norm_num)

example : exp (harmonic 3 : ℝ) * log (harmonic 3 : ℝ) / 3 ≤
    exp (harmonic 8 : ℝ) * log (harmonic 8 : ℝ) / 8 :=
  MetaMathlibExt.exp_harmonic_mul_log_div_monotoneOn (by norm_num) (by norm_num) (by norm_num)

example (n : ℕ) (hn : 2 ≤ n) :
    exp (3 / 2) * log (3 / 2) / 2 ≤ exp (harmonic n : ℝ) * log (harmonic n : ℝ) / n := by
  have htwo : (harmonic 2 : ℝ) = 3 / 2 := by norm_num [harmonic, Finset.sum_range_succ]
  simpa only [htwo, Nat.cast_ofNat] using
    MetaMathlibExt.exp_harmonic_mul_log_div_monotoneOn (by norm_num)
      (Set.mem_Ici.mpr ((by norm_num : 1 ≤ 2).trans hn)) hn

end MathlibExtTest.NumberTheory.RobinKanekoLagariasExpHarmonicMulLogDivMonotoneOn
