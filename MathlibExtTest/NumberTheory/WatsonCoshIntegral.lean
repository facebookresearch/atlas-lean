/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.WatsonCoshIntegral

open MeasureTheory MetaMathlibExt Set

-- At b = α = 1 and β = 0 the two digamma differences give log 2.
example : (∫ x : ℝ in Ioi 0, Complex.exp (-(x : ℂ)) / Complex.cosh x) = Complex.log 2 := by
  have h := (watson_cosh_integral_digamma 1 1 0 (by norm_num) (by norm_num) (by norm_num)).2
  norm_num [Complex.digamma_one, Complex.digamma_one_half] at h ⊢
  linear_combination h

-- At β = -b and α = 0 the minus hypothesis holds, but the integrand is identically one.
example : ¬ IntegrableOn (fun x : ℝ ↦ Complex.cosh (-(x : ℂ)) / Complex.cosh x) (Ioi 0) := by
  have h (x : ℝ) : Complex.cosh (x : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_cosh]
    exact Complex.ofReal_ne_zero.mpr (Real.cosh_pos x).ne'
  simp [Complex.cosh_neg, h, IntegrableOn, integrable_const_iff, not_isFiniteMeasure_iff,
    Real.volume_Ioi]
