/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LurothConsecutiveDigitsIntegral
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open Filter MeasureTheory MetaMathlibExt Set
open scoped ENNReal

-- A threshold above a constant function gives zero superlevel integrals in two dimensions.
example : volume {x ∈ Ioc (0 : ℝ) 1 | ∃ᶠ _n : ℕ in atTop, (2 : ℝ) ≤ 1} = 0 := by
  apply (volume_lurothConsecutiveDigits_zero_one_integral (m := 2) (fun _ => 1)
    measurable_const (fun _ _ => zero_lt_one) monotoneOn_const 1
    (by simp) (fun _ => 2)).1
  simp

-- In dimension zero the empty product has mass one. A negative threshold is allowed.
example : volume {x ∈ Ioc (0 : ℝ) 1 | ∃ᶠ _n : ℕ in atTop, (-1 : ℝ) ≤ 1} = 1 := by
  apply (volume_lurothConsecutiveDigits_zero_one_integral (m := 0) (fun _ => 1)
    measurable_const (fun _ _ => zero_lt_one) monotoneOn_const 2
    (by norm_num) (fun _ => -1)).2
  norm_num [MeasureTheory.volume_pi, Measure.pi_univ]
