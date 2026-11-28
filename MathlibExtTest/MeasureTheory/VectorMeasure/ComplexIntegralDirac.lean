/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.VectorMeasure.ComplexIntegral
import Mathlib.Tactic.NormNum

/-! Concrete checks of complex integration against Dirac measures.
The nonreal weights test the complex scalar convention, and the norm identity
includes zero scalar weights and zero function values. -/

noncomputable section
open MeasureTheory
open MathlibExt.MeasureTheory.Function
open MathlibExt.MeasureTheory.VectorMeasure

namespace MathlibExtTest.ComplexIntegralDirac

example :
    complexIntegral
      (VectorMeasure.dirac (0 : ℂ) (2 + Complex.I) +
        VectorMeasure.dirac (1 : ℂ) (-1 + Complex.I))
      (BoundedMeasurableFunction.indicatorConst ({0} : Set ℂ)
        (measurableSet_singleton 0) 3) = 6 + 3 * Complex.I := by
  rw [complexIntegral_add_measure, complexIntegral_dirac, complexIntegral_dirac]
  norm_num [BoundedMeasurableFunction.indicatorConst_apply, mul_add]

example (c z : ℂ) :
    ‖complexIntegralCLM (VectorMeasure.dirac (0 : ℂ) z)
      (BoundedMeasurableFunction.indicatorConst ({0} : Set ℂ)
        (measurableSet_singleton 0) c)‖ = ‖c‖ * ‖z‖ := by
  rw [complexIntegralCLM_apply, complexIntegral_dirac]
  simp [BoundedMeasurableFunction.indicatorConst_apply]

end MathlibExtTest.ComplexIntegralDirac
