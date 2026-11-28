/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.MovingSofaHammersley

open MeasureTheory MovingSofa Set

-- This rectangle fits the entrance strip, but its area rules out a passage.
example : ¬ IsSofa (Complex.measurableEquivRealProd ⁻¹' (Icc (0 : ℝ) 3 ×ˢ Icc (0 : ℝ) 1)) := by
  intro h
  have harea : volume _ ≤ optimalArea := le_iSup_of_le _ (le_iSup_of_le h le_rfl)
  have hle := harea.trans MovingSofaWanted.hammersley_upper
  rw [Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv] at hle
  simp only [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, sub_zero,
    ENNReal.ofReal_one, mul_one] at hle
  have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle
  nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
