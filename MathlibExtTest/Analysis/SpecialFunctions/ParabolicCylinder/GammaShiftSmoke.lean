/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.Analysis.SpecialFunctions.ParabolicCylinder.GammaProduct

public section

noncomputable section

open Complex

-- The shifted identity is valid at s=-1, although Gamma(s) itself is totalized at a pole.
example : parabolicCylinderU (1 / 2 : ℂ) 0 =
    (2 : ℂ) ^ (-1 / 2 : ℂ) * Gamma (1 / 2) := by
  have h := Gamma_mul_parabolicCylinderU_zero_shift_two (-1 : ℂ) (by norm_num)
  have harg : (-1 : ℂ) + 3 / 2 = 1 / 2 := by ring
  have hpower : (-1 : ℂ) / 2 = -1 / 2 := by ring
  have hgamma : (-1 : ℂ) + 2 = 1 := by ring
  have hlast : (-1 : ℂ) / 2 + 1 = 1 / 2 := by ring
  simpa only [harg, hpower, hgamma, hlast, Gamma_one, one_mul] using h

-- Its positive-half-plane specialization computes the order-3/2 value without cancellation.
example : parabolicCylinderU (3 / 2 : ℂ) 0 = 1 := by
  have h := Gamma_mul_parabolicCylinderU_zero_shift_two (0 : ℂ) (by norm_num)
  norm_num at h
  exact h
