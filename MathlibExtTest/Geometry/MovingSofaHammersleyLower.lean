/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.MovingSofaHammersleyLower
import Mathlib.Analysis.Real.Pi.Bounds

open MeasureTheory MovingSofa Real

-- The bound guarantees an actual sofa of area greater than 2.2, even without an optimizer.
example : ∃ K : Set ℂ, IsSofa K ∧ ENNReal.ofReal (11 / 5) < volume K := by
  have h : (11 / 5 : ℝ) < π / 2 + 2 / π := by
    field_simp [pi_pos]
    nlinarith [pi_gt_d2, sq_nonneg (π - 3.14)]
  have hlt := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num)).2 h
  by_contra! hle
  exact ((hlt.trans_le MovingSofaWanted.hammersley_lower).not_ge
    (iSup_le fun K ↦ iSup_le fun hK ↦ hle K hK))
