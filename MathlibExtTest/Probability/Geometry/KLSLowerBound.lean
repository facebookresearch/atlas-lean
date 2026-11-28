/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Geometry.KLSLowerBound
import Mathlib.Analysis.Real.Pi.Bounds

open MathlibExt.Probability.KLS

-- In particular a dimension-independent upper bound of one is impossible.
example : 1 < klsConstant := by
  refine lt_of_lt_of_le ?_ sqrtPiDivTwo_le_klsConstant
  rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff_of_nonneg zero_le_one]
  exact (Real.lt_sqrt zero_le_one).2 (by linarith [Real.pi_gt_three])
