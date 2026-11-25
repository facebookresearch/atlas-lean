/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.IntegralLogOnePlusOverOnePlusSq
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MathlibExt.Analysis.SpecialFunctions.IntegralLogOnePlusOverOnePlusSqWanted

-- The integral can also be written using the logarithm of the positive square root.
example : (∫ x in 0..1, Real.log (1 + x) / (1 + x ^ 2)) =
    (Real.pi / 4) * Real.log (Real.sqrt 2) := by
  rw [integral_log_one_add_div_one_add_sq, Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring
