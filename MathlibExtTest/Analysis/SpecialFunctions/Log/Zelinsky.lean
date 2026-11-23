/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Log.Zelinsky
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- The least admissible integer gives a rational upper bound for log 2.
example : Real.log 2 ≤ 89 / 128 := by
  convert log_one_add_one_div_sub_one_le 2 (by decide) using 1 <;> norm_num

-- At the next integer the logarithm is taken at a nonintegral ratio.
example : Real.log (3 / 2) ≤ 121 / 288 := by
  convert log_one_add_one_div_sub_one_le 3 (by decide) using 1 <;> norm_num
