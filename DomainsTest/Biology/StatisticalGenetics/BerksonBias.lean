/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Domains.Biology.StatisticalGenetics.BerksonBias
import Mathlib.Tactic.NormNum

open WantedExt.Biology.StatisticalGenetics.BerksonBiasWanted

-- With all five parameters equal to 1/2, the admitted odds ratio is 7/9.
example :
    ((1 / 2 : ℝ) * (1 / 2) * (1 - (1 / 2) * (1 / 2) * (1 / 2))) *
        ((1 - 1 / 2) * (1 - 1 / 2) * (1 - 1 / 2)) /
          (((1 / 2) * (1 - 1 / 2) * (1 - (1 / 2) * (1 / 2))) *
            ((1 - 1 / 2) * (1 / 2) * (1 - (1 / 2) * (1 / 2)))) = 7 / 9 := by
  rw [(hospitalOddsRatio (1 / 2) (1 / 2) (1 / 2) (1 / 2) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1]
  norm_num

-- At t₀ = 1, people with neither disease are never admitted, so the ratio is zero.
example :
    ((1 / 2 : ℝ) * (1 / 2) * (1 - 1 * (1 / 2) * (1 / 2))) *
        ((1 - 1 / 2) * (1 - 1 / 2) * (1 - 1)) /
          (((1 / 2) * (1 - 1 / 2) * (1 - 1 * (1 / 2))) *
            ((1 - 1 / 2) * (1 / 2) * (1 - 1 * (1 / 2)))) = 0 := by
  rw [(hospitalOddsRatio (1 / 2) (1 / 2) (1 / 2) (1 / 2) 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1]
  norm_num
