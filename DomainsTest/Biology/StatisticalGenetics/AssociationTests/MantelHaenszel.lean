/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.StatisticalGenetics.AssociationTests.MantelHaenszel
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for the Mantel–Haenszel summary odds ratio
-/

open WantedExt.Biology.StatisticalGenetics.MantelHaenszelWanted

-- The stratum totals are 5 and 9, and both stratum odds ratios are 2.
example : summaryOddsRatio ![2, 3] ![1, 1] ![1, 3] ![1, 2] = 2 := by
  apply summaryOddsRatio_eq_of_common
  · intro k
    fin_cases k <;> norm_num
  · intro k
    fin_cases k <;> norm_num
  · norm_num [Fin.sum_univ_two]

-- The third stratum has positive total and zero weight, with both cross-products zero.
example : summaryOddsRatio ![2, 3, 1] ![1, 1, 0] ![1, 3, 1] ![1, 2, 0] = 2 := by
  apply summaryOddsRatio_eq_of_common
  · intro k
    fin_cases k <;> norm_num
  · intro k
    fin_cases k <;> norm_num
  · norm_num [Fin.sum_univ_three]
