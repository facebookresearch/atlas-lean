/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.PopulationGenetics.WrightFStatistics
import Mathlib.Tactic.NormNum

open Domains.Biology.PopulationGenetics.WrightFStatistics

-- Both ratios on the right are nontrivial.
example :
    1 - (1 - (1 / 4 : ℝ) / (3 / 4)) =
      (1 - (1 - (1 / 4 : ℝ) / (1 / 2))) * (1 - (1 - (1 / 2 : ℝ) / (3 / 4))) :=
  hierarchical_identity (1 / 4) (1 / 2) (3 / 4) (by norm_num) (by norm_num)

-- Zero non-identity at the individual level is allowed.
example : 1 - (1 - (0 : ℝ) / 3) = (1 - (1 - (0 : ℝ) / 2)) * (1 - (1 - (2 : ℝ) / 3)) :=
  hierarchical_identity 0 2 3 (by norm_num) (by norm_num)
