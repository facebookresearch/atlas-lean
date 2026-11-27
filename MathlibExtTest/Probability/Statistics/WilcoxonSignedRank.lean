/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.WilcoxonSignedRank

open WantedExt.Probability.Statistics.WilcoxonSignedRankWanted

-- The empty family has exactly one subset, with sum zero.
example : subsetSumCount 0 0 = 1 ∧ subsetSumCount 0 1 = 0 := by
  decide +kernel

-- For three ranks, both `{3}` and `{1, 2}` have sum three.
example : subsetSumCount 3 3 = 2 := by
  decide +kernel

example : ∑ t ∈ Finset.range 4, subsetSumCount 8 t = 5 :=
  subsetSumCount_examples.2
