/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.Bayesian.BetaBernoulliFeatures

open MeasureTheory ProbabilityTheory Cslib.MachineLearning.Bayesian
  Cslib.MachineLearning.Bayesian.BetaBernoulliFeatures MathlibExt.Probability.IndianBuffet

-- With `α = 2` and `K = 2` features, an entry is one with probability `1/2`.
example : (binomialKernel 1 ∘ₘ betaMeasure ((2 : ℝ) / (2 : ℕ)) 1).real {1} = 1 / 2 := by
  rw [entry_prob (by norm_num) (by norm_num)]
  norm_num

-- The closed form for `N = 3`, `K = 2`, `α = 2` is `3 · 2 · 1/2 = 3`.
example : expectedOnes 2 3 2 = 3 := by
  rw [expectedOnes_eq_mul_entry_prob (by norm_num) 3 (by norm_num),
    entry_prob (by norm_num) (by norm_num)]
  norm_num
