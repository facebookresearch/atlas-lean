/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Asymptotics.TaylorsLaw
import Mathlib.Tactic

namespace MetaMathlibExt

open scoped BigOperators

/-- The public predicate uses one-based samples and the unbiased `n - 1` denominator. -/
example (a : ℕ → ℕ) :
    SatisfiesTaylorsLawAsymptotically a ↔
      IsTaylorAdmissibleSequence a ∧
      ∃ c b : ℝ, 0 < c ∧
        Filter.Tendsto
          (fun n : ℕ => initialSegmentSampleVariance a n /
            Real.rpow (initialSegmentMean a n) b)
          Filter.atTop (nhds c) := by
  rfl

/-- At sample size two, the canonical mean uses exactly `a 1` and `a 2`. -/
example (a : ℕ → ℕ) :
    initialSegmentMean a 2 = ((a 1 : ℝ) + a 2) / 2 := by
  norm_num [initialSegmentMean, Finset.sum_range_succ]
  ring

/-- The inverse-zero convention makes the one-sample canonical variance total and equal to zero. -/
example (a : ℕ → ℕ) : initialSegmentSampleVariance a 1 = 0 := by
  simp [initialSegmentSampleVariance]

end MetaMathlibExt
