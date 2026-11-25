/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HeightOneMultipleZetaSeries

open MetaMathlibExt

-- At order one the Hurwitz coefficients are all one, giving the depth-one zeta series.
example (s : ℂ) : multipleHurwitzZeta 1 s = heightOneMultipleZeta s 0 := by
  rw [multipleHurwitzZeta, heightOneMultipleZeta_zero]
  apply tsum_congr
  intro b
  simp [Nat.factorial_ne_zero]

-- The smallest shift cancels the integral weight. At depth one the series in n is conditional.
example :
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.Ico 2 N,
        (-1 : ℂ) ^ n / ((n : ℂ) - 1) * (∑' a : ℕ, ((a : ℂ) + 1) ^ (-(n : ℂ))))
      Filter.atTop (nhds (∫ r in (0 : ℝ)..1, multipleHurwitzZeta r 2)) := by
  simpa [heightOneMultipleZeta_zero, sub_eq_add_neg] using
    tendsto_alternating_heightOneMultipleZeta_integral (-1) (by decide) 0
