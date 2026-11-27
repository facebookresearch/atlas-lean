/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.Recurrences.KJacobsthalGeneratingFunction

open MetaMathlibExt PowerSeries

-- At k = 0 the denominator has no linear term, even with signed initial values.
example :
    mk (companionKJacobsthal 0 (-2) 4) * (1 - C 2 * X ^ 2) = C (-2) + C 4 * X := by
  simpa using companionKJacobsthal_generatingFunction 0 (-2) 4

-- The linear correction is nonzero at k = 3, but the quadratic coefficient cancels.
example :
    let p := mk (companionKJacobsthal 3 (-2) 4) *
      (1 - C ((3 : ℕ) : ℤ) * X - C 2 * X ^ 2)
    coeff 1 p = 10 ∧ coeff 2 p = 0 := by
  dsimp only
  rw [companionKJacobsthal_generatingFunction]
  simp only [map_add, coeff_succ_mul_X, coeff_zero_C, coeff_succ_C, zero_add, add_zero]
  norm_num
