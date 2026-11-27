/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.KJacobsthalIntegralCompanionKJacobsthalCatalan
import Mathlib.Tactic.NormNum

/-! # Tests for Catalan's identity for the companion $k$-Jacobsthal numbers -/

namespace MathlibExtTest.NumberTheory.Recurrences.KJacobsthalIntegralCompanionKJacobsthalCatalan

open MetaMathlibExt

-- The Jacobsthal case, where the integer power has a nonnegative exponent.
example : ((companionKJacobsthal 1 0 1 (3 - 1) * companionKJacobsthal 1 0 1 (3 + 1) -
    companionKJacobsthal 1 0 1 3 ^ 2 : ℤ) : ℚ) = -4 := by
  have h := companionKJacobsthal_catalan 1 0 1 3 1 (by decide)
  rw [h]
  norm_num [lucasU, kJacobsthalParams]

-- A companion case with `r = n`, so the integer power has a negative exponent.
example : ((companionKJacobsthal 2 1 1 (2 - 2) * companionKJacobsthal 2 1 1 (2 + 2) -
    companionKJacobsthal 2 1 1 2 ^ 2 : ℤ) : ℚ) = 12 := by
  have h := companionKJacobsthal_catalan 2 1 1 2 2 (by decide)
  rw [h]
  norm_num [lucasU_kJacobsthalParams_two]

end MathlibExtTest.NumberTheory.Recurrences.KJacobsthalIntegralCompanionKJacobsthalCatalan
