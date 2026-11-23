/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.AbundancyIndexDiv
import Mathlib.Tactic.NormNum

open MathlibExt.NumberTheory.PrimitiveNondeficientWanted

-- The bound is sharp when the prime divides exactly once, even with a nontrivial cofactor.
example : abundancyIndex 6 / abundancyIndex 3 = 1 + 1 / (2 : ℚ) := by
  unfold abundancyIndex
  decide +kernel

-- Removing one of the two factors of 2 from 12 gives the bound 1 + 1/4.
example : abundancyIndex 12 / abundancyIndex 6 ≤ 5 / 4 := by
  have h := abundancyIndex_div_le 12 2 2 (by decide) Nat.prime_two (by decide) (by decide +kernel)
  norm_num at h
  exact h
