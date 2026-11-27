/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.DigitSumDirichletConvolution
import Mathlib.Tactic.NormNum

/-! # Tests for Dirichlet convolutions of digit sums -/

open MetaMathlibExt

-- Each of the four ordered factor pairs of six contributes two in base two.
example : (digitSumArith 2 ^ 2) 6 = 8 := by
  rw [digitSumArith_sq_apply]
  decide

-- At the first recursive index, the alternating binomial sum is 1/20.
example : digitConvolutionCoeff 2 3 = digitConvolutionCoeff 2 2 / (40 * Real.log 2) := by
  rw [digitConvolutionCoeff_succ 2 (k := 2) le_rfl]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring
