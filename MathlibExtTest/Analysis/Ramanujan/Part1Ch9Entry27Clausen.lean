/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Ramanujan.Part1Ch9Entry27Clausen
import Mathlib.Tactic.NormNum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry27Clausen

open Finset

-- Even at a root of the falling product, its derivative can be nonzero.
example : chapter9FallingDerivative 2 1 = -1 := by
  have h₀ : (range 3).erase 0 = {1, 2} := by decide
  have h₁ : (range 3).erase 1 = {0, 2} := by decide
  have h₂ : (range 3).erase 2 = {0, 1} := by decide
  norm_num [chapter9FallingDerivative, Finset.sum_range_succ, h₀, h₁, h₂]

-- The first Bernoulli correction is independent of the exponent.
example (r : ℝ) : chapter9Entry27Coeff 1 r = 1 / 12 := by
  norm_num [chapter9Entry27Coeff, chapter9FallingDerivative, bernoulli_two, Nat.factorial]

-- At r = 0 the first-order approximation contains the Stirling correction 1 / (12 n).
example (C x : ℝ) : chapter9Entry27Approx 0 C 1 x = C - x + 1 / (12 * x) := by
  norm_num [chapter9Entry27Approx, chapter9Entry27Coeff, chapter9FallingDerivative,
    bernoulli_two, Nat.factorial, Real.rpow_neg_one, Real.rpow_eq_pow]
  ring

example : Summable (chapter9Entry27LogTerm 2) := by
  obtain ⟨_, _, h⟩ := ramanujan_part1_ch9_entry27_clausen 2 (by norm_num)
  exact (h (by norm_num)).2.1

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry27Clausen
