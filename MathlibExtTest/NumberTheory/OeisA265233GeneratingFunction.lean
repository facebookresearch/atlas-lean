/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.OeisA265233GeneratingFunction
import Mathlib.Tactic.NormNum

/-! # Tests for the generating function of A265233 -/

open MathlibExt.NumberTheory.OeisA265233Wanted

-- At `x = 0` the identity reads `a₀ = (₂F₁(0) + 5) / 6`: the constant `5` accounts for
-- `a₀ = 1` while the hypergeometric series starts with `1`.
example : ∑' n : ℕ, (a265233 n : ℝ) * 0 ^ n = 1 := by
  rw [tsum_a265233_eq 0 (by norm_num) (by norm_num)]
  norm_num

-- Close to `x = 1/12` the theorem still applies, although the double series
-- `∑ c_k C(2k, j) (-4)^j x^(k + j)` no longer converges absolutely there.
example : ∑' n : ℕ, (a265233 n : ℝ) * (1 / 13) ^ n =
    (ordinaryHypergeometric (1 / 3 : ℝ) (2 / 3 : ℝ) 1
      (27 * (1 / 13) * (1 - 4 * (1 / 13)) ^ 2) + 5) / 6 :=
  tsum_a265233_eq _ (by norm_num [abs_of_pos]) (by norm_num [abs_of_pos])

-- For negative `x` the second hypothesis is the binding one: it holds at `x = -1/40` ...
example : ∑' n : ℕ, (a265233 n : ℝ) * (-1 / 40) ^ n =
    (ordinaryHypergeometric (1 / 3 : ℝ) (2 / 3 : ℝ) 1
      (27 * (-1 / 40) * (1 - 4 * (-1 / 40)) ^ 2) + 5) / 6 :=
  tsum_a265233_eq _ (by norm_num [abs_of_neg]) (by norm_num [abs_of_neg])

-- ... but fails at `x = -1/20`, where `|x| < 1/12` holds.
example : |(-1 / 20 : ℝ)| < 1 / 12 ∧ ¬ |27 * (-1 / 20 : ℝ) * (1 - 4 * (-1 / 20)) ^ 2| < 1 := by
  norm_num [abs_of_neg]
