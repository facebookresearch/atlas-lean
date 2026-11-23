/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedPadovanPerrinModel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # Tests for `MathlibExt.NumberTheory.GeneralizedPadovanPerrinModel` -/

namespace MathlibExtTest.GeneralizedPadovanPerrinModel

open Polynomial MetaMathlibExt

-- The Padovan–Perrin polynomial `z³ - z - 1` (`k₁ = k₂ = 1`, `s = 2`): the hypotheses hold, since
-- `(-3/2)² = 9/4 ≠ 1/3`, so its three roots are distinct.
example : (X ^ 3 - X - 1 : ℂ[X]).Separable := by
  simpa using padovanPerrin_charPoly_separable_of_p_eq_one 1 1 2 one_pos one_pos two_pos
    (by norm_num)

-- Boundary case `s = 1`: the Fibonacci polynomial `z² - z - 1`, where `-2 ≠ 1/2`.
example : (X ^ 2 - X - 1 : ℂ[X]).Separable := by
  simpa using padovanPerrin_charPoly_separable_of_p_eq_one 1 1 1 one_pos one_pos one_pos
    (by norm_num)

-- For odd `s` the hypothesis always holds: its left side is an odd power of a negative number and
-- its right side is positive.
example (k₁ k₂ s : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hs : Odd s) :
    (X ^ (s + 1) - C (k₁ : ℂ) * X - C (k₂ : ℂ)).Separable := by
  have hs₀ : 0 < s := hs.pos
  refine padovanPerrin_charPoly_separable_of_p_eq_one k₁ k₂ s hk₁ hk₂ hs₀ (ne_of_lt ?_)
  have hneg : -(k₂ : ℚ) * (s + 1) / (k₁ * s) < 0 := by
    rw [neg_mul, neg_div, neg_lt_zero]
    positivity
  calc (-(k₂ : ℚ) * (s + 1) / (k₁ * s)) ^ s < 0 := hs.pow_neg hneg
    _ < k₁ / (s + 1) := by positivity

-- The hypothesis cannot be dropped: for `k₁ = 3`, `k₂ = 2`, `s = 2` both of its sides equal `1`,
-- and `z³ - 3 z - 2 = (z + 1)² (z - 2)` is not separable (`-1` is also a root of its derivative).
example : ∃ k₁ k₂ s : ℕ, 0 < k₁ ∧ 0 < k₂ ∧ 0 < s ∧
    (-(k₂ : ℚ) * (s + 1) / (k₁ * s)) ^ s = k₁ / (s + 1) ∧
    ¬ (X ^ (s + 1) - C (k₁ : ℂ) * X - C (k₂ : ℂ)).Separable := by
  refine ⟨3, 2, 2, by norm_num, by norm_num, by norm_num, by norm_num, fun hsep => ?_⟩
  have h := aeval_ne_zero_of_isCoprime hsep (-1 : ℂ)
  norm_num at h

end MathlibExtTest.GeneralizedPadovanPerrinModel
