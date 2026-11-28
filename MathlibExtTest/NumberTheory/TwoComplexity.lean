/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TwoComplexity
import Mathlib.Tactic.IntervalCases

/-! # Tests for the 2-complexity of even integers -/

namespace MathlibExt.NumberTheory.TwoComplexityWanted

-- The smallest positive even number with three set bits needs exactly five copies of two.
example : complexityL 2 14 = 5 := by
  have two : CanBuild 2 1 2 := CanBuild.base
  have build : CanBuild 2 5 14 := two.add (two.mul (two.add (two.mul two)))
  refine le_antisymm (complexityL_min_le build) ?_
  have hl := logb_two_add_one_le 14 (by decide) (by decide) (by
    rintro ⟨a, b, hab, he⟩
    have hb : b < 4 := by
      by_contra! h
      have hlarge : 2 ^ 4 ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) h
      have hsmall : 2 ^ b ≤ 14 := he ▸ Nat.le_add_left _ _
      exact (by decide : ¬ (2 ^ 4 ≤ 14)) (hlarge.trans hsmall)
    interval_cases b <;> interval_cases a <;> norm_num at he)
  have hlog : (3 : ℝ) < Real.logb 2 14 := calc
    (3 : ℝ) = Real.logb 2 ((2 : ℝ) ^ 3) := by
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
      norm_num
    _ < _ := Real.logb_lt_logb (by norm_num) (by norm_num) (by norm_num)
  have h : (4 : ℝ) < complexityL 2 14 := by push_cast at hl; linarith
  exact_mod_cast h

-- The lowest allowed third exponent in the three-power form is one.
example : twoComplexityAddTwoForm 3 14 := Or.inl ⟨2, 1, by decide⟩

-- Odd inputs use the default value of the complexity.
example : complexityL 2 1 = 0 := by
  apply complexityL_eq_zero_iff.mpr
  rintro ⟨k, hk⟩
  have even_build {k n : ℕ} (h : CanBuild 2 k n) : 2 ∣ n := by
    induction h with
    | base => decide
    | add _ _ hx hy => exact dvd_add hx hy
    | mul _ _ hx _ => exact dvd_mul_of_dvd_left hx _
  exact absurd (even_build hk) (by decide)

-- Independently check the exponent conclusion on a finite grid, including m = 0 and a = b.
example : ∀ (m : Fin 5) (a b : Fin 6), a.val ≤ b.val →
    (2 : ℕ) ^ m.val < 2 ^ a.val + 2 ^ b.val →
    2 ^ a.val + 2 ^ b.val ≤ (2 : ℕ) ^ (m.val + 1) → b.val = m.val := by decide

-- A client can recover the larger exponent of any ordered representation of the endpoint.
example (a b : ℕ) (hab : a ≤ b) (h : 32 = 2 ^ a + 2 ^ b) : b = 4 :=
  largest_exponent_of_two_pow_add_two_pow 4 32 a b hab (by decide) (by decide) h

end MathlibExt.NumberTheory.TwoComplexityWanted
