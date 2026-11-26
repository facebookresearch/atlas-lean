/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.PrimeCounting.AxlerMertensRemainder

/-!
# Tests for Axler's Mertens remainder bound
-/

namespace MetaMathlibExt

-- At the threshold x = x₀ = 2, the boundary prime is excluded.
example (η : ℝ) (hη : 0 < η)
    (hθ : ∀ y : ℝ, 2 ≤ y → |Chebyshev.theta y - y| < η * y / Real.log y) :
    |(∑' p : ℕ, if p.Prime ∧ p ≠ 2 then Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ) else 0) -
        ∑' m : ℕ, Real.logarithmicIntegralReal (2 ^ (-((m : ℝ) + 1))) / ((m : ℝ) + 2)| <
      η / Real.log 2 ^ 2 * (3 * Real.log 2 - 1) := by
  have htail (p : ℕ) : (p.Prime ∧ (2 : ℝ) < p) ↔ p.Prime ∧ p ≠ 2 := by
    constructor
    · rintro ⟨hp, hlt⟩
      exact ⟨hp, ne_of_gt (by exact_mod_cast hlt)⟩
    · rintro ⟨hp, hne⟩
      exact ⟨hp, by exact_mod_cast lt_of_le_of_ne hp.two_le hne.symm⟩
  have h := abs_mertensRemainder_sub_tsum_logarithmicIntegral_lt 1 one_pos η 2 hη (by norm_num)
    (by simpa using hθ) 2 le_rfl
  simp only [htail] at h
  norm_num at h ⊢
  exact h

-- Below the first prime the remainder sums over all primes, including 2.
example (k : ℕ) (hk : 0 < k) (η : ℝ) (hη : 0 < η)
    (hθ : ∀ y : ℝ, 3 / 2 ≤ y → |Chebyshev.theta y - y| < η * y / Real.log y ^ k) :
    |(∑' p : ℕ, if p.Prime then Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ) else 0) -
        ∑' m : ℕ, Real.logarithmicIntegralReal ((3 / 2) ^ (-((m : ℝ) + 1))) / ((m : ℝ) + 2)| <
      η / Real.log (3 / 2) ^ (k + 1) * (5 / 2 * Real.log 3 - 1) := by
  have htail (p : ℕ) : (p.Prime ∧ (3 / 2 : ℝ) < p) ↔ p.Prime := by
    refine ⟨And.left, fun hp ↦ ⟨hp, ?_⟩⟩
    have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    exact (by norm_num : (3 / 2 : ℝ) < 2).trans_le hp₂
  have h := abs_mertensRemainder_sub_tsum_logarithmicIntegral_lt k hk η (3 / 2) hη (by norm_num)
    hθ (3 / 2) le_rfl
  norm_num [htail] at h ⊢
  exact h

end MetaMathlibExt
