/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.CompositionsOddParts

/-! # Tests for `MathlibExt.Combinatorics.Enumerative.CompositionsOddParts` -/

namespace MathlibExtTest.CompositionsOddParts

open MetaMathlibExt

/-- For `β = 2` the root of unity of the statement is `e^{πi} = -1`. -/
private theorem exp_div_two : Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 : ℕ) : ℂ)) = -1 := by
  rw [show 2 * (Real.pi : ℂ) * Complex.I / ((2 : ℕ) : ℂ) = Real.pi * Complex.I by push_cast; ring]
  exact Complex.exp_pi_mul_I

/-- For `β = 4` the root of unity of the statement is `e^{πi/2} = i`. -/
private theorem exp_div_four :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((4 : ℕ) : ℂ)) = Complex.I := by
  rw [show 2 * (Real.pi : ℂ) * Complex.I / ((4 : ℕ) : ℂ) = Real.pi / 2 * Complex.I by
    push_cast; ring]
  exact Complex.exp_pi_div_two_mul_I

-- `β = 2`, `α = 0`: the partial fractions `1 / (1 - u²) = (1/2) (1 / (1 - u) + 1 / (1 + u))`.
example (u : ℂ) (hu : 1 - u ^ 2 ≠ 0) :
    1 / (1 - u ^ 2) = 1 / 2 * (1 / (1 - u) + 1 / (1 + u)) := by
  have h := pow_div_one_sub_pow_eq_sum 0 2 (by norm_num) u hu
  rw [exp_div_two] at h
  simpa [Finset.sum_range_succ, sub_eq_add_neg] using h

-- `β = 2`, `α = 1`: the partial fractions `u / (1 - u²) = (1/2) (1 / (1 - u) - 1 / (1 + u))`;
-- the sign comes from `ζ ^ (-1) = -1`.
example (u : ℂ) (hu : 1 - u ^ 2 ≠ 0) :
    u / (1 - u ^ 2) = 1 / 2 * (1 / (1 - u) - 1 / (1 + u)) := by
  have h := pow_div_one_sub_pow_eq_sum 1 2 (by norm_num) u hu
  rw [exp_div_two] at h
  simpa [Finset.sum_range_succ, sub_eq_add_neg, neg_div] using h

-- `β = 4`, `α = 1`, with `ζ = i`: the four roots of unity `1, i, -1, -i` all contribute,
-- with the weights `ζ ^ (-k) = 1, -i, -1, i`.
example (u : ℂ) (hu : 1 - u ^ 4 ≠ 0) :
    u / (1 - u ^ 4) = 1 / 4 * (1 / (1 - u) - Complex.I / (1 - Complex.I * u)
      - 1 / (1 + u) + Complex.I / (1 + Complex.I * u)) := by
  have h := pow_div_one_sub_pow_eq_sum 1 4 (by norm_num) u hu
  rw [exp_div_four, pow_one] at h
  rw [h]
  simp [Finset.sum_range_succ, zpow_neg, pow_succ, sub_eq_add_neg, neg_div]

-- At `u = 0` (where `1 - u ^ β ≠ 0` holds) the identity says that the `α`-th powers of the
-- `β`-th roots of unity sum to zero when `0 < α < β`.
example (α β : ℕ) (h0 : 0 < α) (hα : α < β) :
    ∑ k ∈ Finset.range β,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (β : ℂ)) ^ (-((k : ℤ) * (α : ℤ))) = 0 := by
  have hβ : (β : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h := pow_div_one_sub_pow_eq_sum α β hα 0 (by simp [zero_pow (by omega : β ≠ 0)])
  simpa [zero_pow (by omega : α ≠ 0), zero_pow (by omega : β ≠ 0), hβ] using h.symm

end MathlibExtTest.CompositionsOddParts
