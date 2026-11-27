/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.AxlerEffectivePrimeEstimates
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Tests for Axler's prime-counting bounds
-/

namespace MetaMathlibExt

-- At order three the convolution uses three different earlier coefficients.
example (x₀ : ℝ) (hx₀ : 0 < x₀)
    (hpos : ∀ x : ℝ, x₀ ≤ x → 0 < 2 * Real.log x - 4 - 4 / Real.log x - 4 / Real.log x ^ 2)
    (hlow : ∀ x : ℝ, x₀ ≤ x →
      x / (2 * Real.log x - 4 - 4 / Real.log x - 4 / Real.log x ^ 2) <
        (Nat.primeCounting ⌊x⌋₊ : ℝ))
    (x : ℝ) (hx : x₀ ≤ x) :
    x / (2 * Real.log x) + x / Real.log x ^ 2 + 3 * x / Real.log x ^ 3 + 9 * x / Real.log x ^ 4 <
      (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  let a (i : ℕ) : ℝ := if i = 0 then 2 else -4
  let b (k : ℕ) : ℝ := if k = 0 then 1 / 2 else 3 ^ (k - 1)
  have h₃ : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hden (y : ℝ) :
      a 0 * Real.log y + ∑ i ∈ Finset.Icc 1 3, a i / Real.log y ^ (i - 1) =
        2 * Real.log y - 4 - 4 / Real.log y - 4 / Real.log y ^ 2 := by
    rw [h₃]
    norm_num [a]
    ring
  have h := series_lt_primeCounting_of_lt_primeCounting 3 (by decide) a b (by norm_num [a])
    (by intro i hi; rw [h₃] at hi; fin_cases hi <;> norm_num [a]) x₀ hx₀
    (fun y hy ↦ hden y ▸ hpos y hy) (fun y hy ↦ hden y ▸ hlow y hy) (by norm_num [a, b])
    (by
      intro k hk
      rw [h₃] at hk
      fin_cases hk <;>
        norm_num [a, b, h₃, show Finset.Icc 1 2 = {1, 2} by decide]) x hx
  convert h using 1
  norm_num [b, Finset.sum_range_succ]
  ring

-- Start below the first prime and end at the jump at 2.
example (η : ℝ) (hη : 0 < η)
    (hθ : ∀ y : ℝ, 3 / 2 ≤ y → |Chebyshev.theta y - y| < η * y / Real.log y) :
    let J (e : ℝ) := 2 / Real.log 2 + e * 2 / Real.log 2 ^ 2 +
      ∫ t in (3 / 2 : ℝ)..2, (1 / Real.log t ^ 2 + e / Real.log t ^ 3)
    J (-η) ≤ 1 ∧ 1 ≤ J η := by
  have h := primeCounting_mem_Icc_auxJ 1 (by decide) η (3 / 2) hη (by norm_num)
    (by simpa using hθ) 2 (by norm_num)
  have hfirst : Nat.primeCounting 2 = 1 := by decide
  have hfloor : ⌊(3 / 2 : ℝ)⌋₊ = 1 := (Nat.floor_eq_iff' one_ne_zero).2 (by norm_num)
  simpa [hfloor, hfirst, Chebyshev.theta_eq_zero_of_lt_two (by norm_num : (3 / 2 : ℝ) < 2)] using h

-- The last branch of the error factor is antitone on `[e⁶⁷³, ∞)`.
example : AntitoneOn (fun y : ℝ ↦ Real.log y ^ 6 *
    (121.0961 * (Real.log y / 5.5666305) ^ (3 / 2 : ℝ) *
      Real.exp (-2 * Real.sqrt (Real.log y / 5.5666305)))) (Set.Ici (Real.exp 673)) :=
  fun x₁ hx₁ x _ hx ↦ axlerThetaErrorFactor_tail_antitone x₁ x hx₁ hx

-- Start at the endpoint `e⁶⁷³`; at powers of `e` the factor is a function of the exponent.
example :
    (700 : ℝ) ^ 6 * (121.0961 * (700 / 5.5666305) ^ (3 / 2 : ℝ) *
        Real.exp (-2 * Real.sqrt (700 / 5.5666305))) ≤
      673 ^ 6 * (121.0961 * (673 / 5.5666305) ^ (3 / 2 : ℝ) *
        Real.exp (-2 * Real.sqrt (673 / 5.5666305))) := by
  simpa using axlerThetaErrorFactor_tail_antitone (Real.exp 673) (Real.exp 700) le_rfl
    (Real.exp_le_exp.mpr (by norm_num))

-- For squares and `k = 1` the tail is compared with `li(1 / x)` up to `3 η / (x log² x)`.
example (η x₀ : ℝ) (hη : 0 < η) (hx₀ : 1 < x₀)
    (hθ : ∀ y : ℝ, x₀ ≤ y → |Chebyshev.theta y - y| < η * y / Real.log y)
    (x : ℝ) (hx : x₀ ≤ x) :
    |Real.logarithmicIntegralReal x⁻¹ +
        ∑' p : ℕ, if p.Prime ∧ x < p then 1 / (p : ℝ) ^ 2 else 0| <
      3 * η / (x * Real.log x ^ 2) := by
  have h := abs_logarithmicIntegral_add_tsum_inv_prime_pow_lt 1 one_pos η x₀ hη hx₀
    (by simpa using hθ) 2 le_rfl x hx
  have hexp : x ^ ((1 : ℝ) - (2 : ℕ)) = x⁻¹ := by norm_num [Real.rpow_neg_one]
  have hbound : η / (x ^ (2 - 1) * Real.log x ^ (1 + 1)) * (1 + (2 : ℕ) / ((2 : ℕ) - 1 : ℝ)) =
      3 * η / (x * Real.log x ^ 2) := by
    norm_num
    ring
  rwa [hexp, hbound] at h

-- For cubes the factor `1 + n / (n - 1)` is `5 / 2` and the power `x ^ (n - 1)` is `x²`.
example (k : ℕ) (hk : 0 < k) (η x₀ : ℝ) (hη : 0 < η) (hx₀ : 1 < x₀)
    (hθ : ∀ y : ℝ, x₀ ≤ y → |Chebyshev.theta y - y| < η * y / Real.log y ^ k)
    (x : ℝ) (hx : x₀ ≤ x) :
    |Real.logarithmicIntegralReal (x ^ (-2 : ℝ)) +
        ∑' p : ℕ, if p.Prime ∧ x < p then 1 / (p : ℝ) ^ 3 else 0| <
      5 * η / (2 * x ^ 2 * Real.log x ^ (k + 1)) := by
  have h := abs_logarithmicIntegral_add_tsum_inv_prime_pow_lt k hk η x₀ hη hx₀ hθ 3
    (by norm_num) x hx
  have hexp : x ^ ((1 : ℝ) - (3 : ℕ)) = x ^ (-2 : ℝ) := by norm_num
  have hbound : η / (x ^ (3 - 1) * Real.log x ^ (k + 1)) * (1 + (3 : ℕ) / ((3 : ℕ) - 1 : ℝ)) =
      5 * η / (2 * x ^ 2 * Real.log x ^ (k + 1)) := by
    norm_num
    ring
  rwa [hexp, hbound] at h

end MetaMathlibExt
