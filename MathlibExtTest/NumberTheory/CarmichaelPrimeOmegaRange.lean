/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CarmichaelPrimeOmegaRange
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Simproc.Factors

/-! # Tests for Carmichael numbers with a prime number of prime factors in a range -/

namespace MathlibExtTest.CarmichaelPrimeOmegaRange

-- The predicate of the conclusion is satisfiable: `561 = 3 * 11 * 17` is a Carmichael number
-- with three prime factors.
example : (561 : ℕ).IsCarmichael ∧ (ArithmeticFunction.cardFactors 561).Prime := by
  refine ⟨Nat.isCarmichael_561, ?_⟩
  simp only [ArithmeticFunction.cardFactors_apply, Nat.primeFactorsList_ofNat]
  norm_num

-- The lower bound `e^{(γ/4) y^θ log y} ≤ n` is unbounded in `y`, so the theorem gives infinitely
-- many Carmichael numbers whose number of prime factors is prime.
example
    (hHB : ∃ C : ℝ, ∀ d : ℕ, 2 ≤ d → ∀ c : ℕ, Nat.Coprime c d →
      ∃ p : ℕ, p.Prime ∧ p ≡ c [MOD d] ∧ (p : ℝ) ≤ C * d * Real.log d ^ 2)
    (θ : ℝ) (hθ : θ ∈ Set.Ioo 1 2) (γ : ℝ) (hγ : 0 < γ)
    (hQ : ∃ Y : ℝ, ∀ y : ℝ, Y < y →
      γ * y ^ θ / Real.log (y ^ θ) ≤
        ({q : ℕ | q.Prime ∧ y ^ θ / Real.log y ≤ q ∧ (q : ℝ) ≤ y ^ θ ∧
          ∀ p : ℕ, p.Prime → p ∣ q - 1 → (p : ℝ) ≤ y}.ncard : ℝ)) :
    {n : ℕ | n.IsCarmichael ∧ (ArithmeticFunction.cardFactors n).Prime}.Infinite := by
  obtain ⟨Y, hY⟩ :=
    MetaMathlibExt.exists_carmichael_prime_cardFactors_between_of_heathBrown hHB θ hθ γ hγ hQ
  refine Set.infinite_of_not_bddAbove ?_
  rintro ⟨N, hN⟩
  set y : ℝ := max (Y + 1) (max (Real.exp 1) (4 * (N + 1) / γ)) with hy
  have hyY : Y < y := lt_of_lt_of_le (lt_add_one Y) (le_max_left _ _)
  have hye : Real.exp 1 ≤ y := (le_max_left _ _).trans (le_max_right _ _)
  have hyN : 4 * (N + 1) / γ ≤ y := (le_max_right _ _).trans (le_max_right _ _)
  have hy1 : 1 ≤ y := le_trans (Real.one_le_exp zero_le_one) hye
  have hlog : 1 ≤ Real.log y := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hye
  have hyθ : y ≤ y ^ θ := Real.self_le_rpow_of_one_le hy1 hθ.1.le
  obtain ⟨n, hn, hΩ, hlow, -⟩ := hY y hyY
  have h1 : (N : ℝ) + 1 ≤ γ / 4 * y ^ θ * Real.log y := by
    have h2 : (N : ℝ) + 1 ≤ γ / 4 * y := by
      rw [div_le_iff₀ hγ] at hyN
      linarith
    have h3 : γ / 4 * y ≤ γ / 4 * y ^ θ := by gcongr
    have h4 : γ / 4 * y ^ θ ≤ γ / 4 * y ^ θ * Real.log y :=
      le_mul_of_one_le_right (by positivity) hlog
    linarith
  have h5 : (N : ℝ) < n := by
    have := Real.add_one_le_exp (γ / 4 * y ^ θ * Real.log y)
    linarith
  exact absurd (hN ⟨hn, hΩ⟩) (by exact_mod_cast h5.not_ge)

end MathlibExtTest.CarmichaelPrimeOmegaRange
