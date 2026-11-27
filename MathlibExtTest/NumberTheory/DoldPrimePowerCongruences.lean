/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DoldPrimePowerCongruences
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace MetaMathlibExt.DoldPrimePowerCongruencesTest

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

-- At n = m = 1 we compare V p with V 1; the second case has p | n and m > 1.
example (V : ℕ → ℤ)
    (h : ∀ n : ℕ, 1 ≤ n → (n : ℤ) ∣ ∑ d ∈ n.divisors, μ (n / d) * V d) :
    (V 2 ≡ V 1 [ZMOD 2]) ∧ (V 24 ≡ V 12 [ZMOD 4]) := by
  have hp := (prime_power_congruence_iff_dold (V := V)).mpr h
  exact ⟨hp (n := 1) (m := 1) (p := 2) (by decide) (by decide) Nat.prime_two,
    hp (n := 6) (m := 2) (p := 2) (by decide) (by decide) Nat.prime_two⟩

-- At n = 12 the weight at d = 2 is positive, those at d = 4 and 6 are negative,
-- and those at d = 1 and 3 vanish.
example (V : ℕ → ℤ)
    (h : ∀ n m p : ℕ, 1 ≤ n → 1 ≤ m → p.Prime →
      V (n * p ^ m) ≡ V (n * p ^ (m - 1)) [ZMOD (p : ℤ) ^ m]) :
    (12 : ℤ) ∣ V 12 - V 6 - V 4 + V 2 := by
  have h12 := (prime_power_congruence_iff_dold (V := V)).mp h (n := 12) (by decide)
  have hdiv : Nat.divisors 12 = {1, 2, 3, 4, 6, 12} := by decide
  have hμ4 : μ 4 = 0 := by
    simpa using moebius_apply_prime_pow (k := 2) Nat.prime_two (by decide)
  have hμ6 : μ 6 = 1 := by
    change μ (2 * 3) = 1
    rw [isMultiplicative_moebius.map_mul_of_coprime (show Nat.Coprime 2 3 by decide)]
    norm_num [moebius_apply_prime Nat.prime_two, moebius_apply_prime Nat.prime_three]
  have hμ12 : μ 12 = 0 := by
    change μ (4 * 3) = 0
    rw [isMultiplicative_moebius.map_mul_of_coprime (show Nat.Coprime 4 3 by decide), hμ4, zero_mul]
  norm_num [hdiv, hμ4, hμ6, hμ12, moebius_apply_prime Nat.prime_two,
    moebius_apply_prime Nat.prime_three, moebius_apply_one] at h12
  convert h12 using 1; ring

example (n : ℕ) (hn : 1 ≤ n) :
    (n : ℤ) ∣ ∑ d ∈ n.divisors, μ (n / d) * 0 :=
  (prime_power_congruence_iff_dold (V := fun _ => 0)).mp (by intros; rfl) (n := n) hn

-- The value at index zero does not matter, and negative values are allowed.
example (n : ℕ) (hn : 1 ≤ n) :
    (n : ℤ) ∣ ∑ d ∈ n.divisors, μ (n / d) * (if d = 0 then 0 else -3) := by
  refine (prime_power_congruence_iff_dold (V := fun d => if d = 0 then 0 else -3)).mp ?_ (n := n) hn
  intro d m p hd _ hp
  have hd' : d ≠ 0 := by omega
  simp [hd', hp.ne_zero]

end MetaMathlibExt.DoldPrimePowerCongruencesTest
