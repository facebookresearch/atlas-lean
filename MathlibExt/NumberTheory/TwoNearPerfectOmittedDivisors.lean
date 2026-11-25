/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Zify

/-!
# Omitted divisors of two-near perfect numbers of the form `2^k p^2`
-/

namespace MetaMathlibExt

open ArithmeticFunction

-- Divisibility and distinctness specify an omitted pair in the source statement.
set_option linter.unusedVariables false in
/-- **Sum and parity of the omitted divisors of a $2$-near perfect $2^k p^2$.** Let $p$ be an odd
prime, let $k$ be a natural number, and let $d_1 \ne d_2$ be divisors of $n = 2^k p^2$ with
$\sigma(n) = 2n + d_1 + d_2$, where $\sigma$ denotes the sum of divisors. Then
$d_1 + d_2 = -p^2 + (2^{k+1} - 1) p + (2^{k+1} - 1)$, and $d_1$ and $d_2$ have opposite parity.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Lemma 5
(`integers-2024-A61-lem-5`). -/
public theorem omitted_divisors_sum_two_pow_mul_prime_sq {k p d₁ d₂ : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hd₁ : d₁ ∣ 2 ^ k * p ^ 2) (hd₂ : d₂ ∣ 2 ^ k * p ^ 2)
    (hne : d₁ ≠ d₂)
    (hσ : ArithmeticFunction.sigma 1 (2 ^ k * p ^ 2) = 2 * (2 ^ k * p ^ 2) + d₁ + d₂) :
    ((d₁ + d₂ : ℕ) : ℤ) = -(p : ℤ) ^ 2 + (2 ^ (k + 1) - 1) * p + (2 ^ (k + 1) - 1) ∧
      d₁ % 2 ≠ d₂ % 2 := by
  have htwo : sigma 1 (2 ^ k) + 1 = 2 * 2 ^ k := by
    rw [sigma_one_apply_prime_pow Nat.prime_two]
    simpa only [one_add_one_eq_two, mul_one, pow_succ'] using geom_sum_mul_add (1 : ℕ) (k + 1)
  have hsquare : sigma 1 (p ^ 2) = 1 + p + p ^ 2 := by
    simp [sigma_one_apply_prime_pow hp, Finset.sum_range_succ]
  rw [isMultiplicative_sigma.map_mul_of_coprime
    (Nat.coprime_pow_primes k 2 Nat.prime_two hp hp2.symm), hsquare] at hσ
  constructor
  · zify at htwo hσ ⊢
    rw [pow_succ' (2 : ℤ) k]
    linear_combination (1 + (p : ℤ) + p ^ 2) * htwo - hσ
  · have hpodd := hp.odd_of_ne_two hp2
    have hodd : Odd (sigma 1 (2 ^ k)) := Nat.odd_iff.mpr (by omega)
    have hprod := hodd.mul (hpodd.one_add.add_odd (hpodd.pow (n := 2)))
    rw [hσ] at hprod
    have := Nat.odd_iff.mp hprod
    omega

end MetaMathlibExt
