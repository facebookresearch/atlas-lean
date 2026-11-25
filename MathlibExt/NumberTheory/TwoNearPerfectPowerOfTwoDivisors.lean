/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Linarith

/-!
# Two-near perfect numbers with two omitted powers of two
-/

namespace MetaMathlibExt

open ArithmeticFunction

/-- **$2$-near perfect $2^k p^2$ whose omitted divisors are powers of $2$.** Let $p$ be an odd
prime, let $k$ be a natural number and let $i \ne j$ be natural numbers with $i \le k$ and
$j \le k$. If $n = 2^k p^2$ satisfies $\sigma(n) = 2n + 2^i + 2^j$, where $\sigma$ is the
sum-of-divisors function (that is, $n$ is $2$-near perfect with omitted divisors $2^i$ and
$2^j$), then $n = 18$ and either $i = 0, j = 1$ or $i = 1, j = 0$, so the omitted divisors are
$1$ and $2$.

See Aryan, Madhavani, Parikh, Slattery and Zelinsky, *On 2-Near Perfect Numbers*,
Proposition 8 of [arXiv:2310.01305](https://arxiv.org/abs/2310.01305).

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Proposition 1
(`integers-2024-A61-prop-1`). -/
public theorem two_near_perfect_two_pow_mul_prime_sq_case_one {k p i j : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hi : i ≤ k) (hj : j ≤ k) (hij : i ≠ j)
    (hσ : ArithmeticFunction.sigma 1 (2 ^ k * p ^ 2) = 2 * (2 ^ k * p ^ 2) + 2 ^ i + 2 ^ j) :
    2 ^ k * p ^ 2 = 18 ∧ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) := by
  have htwo : sigma 1 (2 ^ k) + 1 = 2 * 2 ^ k := by
    rw [sigma_one_apply_prime_pow Nat.prime_two]
    simpa only [one_add_one_eq_two, mul_one, pow_succ'] using geom_sum_mul_add (1 : ℕ) (k + 1)
  have hsquare : sigma 1 (p ^ 2) = 1 + p + p ^ 2 := by
    simp [sigma_one_apply_prime_pow hp, Finset.sum_range_succ]
  rw [isMultiplicative_sigma.map_mul_of_coprime
    (Nat.coprime_pow_primes k 2 Nat.prime_two hp hp2.symm), hsquare] at hσ
  -- Collect the terms involving the prime without subtracting in ℕ.
  have heq : (p + 1) * (2 * 2 ^ k) = (p + 1) * p + 2 ^ i + 2 ^ j + 1 := by
    nlinarith only [hσ, congrArg (fun t => t * (1 + p + p ^ 2)) htwo]
  have hpowi : 2 ^ i ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hi
  have hpowj : 2 ^ j ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hj
  -- The two omitted divisors sum to at most 2 * 2 ^ k, forcing p + 1 = 2 * 2 ^ k.
  have hprime : 2 * 2 ^ k = p + 1 := by
    rcases lt_trichotomy (2 * 2 ^ k) (p + 1) with h | h | h
    · have hle : 2 * 2 ^ k ≤ p := by omega
      have hmul := Nat.mul_le_mul_left (p + 1) hle
      rw [heq] at hmul
      lia
    · exact h
    · nlinarith only [heq, hpowi, hpowj, hp.two_le, Nat.mul_le_mul_left p h]
  have hsum : 2 ^ i + 2 ^ j + 1 = 2 * 2 ^ k := by
    rw [hprime] at heq ⊢
    nlinarith only [heq]
  -- Their sum is odd, so one omitted divisor is 1 and the other is at most 2 ^ k.
  have hk : k ≤ 1 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    cases i <;> cases j <;> simp only [pow_zero, pow_succ] at hpowi hpowj hsum ⊢ <;> omega
  obtain rfl : k = 1 := by omega
  obtain rfl : p = 3 := by omega
  exact ⟨by decide, by omega⟩

end MetaMathlibExt
