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
import Mathlib.Tactic.Zify

/-!
# No two-near perfect numbers with omitted divisors `2^i` and `p` or `p^2`

The main result is `not_two_near_perfect_two_pow_mul_prime_sq_case_two`, Proposition 2
of Aryan, Madhavani, Parikh, Slattery and Zelinsky, *On 2-Near Perfect Numbers*.
-/

namespace MetaMathlibExt

open ArithmeticFunction

@[expose] public section

/-- **No $2$-near perfect $2^k p^2$ with omitted divisors $2^i$ and $p$ or $p^2$.** Let $p$ be an
odd prime, let $k$ and $i$ be natural numbers with $i \le k$, let $m$ be $1$ or $2$, and let
$n = 2^k p^2$. Then $\sigma(n) \ne 2n + 2^i + p^m$, where $\sigma$ is the sum-of-divisors
function; that is, $n$ is not $2$-near perfect with omitted divisors $2^i$ and $p^m$.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Proposition 2
(`integers-2024-A61-prop-2`). -/
public theorem not_two_near_perfect_two_pow_mul_prime_sq_case_two {k p i m : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hi : i ≤ k) (hm : m = 1 ∨ m = 2) :
    ArithmeticFunction.sigma 1 (2 ^ k * p ^ 2) ≠ 2 * (2 ^ k * p ^ 2) + 2 ^ i + p ^ m := by
  intro hσ
  have htwo : sigma 1 (2 ^ k) + 1 = 2 * 2 ^ k := by
    rw [sigma_one_apply_prime_pow Nat.prime_two]
    simpa only [one_add_one_eq_two, mul_one, pow_succ'] using geom_sum_mul_add (1 : ℕ) (k + 1)
  have hsquare : sigma 1 (p ^ 2) = 1 + p + p ^ 2 := by
    simp [sigma_one_apply_prime_pow hp, Finset.sum_range_succ]
  rw [isMultiplicative_sigma.map_mul_of_coprime
    (Nat.coprime_pow_primes k 2 Nat.prime_two hp hp2.symm), hsquare] at hσ
  have heq : (p + 1) * (2 * 2 ^ k) = p ^ 2 + p + 1 + 2 ^ i + p ^ m := by
    nlinarith only [hσ, congrArg (fun t => t * (1 + p + p ^ 2)) htwo]
  have hpow : 2 ^ i ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hi
  have hpos : 0 < (2 : ℤ) ^ i := pow_pos (by decide) i
  have hpcast : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  zify at heq hpow
  rcases hm with rfl | rfl
  · simp only [pow_one] at heq
    have hfactor : ((p : ℤ) + 1) * (2 * 2 ^ k - p - 1) = 2 ^ i := by
      nlinarith only [heq]
    have hy : 1 ≤ (2 : ℤ) * 2 ^ k - p - 1 := by
      by_contra h
      have hmul := mul_nonpos_of_nonneg_of_nonpos
        (show 0 ≤ (p : ℤ) + 1 by omega)
        (show (2 : ℤ) * 2 ^ k - p - 1 ≤ 0 by omega)
      nlinarith only [hfactor, hpos, hmul]
    have hmul := mul_nonneg (show 0 ≤ (p : ℤ) by omega)
      (show 0 ≤ (2 : ℤ) * 2 ^ k - p - 2 by omega)
    nlinarith only [hfactor, hpow, hmul, hy, hpcast]
  · have hfactor : ((p : ℤ) + 1) * (2 * 2 ^ k - 2 * p + 1) = 2 ^ i + 2 := by
      nlinarith only [heq]
    have hy : 1 ≤ (2 : ℤ) * 2 ^ k - 2 * p + 1 := by
      by_contra h
      have hmul := mul_nonpos_of_nonneg_of_nonpos
        (show 0 ≤ (p : ℤ) + 1 by omega)
        (show (2 : ℤ) * 2 ^ k - 2 * p + 1 ≤ 0 by omega)
      nlinarith only [hfactor, hpos, hmul]
    have hy' : (2 : ℤ) * 2 ^ k - 2 * p + 1 ≤ 1 := by
      by_contra h
      have hmul := mul_nonneg (show 0 ≤ (p : ℤ) by omega)
        (show 0 ≤ (2 : ℤ) * 2 ^ k - 2 * p - 1 by omega)
      nlinarith only [hfactor, hpow, hmul, hpcast,
        show 2 ≤ (2 : ℤ) * 2 ^ k - 2 * p + 1 by omega]
    have hprime : 2 ^ k = p := by
      exact_mod_cast (show (2 : ℤ) ^ k = p by omega)
    exact hp2 (Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two
      (by rw [hprime]))

end

end MetaMathlibExt
