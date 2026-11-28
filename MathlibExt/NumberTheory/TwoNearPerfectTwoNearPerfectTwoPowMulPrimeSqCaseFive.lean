/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.IntervalCases
import MathlibExt.NumberTheory.TwoNearPerfectTwoNearPerfectTwoPowMulPrimeSq

/-!
# 2-near perfect `2^k p^2` with omitted divisors `p^m` and `2^b p^j`

This module proves that a `2`-near perfect number of the form `2^k p^2` with `p` an odd
prime and omitted divisors `p^m` and `2^b p^j` (where `m, j ∈ {1, 2}` and `1 ≤ b ≤ k`) is
`200`. The proof is a corollary of the classification of `2`-near perfect numbers of the form
`2^k p^2` as `18`, `36` or `200`: at `18` the omitted divisors would sum to `3`, but each is a
positive multiple of the odd prime `p ≥ 3`; at `36` they would sum to `19`, which no `p` with
`p^2 ∣ 36` and `p ≥ 3` divides.

Statements from Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua
Zelinsky, *On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61 (arXiv:2310.01305).
-/

namespace MetaMathlibExt

/-- **$2$-near perfect $2^k p^2$ with omitted divisors $p^m$ and $2^b p^j$.** Let $p$ be an odd
prime, let each of $m$ and $j$ be $1$ or $2$, and let $b, k$ be integers with $1 \le b \le k$.
If $n = 2^k p^2$ satisfies $\sigma(n) = 2n + p^m + 2^b p^j$, where $\sigma$ is the
sum-of-divisors function (that is, $n$ is $2$-near perfect with omitted divisors $p^m$ and
$2^b p^j$), then $n = 200$.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Proposition 4
(`integers-2024-A61-prop-4`). -/
public theorem two_near_perfect_two_pow_mul_prime_sq_case_five {k p m b j : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : m = 1 ∨ m = 2) (hb : 1 ≤ b) (hbk : b ≤ k)
    (hj : j = 1 ∨ j = 2)
    (hσ : ArithmeticFunction.sigma 1 (2 ^ k * p ^ 2) =
      2 * (2 ^ k * p ^ 2) + p ^ m + 2 ^ b * p ^ j) :
    2 ^ k * p ^ 2 = 200 := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hm2 : m ≤ 2 := by omega
  have hj2 : j ≤ 2 := by omega
  have hd₁ : p ^ m ∣ 2 ^ k * p ^ 2 :=
    dvd_trans (pow_dvd_pow _ hm2) (dvd_mul_left _ _)
  have hd₂ : 2 ^ b * p ^ j ∣ 2 ^ k * p ^ 2 :=
    mul_dvd_mul (pow_dvd_pow _ hbk) (pow_dvd_pow _ hj2)
  have hne : p ^ m ≠ 2 ^ b * p ^ j := by
    have h1 : Odd (p ^ m) := hodd.pow
    have h2e : Even (2 ^ b) := Nat.even_pow.mpr ⟨⟨1, rfl⟩, by omega⟩
    have h2 : Even (2 ^ b * p ^ j) := h2e.mul_right _
    obtain ⟨m1, hm1⟩ := h1
    obtain ⟨m2, hm2⟩ := h2
    intro hcon
    rw [hcon] at hm1
    omega
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hm0 : m ≠ 0 := by omega
  have hj0 : j ≠ 0 := by omega
  rcases two_near_perfect_two_pow_mul_prime_sq hp hd₁ hd₂ hne hσ with h | h | h
  · exfalso
    rw [h] at hσ
    have h18 : ArithmeticFunction.sigma 1 18 = 39 := by decide
    have hpm : p ≤ p ^ m := Nat.le_self_pow hm0 p
    have hpj : p ≤ p ^ j := Nat.le_self_pow hj0 p
    have h2b : 2 ≤ 2 ^ b := Nat.le_self_pow (by omega) 2
    have h2bpj : 2 * p ≤ 2 ^ b * p ^ j := Nat.mul_le_mul h2b hpj
    omega
  · exfalso
    have h4 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hp6 : p ≤ 6 := by nlinarith [Nat.mul_le_mul_right (p ^ 2) h4]
    rw [h] at hσ
    have h36 : ArithmeticFunction.sigma 1 36 = 91 := by decide
    have h19 : p ^ m + 2 ^ b * p ^ j = 19 := by omega
    have hdvd : p ∣ 19 := by
      rw [← h19]
      exact (dvd_pow_self p hm0).add ((dvd_pow_self p hj0).mul_left _)
    interval_cases p <;> omega
  · exact h

end MetaMathlibExt
