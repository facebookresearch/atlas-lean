/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Basic
public import MathlibExt.NumberTheory.NearPerfectTwoPrimePower
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors

/-! # No near `F_k`-perfect number `p₁ ^ a * p₂ ^ b` with `a + b` odd or `a, b` both odd

For distinct odd primes `p₁`, `p₂` and exponents `a, b ≥ 1` with `a + b` odd or both odd,
`not_isNearFkPerfect_pow_mul_pow` shows `p₁ ^ a * p₂ ^ b` is not near `F_k`-perfect for
`k > 1`: multiplicativity of the divisor sum `σₖ` factors it into two geometric sums with an
even number of odd terms in total, while the near-perfect equation would force it to be odd.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 20.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FkPerfectWanted

/-- **$[k,\ell]$-near-perfect numbers.** For natural numbers $k$, $\ell$ and $n$, write
$\sigma_k(n) = \sum_{e \mid n} e^k$. The number $n$ is $[k,\ell]$-near-perfect when there is a
divisor $d$ of $n$ with $d < n$ such that $\sigma_k(n) = n^k + d^k + \ell n$. -/
def IsKLNearPerfect (k l n : ℕ) : Prop :=
  ∃ d, KLNearPerfectWith k l n d

/-- **Near $F_k$-perfect numbers.** For natural numbers $k$ and $n$, the number $n$ is near
$F_k$-perfect when it is $[k,3]$-near-perfect, that is, when some proper divisor $d$ of $n$
($d \mid n$ and $d < n$) satisfies $\sigma_k(n) = n^k + d^k + 3n$, where
$\sigma_k(n) = \sum_{e \mid n} e^k$ is the sum of the $k$-th powers of the divisors of $n$.

No condition $k > 1$ is imposed here; the results that need it assume it. -/
def IsNearFkPerfect (k n : ℕ) : Prop :=
  IsKLNearPerfect k 3 n

private theorem odd_prime_geom_sum_modEq_two (p b k : ℕ) (hpo : Odd p) :
    (∑ i ∈ Finset.range b, p ^ (i * k)) ≡ b [MOD 2] := by
  have hp1 : p ≡ 1 [MOD 2] := by
    simpa [Nat.ModEq] using Nat.odd_iff.mp hpo
  induction b with
  | zero =>
    simpa only [Finset.range_zero, Finset.sum_empty] using
      (Nat.ModEq.refl (n := 2) 0)
  | succ b ih =>
    rw [Finset.sum_range_succ]
    simpa only [one_pow, Nat.succ_eq_add_one] using ih.add (hp1.pow (b * k))

private theorem sigma_two_prime_pow (k p₁ p₂ a b : ℕ) (hp₁ : p₁.Prime)
    (hp₂ : p₂.Prime) (hne : p₁ ≠ p₂) :
    (∑ e ∈ (p₁ ^ a * p₂ ^ b).divisors, e ^ k) =
      (∑ i ∈ Finset.range (a + 1), p₁ ^ (i * k)) *
        (∑ i ∈ Finset.range (b + 1), p₂ ^ (i * k)) := by
  have hcop : Nat.Coprime (p₁ ^ a) (p₂ ^ b) :=
    (((Nat.coprime_primes hp₁ hp₂).mpr hne).pow_left a).pow_right b
  rw [← ArithmeticFunction.sigma_apply,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
    ArithmeticFunction.sigma_apply_prime_pow hp₁,
    ArithmeticFunction.sigma_apply_prime_pow hp₂]

/-- **No near $F_k$-perfect number $p_1^a p_2^b$ with $a + b$ odd or $a, b$ both odd.** Let
$k > 1$, let $p_1 \ne p_2$ be odd primes and let $a, b \ge 1$ be natural numbers such that
$a + b$ is odd or both $a$ and $b$ are odd. Then $p_1^a p_2^b$ is not near $F_k$-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 20. -/
theorem not_isNearFkPerfect_pow_mul_pow
    (k p₁ p₂ a b : ℕ) (hk : 1 < k) (hp₁ : p₁.Prime)
    (hp₂ : p₂.Prime) (ho₁ : Odd p₁) (ho₂ : Odd p₂)
    (hne : p₁ ≠ p₂) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hpar : Odd (a + b) ∨ (Odd a ∧ Odd b)) :
    ¬ IsNearFkPerfect k (p₁ ^ a * p₂ ^ b) := by
  have _nontrivial : k ≠ 0 ∧ a ≠ 0 ∧ b ≠ 0 := by omega
  rintro ⟨d, hdvd, _, hsum⟩
  have hnodd : Odd (p₁ ^ a * p₂ ^ b) := ho₁.pow.mul ho₂.pow
  have hdodd : Odd d := by
    by_contra hcon
    simp only [Nat.not_odd_iff_even] at hcon
    exact (Nat.not_even_iff_odd.mpr hnodd)
      (even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hcon).trans hdvd))
  have hodd_or : Odd a ∨ Odd b := by
    rcases hpar with h | ⟨ha', _⟩
    · by_contra hcon
      rw [not_or] at hcon
      simp only [Nat.not_odd_iff_even] at hcon
      exact (Nat.not_even_iff_odd.mpr h) (hcon.1.add hcon.2)
    · exact Or.inl ha'
  have heven_prod : Even ((a + 1) * (b + 1)) := by
    rcases hodd_or with ha' | hb'
    · exact (ha'.add_one).mul_right _
    · exact (hb'.add_one).mul_left _
  have hleft : (∑ e ∈ (p₁ ^ a * p₂ ^ b).divisors, e ^ k) ≡ 0 [MOD 2] := by
    rw [sigma_two_prime_pow k p₁ p₂ a b hp₁ hp₂ hne]
    exact ((odd_prime_geom_sum_modEq_two p₁ (a + 1) k ho₁).mul
      (odd_prime_geom_sum_modEq_two p₂ (b + 1) k ho₂)).trans
      (Nat.modEq_zero_iff_dvd.mpr (even_iff_two_dvd.mp heven_prod))
  have hevenL : Even (∑ e ∈ (p₁ ^ a * p₂ ^ b).divisors, e ^ k) := by
    rw [Nat.even_iff]
    simpa [Nat.ModEq] using hleft
  have hoddR : Odd ((p₁ ^ a * p₂ ^ b) ^ k + d ^ k + 3 * (p₁ ^ a * p₂ ^ b)) :=
    ((hnodd.pow).add_odd hdodd.pow).add_odd ((by decide : Odd 3).mul hnodd)
  rw [hsum] at hevenL
  exact (Nat.not_even_iff_odd.mpr hoddR) hevenL

end MathlibExt.NumberTheory.FkPerfectWanted
