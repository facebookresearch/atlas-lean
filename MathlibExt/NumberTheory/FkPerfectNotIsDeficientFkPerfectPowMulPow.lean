/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Basic
public import MathlibExt.NumberTheory.OddPrimeDeficientPerfect
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-! # No deficient `F_k`-perfect number `p₁ ^ a * p₂ ^ b` with `a + b` odd or `a, b` both odd

For distinct odd primes `p₁ ≠ p₂` and exponents `a, b ≥ 1` with `a + b` odd or both `a`
and `b` odd, the number `p₁ ^ a * p₂ ^ b` is not deficient `F_k`-perfect. Every divisor
is odd and the divisor count `(a + 1) * (b + 1)` is even, so the divisor-power sum is
even while the deficient-perfect equation would force it to be odd.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", *INTEGERS* 25 (2025), Article A86
(<https://math.colgate.edu/~integers/z86/z86.pdf>), Theorem 19.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FkPerfectWanted

/-- **Deficient $F_k$-perfect numbers.** For natural numbers $k$ and $n$, write
$\sigma_k(n) = \sum_{e \mid n} e^k$. The number $n$ is deficient $F_k$-perfect when it is
$[k,3]$-deficient-perfect, that is, when there is a divisor $d$ of $n$ with $d < n$ such that
$\sigma_k(n) + d^k = n^k + 3n$. -/
def IsDeficientFkPerfect (k n : ℕ) : Prop :=
  IsKLDeficientPerfect k 3 n

/-- **No deficient $F_k$-perfect number $p_1^a p_2^b$ with $a + b$ odd or $a, b$ both odd.** Let
$k > 1$ be a natural number, let $p_1 \ne p_2$ be odd primes and let $a, b \ge 1$ be natural
numbers such that $a + b$ is odd or both $a$ and $b$ are odd. Then $n = p_1^a p_2^b$ is not
deficient $F_k$-perfect: there is no divisor $d$ of $n$ with $d < n$ and
$\sigma_k(n) + d^k = n^k + 3n$, where $\sigma_k(n) = \sum_{e \mid n} e^k$.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 19. -/
theorem not_isDeficientFkPerfect_pow_mul_pow
    (k p₁ p₂ a b : ℕ) (hk : 1 < k) (hp₁ : p₁.Prime)
    (hp₂ : p₂.Prime) (ho₁ : Odd p₁) (ho₂ : Odd p₂)
    (hne : p₁ ≠ p₂) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hpar : Odd (a + b) ∨ (Odd a ∧ Odd b)) :
    ¬ IsDeficientFkPerfect k (p₁ ^ a * p₂ ^ b) := by
  -- `hk`, `ha` and `hb` are part of the stated result; the parity argument needs none of them.
  have _hk : 1 < k := hk
  have _ha : 1 ≤ a := ha
  have _hb : 1 ≤ b := hb
  rintro ⟨d, hdvd, _, hsum⟩
  have hn_odd : Odd (p₁ ^ a * p₂ ^ b) := ho₁.pow.mul ho₂.pow
  have hodd_of_dvd : ∀ e : ℕ, e ∣ p₁ ^ a * p₂ ^ b → Odd e := by
    intro e he
    by_contra hcon
    rw [Nat.not_odd_iff_even] at hcon
    exact (Nat.not_even_iff_odd.mpr hn_odd) (hcon.trans_dvd he)
  have hcop : Nat.Coprime (p₁ ^ a) (p₂ ^ b) :=
    Nat.coprime_pow_primes a b hp₁ hp₂ hne
  have hsig : ArithmeticFunction.sigma 0 (p₁ ^ a * p₂ ^ b)
      = ArithmeticFunction.sigma 0 (p₁ ^ a) * ArithmeticFunction.sigma 0 (p₂ ^ b) :=
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop
  have hcard : (p₁ ^ a * p₂ ^ b).divisors.card = (a + 1) * (b + 1) := by
    rw [ArithmeticFunction.sigma_zero_apply,
      ArithmeticFunction.sigma_zero_apply_prime_pow hp₁,
      ArithmeticFunction.sigma_zero_apply_prime_pow hp₂] at hsig
    exact hsig
  have hpar2 : Even (a + 1) ∨ Even (b + 1) := by
    rcases hpar with hodd | ⟨ha', _⟩
    · rcases Nat.even_or_odd a with hae | hao
      · have hb : Odd b := by
          rw [Nat.odd_iff]
          have hae' := Nat.even_iff.mp hae
          have hodd' := Nat.odd_iff.mp hodd
          omega
        exact Or.inr hb.add_one
      · exact Or.inl hao.add_one
    · exact Or.inl ha'.add_one
  have hcard_even : Even ((p₁ ^ a * p₂ ^ b).divisors.card) := by
    rw [hcard]
    exact hpar2.elim (fun h => h.mul_right _) (fun h => h.mul_left _)
  have hterm : ∀ e ∈ (p₁ ^ a * p₂ ^ b).divisors, e ^ k % 2 = 1 := by
    intro e he
    exact Nat.odd_iff.mp ((hodd_of_dvd e (Nat.dvd_of_mem_divisors he)).pow)
  have hsum0 : (∑ e ∈ (p₁ ^ a * p₂ ^ b).divisors, e ^ k) % 2 = 0 := by
    have hcongr : (∑ e ∈ (p₁ ^ a * p₂ ^ b).divisors, e ^ k % 2)
        = ∑ _e ∈ (p₁ ^ a * p₂ ^ b).divisors, 1 :=
      Finset.sum_congr rfl (fun e he => hterm e he)
    have h1 : (∑ e ∈ (p₁ ^ a * p₂ ^ b).divisors, e ^ k % 2)
        = (p₁ ^ a * p₂ ^ b).divisors.card := by
      rw [hcongr]
      simp
    rw [Finset.sum_nat_mod, h1]
    exact Nat.even_iff.mp hcard_even
  have hd1 : d ^ k % 2 = 1 := Nat.odd_iff.mp ((hodd_of_dvd d hdvd).pow)
  have hn1 : (p₁ ^ a * p₂ ^ b) ^ k % 2 = 1 := Nat.odd_iff.mp hn_odd.pow
  have h31 : 3 * (p₁ ^ a * p₂ ^ b) % 2 = 1 :=
    Nat.odd_iff.mp ((by decide : Odd 3).mul hn_odd)
  omega

end MathlibExt.NumberTheory.FkPerfectWanted
