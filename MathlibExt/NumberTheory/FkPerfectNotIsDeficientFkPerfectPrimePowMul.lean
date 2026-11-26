/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Basic
public import MathlibExt.NumberTheory.OddPrimeDeficientPerfect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors

/-! # No deficient `F_k`-perfect number `p₁ ^ a * p₂` with distinct odd primes

Deficient `F_k`-perfect numbers and the proof that, for `k > 1`, no number of
the form `p₁ ^ a * p₂` with distinct odd primes `p₁` and `p₂` is one.

Statements from Flora Jeba S, Anirban Roy, Pankaj Jyoti
Mahanta, and Manjil P. Saikia, "On Near `F_k`-Perfect and
Deficient `F_k`-Perfect Numbers", *INTEGERS* 25 (2025),
Article A86
(<https://math.colgate.edu/~integers/z86/z86.pdf>).
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

private theorem odd_of_dvd_of_odd (e n : ℕ) (hn : Odd n) (he : e ∣ n) : Odd e := by
  by_contra hcon
  have hcon' : Even e := Nat.not_odd_iff_even.mp hcon
  have hneven : Even n := even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hcon').trans he)
  exact (Nat.not_even_iff_odd.mpr hn) hneven

private theorem card_divisors_prime_pow_mul_prime (p₁ p₂ a : ℕ) (hp₁ : p₁.Prime)
    (hp₂ : p₂.Prime) (hne : p₁ ≠ p₂) :
    (p₁ ^ a * p₂).divisors.card = (a + 1) * 2 := by
  have hcop : (p₁ ^ a).Coprime p₂ :=
    Nat.Coprime.pow_left a ((Nat.coprime_primes hp₁ hp₂).mpr hne)
  have hσ := ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
    (f := ArithmeticFunction.sigma 0) hcop
  simp only [ArithmeticFunction.sigma_zero_apply] at hσ
  have hpa : (p₁ ^ a).divisors.card = a + 1 := by
    rw [Nat.divisors_prime_pow hp₁ a, Finset.card_map, Finset.card_range]
  have hp2 : p₂.divisors.card = 2 := by
    rw [hp₂.divisors, Finset.card_insert_of_notMem (by
      simpa only [Finset.mem_singleton] using hp₂.ne_one.symm), Finset.card_singleton]
  rw [hσ, hpa, hp2]

private theorem even_sum_pow_of_forall_odd (s : Finset ℕ) (k : ℕ)
    (hodd : ∀ e ∈ s, Odd e) (hcard : Even s.card) :
    Even (∑ e ∈ s, e ^ k) := by
  rw [Nat.even_iff, Finset.sum_nat_mod]
  have h1 : ∀ e ∈ s, e ^ k % 2 = 1 := fun e he => Nat.odd_iff.mp ((hodd e he).pow)
  have hsum1 : (∑ e ∈ s, e ^ k % 2) = ∑ _e ∈ s, 1 :=
    Finset.sum_congr rfl (fun e he => h1 e he)
  obtain ⟨c, hc⟩ := hcard
  rw [hsum1, ← Finset.card_eq_sum_ones, hc]
  omega

/-- **No deficient $F_k$-perfect number $p_1^a p_2$ with distinct odd primes.** Let $k > 1$ be
a natural number, let $p_1 \ne p_2$ be odd primes and let $a$ be a natural number. Then
$p_1^a p_2$ is not deficient $F_k$-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 16. -/
theorem not_isDeficientFkPerfect_prime_pow_mul
    (k p₁ p₂ a : ℕ) (hk : 1 < k) (hp₁ : p₁.Prime)
    (hp₂ : p₂.Prime) (ho₁ : Odd p₁) (ho₂ : Odd p₂)
    (hne : p₁ ≠ p₂) :
    ¬ IsDeficientFkPerfect k (p₁ ^ a * p₂) := by
  have _ : k ≠ 0 := by omega
  rintro ⟨d, hdvd, _hlt, hsum⟩
  have hn : Odd (p₁ ^ a * p₂) := ho₁.pow.mul ho₂
  have hcard : (p₁ ^ a * p₂).divisors.card = (a + 1) * 2 :=
    card_divisors_prime_pow_mul_prime p₁ p₂ a hp₁ hp₂ hne
  have hcardeven : Even (p₁ ^ a * p₂).divisors.card := ⟨a + 1, by rw [hcard]; ring⟩
  have hσeven : Even (∑ e ∈ (p₁ ^ a * p₂).divisors, e ^ k) :=
    even_sum_pow_of_forall_odd _ k
      (fun e he => odd_of_dvd_of_odd e _ hn (Nat.dvd_of_mem_divisors he)) hcardeven
  have hdk : Odd (d ^ k) := (odd_of_dvd_of_odd d _ hn hdvd).pow
  have hnk : Odd ((p₁ ^ a * p₂) ^ k) := hn.pow
  have h3 : Odd 3 := ⟨1, rfl⟩
  have h3n : Odd (3 * (p₁ ^ a * p₂)) := h3.mul hn
  obtain ⟨s, hs⟩ := hσeven
  obtain ⟨t, ht⟩ := hdk
  obtain ⟨u, hu⟩ := hnk
  obtain ⟨v, hv⟩ := h3n
  omega

end MathlibExt.NumberTheory.FkPerfectWanted
