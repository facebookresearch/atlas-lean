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
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors

/-! # Twice an odd prime is not `[k,ℓ]`-near-perfect

This module holds `IsKLNearPerfect` and the proof that twice an odd prime is never
`[k,ℓ]`-near-perfect: the divisor sum of `2 * p` factors as `(1 + 2 ^ k) * (1 + p ^ k)`,
and for each proper divisor `1`, `2`, `p` the equation fails by parity or by divisibility
by `p`.

Statements from Flora Jeba S, Anirban Roy, Pankaj Jyoti
Mahanta, and Manjil P. Saikia, "On Near `F_k`-Perfect and
Deficient `F_k`-Perfect Numbers", *INTEGERS* 25 (2025),
Article A86
(<https://math.colgate.edu/~integers/z86/z86.pdf>).
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FkPerfectWanted

/-- **$[k,\ell]$-near-perfect numbers.** For natural numbers $k$, $\ell$ and $n$, write
$\sigma_k(n) = \sum_{e \mid n} e^k$. The number $n$ is $[k,\ell]$-near-perfect when there is a
divisor $d$ of $n$ with $d < n$ such that $\sigma_k(n) = n^k + d^k + \ell n$. -/
def IsKLNearPerfect (k l n : ℕ) : Prop :=
  ∃ d, KLNearPerfectWith k l n d

/-- **Twice an odd prime is not $[k,\ell]$-near-perfect.** Let $k$ and $\ell$ be natural numbers
with $\ell \ge 1$ and let $p$ be an odd prime. Then $2p$ is not $[k,\ell]$-near-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 6. -/
theorem not_isKLNearPerfect_two_mul_prime (k l p : ℕ)
    (hl : 1 ≤ l) (hp : p.Prime) (hpo : Odd p) :
    ¬ IsKLNearPerfect k l (2 * p) := by
  rintro ⟨d, hd, hlt, hsum⟩
  have hcop : Nat.Coprime 2 p := Nat.coprime_two_left.mpr hpo
  have htwo : ArithmeticFunction.sigma k 2 = 1 + 2 ^ k := by
    simp [ArithmeticFunction.sigma_apply, Nat.prime_two.divisors]
  have h1 : (1 : ℕ) ∉ ({p} : Finset ℕ) := by
    simpa only [Finset.mem_singleton] using hp.ne_one.symm
  have hpsig : ArithmeticFunction.sigma k p = 1 + p ^ k := by
    simp [ArithmeticFunction.sigma_apply, hp.divisors, Finset.sum_insert h1]
  have hsigma : (∑ e ∈ (2 * p).divisors, e ^ k) = (1 + 2 ^ k) * (1 + p ^ k) := by
    rw [← ArithmeticFunction.sigma_apply,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, htwo, hpsig]
  rw [hsigma] at hsum
  have hprod : (1 + 2 ^ k) * (1 + p ^ k) = 1 + 2 ^ k + p ^ k + (2 * p) ^ k := by
    rw [mul_pow]; ring
  rw [hprod] at hsum
  have hmain : 1 + 2 ^ k + p ^ k = d ^ k + l * (2 * p) := by
    have h2 : (2 * p) ^ k + d ^ k + l * (2 * p)
        = d ^ k + l * (2 * p) + (2 * p) ^ k := by ac_rfl
    rw [h2] at hsum
    exact Nat.add_right_cancel hsum
  have hdiv : d = 1 ∨ d = 2 ∨ d = p := by
    by_cases hpd : p ∣ d
    · obtain ⟨f, rfl⟩ := hpd
      rw [mul_comm 2 p] at hd
      have hd2 : f ∣ 2 := Nat.dvd_of_mul_dvd_mul_left hp.pos hd
      rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with rfl | rfl
      · exact Or.inr (Or.inr (mul_one p))
      · exfalso
        rw [mul_comm p 2] at hlt
        exact lt_irrefl _ hlt
    · have hcop' : Nat.Coprime d p := (hp.coprime_iff_not_dvd.mpr hpd).symm
      have hd2 : d ∣ 2 := hcop'.dvd_of_dvd_mul_right hd
      rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simp only [pow_zero] at hmain
    have hcon : l * (2 * p) = 2 := by omega
    have h := Nat.mul_le_mul_right (2 * p) hl
    rw [one_mul, hcon] at h
    have h2 := hp.two_le
    omega
  · have h2keven : Even (2 ^ k) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
    have heven : Even (l * (2 * p)) := ⟨l * p, by ring⟩
    rcases hdiv with rfl | rfl | hdp
    · simp only [one_pow] at hmain
      have hodd : Odd (p ^ k) := hpo.pow
      have hLHS : Even (1 + 2 ^ k + p ^ k) := (odd_one.add_even h2keven).add_odd hodd
      have hRHS : Odd (1 + l * (2 * p)) := odd_one.add_even heven
      rw [hmain] at hLHS
      exact (Nat.not_odd_iff_even.mpr hLHS) hRHS
    · have h1pk : 1 + p ^ k = l * (2 * p) := by omega
      have hpd1 : p ∣ 1 := by
        have h1 : p ∣ p ^ k := dvd_pow_self p (by omega)
        have h2 : p ∣ l * (2 * p) := ⟨2 * l, by ring⟩
        rw [← h1pk] at h2
        exact (Nat.dvd_add_left h1).mp h2
      exact hp.not_dvd_one hpd1
    · rw [hdp] at hmain
      have h12k : 1 + 2 ^ k = l * (2 * p) := by omega
      have hLHS : Odd (1 + 2 ^ k) := odd_one.add_even h2keven
      rw [h12k] at hLHS
      exact (Nat.not_even_iff_odd.mpr hLHS) heven

end MathlibExt.NumberTheory.FkPerfectWanted
