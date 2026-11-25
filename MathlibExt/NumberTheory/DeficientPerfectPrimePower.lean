/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.OddPrimeDeficientPerfect
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Deficient-perfect prime powers

In the deficient-perfect equation for a prime power, all nonunit divisor
powers vanish modulo `p ^ k`. The remaining terms rule out odd primes and,
by reduction modulo four, powers of two of exponent at least two.
-/

set_option autoImplicit false

public section

namespace MathlibExt.NumberTheory.FkPerfectWanted

/-- **$[k,\ell]$-deficient-perfect prime powers for $k \ge 2$.** Let $p$ be a prime and let $a$,
$k$ and $\ell$ be natural numbers with $k \ge 2$. If $p^a$ is $[k,\ell]$-deficient-perfect, then
$p = 2$ and $a = 1$.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 5. -/
theorem isKLDeficientPerfect_prime_pow_imp
    (p a k l : ℕ) (hp : p.Prime) (hk : 2 ≤ k) :
    IsKLDeficientPerfect k l (p ^ a) → p = 2 ∧ a = 1 := by
  rintro ⟨d, hd, hlt, hsum⟩
  obtain _ | a := a
  · simp only [pow_zero] at hd hlt
    exact False.elim (Nat.not_lt_of_ge (Nat.dvd_one.mp hd).ge hlt)
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp hd
  rw [Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ, Finset.sum_range_succ'] at hsum
  simp only [pow_zero, one_pow] at hsum
  have heq : (∑ i ∈ Finset.range a, (p ^ (i + 1)) ^ k) + 1 + (p ^ j) ^ k =
      l * p ^ (a + 1) := by omega
  -- Any common divisor of `p ^ k` and `p ^ (a + 1)` divides the contribution of the units.
  have hsmall (m : ℕ) (hmk : m ∣ p ^ k) (hma : m ∣ p ^ (a + 1)) : m ≤ 2 := by
    have hterm (i : ℕ) : m ∣ (p ^ (i + 1)) ^ k :=
      hmk.trans (pow_dvd_pow_of_dvd (dvd_pow_self p (Nat.succ_ne_zero i)) k)
    have htail : m ∣ ∑ i ∈ Finset.range a, (p ^ (i + 1)) ^ k :=
      Finset.dvd_sum fun i _ => hterm i
    have hall : m ∣ (∑ i ∈ Finset.range a, (p ^ (i + 1)) ^ k) + (1 + (p ^ j) ^ k) := by
      rw [← add_assoc, heq]
      exact hma.mul_left l
    have hunit : m ∣ 1 + (p ^ j) ^ k := (Nat.dvd_add_iff_right htail).mpr hall
    cases j with
    | zero =>
      rw [pow_zero, one_pow] at hunit
      exact Nat.le_of_dvd (by decide : 0 < 2) hunit
    | succ j =>
      have h : m ∣ 1 := (Nat.dvd_add_iff_left (hterm j)).mpr hunit
      exact (Nat.le_of_dvd (by decide : 0 < 1) h).trans (by decide)
  have hp2 : p = 2 := by
    have h := hsmall p (dvd_pow_self p (by omega)) (dvd_pow_self p (by omega))
    exact le_antisymm h hp.two_le
  refine ⟨hp2, ?_⟩
  by_contra ha
  have h := hsmall (p ^ 2) (pow_dvd_pow p hk) (pow_dvd_pow p (by omega))
  simp [hp2] at h

end MathlibExt.NumberTheory.FkPerfectWanted
