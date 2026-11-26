/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NearPerfectTwoPrimePower
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-! # Near-perfect prime powers

For `1 ≤ ell`, a prime power is `[2,ell]`-near-perfect with a specified divisor precisely
when its exponent is two, `ell = 1`, and the divisor is one.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta, and Manjil P. Saikia,
"On Near `F_k`-Perfect and Deficient `F_k`-Perfect Numbers", *INTEGERS* 25 (2025),
Article A86 (<https://math.colgate.edu/~integers/z86/z86.pdf>), Theorem 2.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FkPerfectWanted

/-- **Prime powers that are $[2,\ell]$-near-perfect.** Let $p$ be a prime, let $a$, $\ell$ and
$d$ be natural numbers with $\ell \ge 1$, and write $\sigma_2(m)$ for the sum of the squares of
the divisors of $m$. Then $d$ is a proper divisor of $p^a$ ($d \mid p^a$ and $d < p^a$) with
$\sigma_2(p^a) = (p^a)^2 + d^2 + \ell p^a$ if and only if $a = 2$, $\ell = 1$ and $d = 1$.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 2. -/
theorem klNearPerfectWith_prime_pow_two_iff
    (p a l d : ℕ) (hp : p.Prime) (hl : 1 ≤ l) :
    KLNearPerfectWith 2 l (p ^ a) d ↔
      a = 2 ∧ l = 1 ∧ d = 1 := by
  constructor
  · rintro ⟨hd, hlt, hsum⟩
    have ha : a ≠ 0 := by
      intro ha
      subst a
      simp only [pow_zero] at hd hlt
      have hd1 : d = 1 := Nat.eq_one_of_dvd_one hd
      omega
    rw [← ArithmeticFunction.sigma_apply,
      ArithmeticFunction.sigma_apply_prime_pow hp] at hsum
    have htail : p ∣ ∑ i ∈ Finset.range a, p ^ ((i + 1) * 2) := by
      apply Finset.dvd_sum
      intro i _
      exact dvd_pow_self p (by omega)
    have hgeom : (∑ i ∈ Finset.range (a + 1), p ^ (i * 2)) ≡ 1 [MOD p] := by
      rw [Finset.sum_range_succ', Nat.zero_mul, pow_zero]
      simpa only [zero_add] using
        (Nat.modEq_zero_iff_dvd.mpr htail).add (Nat.ModEq.refl 1)
    have hpd : ¬ p ∣ d := by
      intro hpd
      have hpa : p ∣ p ^ a := dvd_pow_self p ha
      have hrhs : p ∣ (p ^ a) ^ 2 + d ^ 2 + l * p ^ a :=
        dvd_add (dvd_add (hpa.trans (dvd_pow_self (p ^ a) (by decide)))
          (hpd.trans (dvd_pow_self d (by decide)))) (dvd_mul_of_dvd_right hpa l)
      rw [hsum] at hgeom
      exact hp.not_dvd_one (Nat.modEq_zero_iff_dvd.mp
        (hgeom.symm.trans (Nat.modEq_zero_iff_dvd.mpr hrhs)))
    have hd1 : d = 1 := by
      obtain ⟨b, _, hb⟩ := (Nat.dvd_prime_pow hp).mp hd
      have hb0 : b = 0 := by
        by_contra hb0
        exact hpd (hb ▸ dvd_pow_self p hb0)
      simpa only [hb0, pow_zero] using hb
    subst d
    rw [Finset.sum_range_succ, pow_mul, one_pow] at hsum
    have hsmall : (∑ i ∈ Finset.range a, p ^ (i * 2)) = 1 + l * p ^ a := by
      omega
    have ha2 : 2 ≤ a := by
      by_contra h
      have ha1 : a = 1 := by omega
      rw [ha1, Finset.sum_range_one, Nat.zero_mul, pow_zero, pow_one] at hsmall
      have hpos : 0 < l * p := Nat.mul_pos (by omega) hp.pos
      omega
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
    rw [Finset.sum_range_succ', Finset.sum_range_succ'] at hsmall
    simp only [Nat.zero_mul, pow_zero, Nat.zero_add, Nat.one_mul] at hsmall
    have hb0 : b = 0 := by
      by_contra hb0
      have htail3 : p ^ 3 ∣ ∑ i ∈ Finset.range b, p ^ ((i + 1 + 1) * 2) := by
        apply Finset.dvd_sum
        intro i _
        exact Nat.pow_dvd_pow p (by omega)
      have hmiddle : (∑ i ∈ Finset.range b, p ^ ((i + 1 + 1) * 2)) + p ^ 2 =
          l * p ^ (b + 2) := by omega
      have hdiv : p ^ 3 ∣ p ^ 2 :=
        (Nat.dvd_add_iff_right htail3).mpr
          (hmiddle ▸ dvd_mul_of_dvd_right (Nat.pow_dvd_pow p (by omega)) l)
      have := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdiv
      omega
    subst b
    simp only [Finset.range_zero, Finset.sum_empty, zero_add] at hsmall
    have hl1 : l = 1 := Nat.mul_right_cancel (pow_pos hp.pos 2) (by omega)
    exact ⟨rfl, hl1, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩
    refine ⟨one_dvd _, Nat.one_lt_pow (by decide) hp.one_lt, ?_⟩
    rw [← ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply_prime_pow hp]
    simp [Finset.sum_range_succ, pow_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

end MathlibExt.NumberTheory.FkPerfectWanted
