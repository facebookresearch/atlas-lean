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
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors

/-!
# Deficient-perfect prime powers

## Main statements

* `isKLDeficientPerfect_prime_pow_two_iff`: a prime power `p ^ a` is `[2,ℓ]`-deficient-perfect
  exactly when `p = 2`, `a = 1` and `ℓ = 1`. Reducing the divisor-sum equation modulo `p ^ 2`
  excludes every exponent `a ≥ 2`, and at `a = 1` the equation gives `ℓ * p = 2`. The weaker form
  that also allows `a = 2` is `isKLDeficientPerfect_prime_pow_two_imp`.
* `klDeficientPerfectWith_one_prime_pow_iff`: the prime power `p ^ a` is `[1,ℓ]`-deficient-perfect
  with divisor `d` if and only if `p = 2`, `ℓ = 1`, `d = 1` and `a ≥ 1`. This is the `k = 1` part
  of Theorem 5.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta, and Manjil P. Saikia, "On Near
`F_k`-Perfect and Deficient `F_k`-Perfect Numbers", Theorem 3, Corollary 1 and Theorem 5.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FkPerfectWanted

private theorem sum_range_two_pow_add_one (a : ℕ) :
    (∑ i ∈ Finset.range a, 2 ^ i) + 1 = 2 ^ a := by
  induction a with
  | zero => simp
  | succ a ih => rw [Finset.sum_range_succ, pow_succ]; omega

/-- **Prime powers that are $[1,\ell]$-deficient-perfect with a given divisor.** Let $p$ be a
prime, let $a$, $\ell$ and $d$ be natural numbers, and write $\sigma_1(m)$ for the sum of the
divisors of $m$. Then $d$ is a proper divisor of $p^a$ ($d \mid p^a$ and $d < p^a$) with
$\sigma_1(p^a) + d = p^a + \ell p^a$ if and only if $p = 2$, $\ell = 1$, $d = 1$ and $a \ge 1$.

This is the $k = 1$ part of Theorem 5 of the source.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 5. -/
theorem klDeficientPerfectWith_one_prime_pow_iff
    (p a l d : ℕ) (hp : p.Prime) :
    KLDeficientPerfectWith 1 l (p ^ a) d ↔
      p = 2 ∧ l = 1 ∧ d = 1 ∧ 1 ≤ a := by
  constructor
  · rintro ⟨hdvd, hlt, hsum⟩
    have ha : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with rfl | h
      · rw [pow_zero] at hdvd hlt
        exact absurd (Nat.dvd_one.mp hdvd) (Nat.ne_of_lt hlt)
      · exact h
    obtain ⟨b, _hb, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hsigma : (∑ e ∈ (p ^ a).divisors, e) = ∑ i ∈ Finset.range (a + 1), p ^ i := by
      have h := ArithmeticFunction.sigma_one_apply_prime_pow (p := p) (i := a) hp
      rwa [ArithmeticFunction.sigma_one_apply] at h
    simp only [pow_one] at hsum
    rw [hsigma] at hsum
    have htail : p ∣ ∑ i ∈ Finset.range a, p ^ (i + 1) := by
      apply Finset.dvd_sum
      intro i _
      exact dvd_pow_self p (by omega)
    have hpa0 : p ^ a ≡ 0 [MOD p] :=
      Nat.modEq_zero_iff_dvd.mpr (dvd_pow_self p (by omega))
    have hS1 : (∑ i ∈ Finset.range (a + 1), p ^ i) ≡ 1 [MOD p] := by
      rw [Finset.sum_range_succ', pow_zero]
      simpa only [zero_add] using
        (Nat.modEq_zero_iff_dvd.mpr htail).add (Nat.ModEq.refl 1)
    have hb0 : b = 0 := by
      by_contra hb
      have hpb0 : p ^ b ≡ 0 [MOD p] :=
        Nat.modEq_zero_iff_dvd.mpr (dvd_pow_self p hb)
      have hleft : (∑ i ∈ Finset.range (a + 1), p ^ i) + p ^ b ≡ 1 [MOD p] := by
        simpa only [add_zero] using hS1.add hpb0
      have hright : p ^ a + l * p ^ a ≡ 0 [MOD p] := by
        simpa only [add_zero, mul_zero] using hpa0.add (hpa0.mul_left l)
      have hcongr : p ^ a + l * p ^ a ≡ 1 [MOD p] := by
        simpa only [hsum] using hleft
      have h10 : (1 : ℕ) ≡ 0 [MOD p] := hcongr.symm.trans hright
      exact hp.not_dvd_one (Nat.modEq_zero_iff_dvd.mp h10)
    have hd1 : p ^ b = 1 := by rw [hb0, pow_zero]
    rw [hd1] at hsum
    have hleft2 : (∑ i ∈ Finset.range (a + 1), p ^ i) + 1 ≡ 2 [MOD p] := by
      simpa only [one_add_one_eq_two] using hS1.add (Nat.ModEq.refl 1)
    have hright2 : p ^ a + l * p ^ a ≡ 0 [MOD p] := by
      simpa only [add_zero, mul_zero] using hpa0.add (hpa0.mul_left l)
    have hcongr2 : p ^ a + l * p ^ a ≡ 2 [MOD p] := by
      simpa only [hsum] using hleft2
    have hpdvd2 : p ∣ 2 := Nat.modEq_zero_iff_dvd.mp (hcongr2.symm.trans hright2)
    have hp2 : p = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hpdvd2 with h | h
      · exact absurd h hp.ne_one
      · exact h
    rw [hp2] at hsum
    have hsplit : (∑ i ∈ Finset.range (a + 1), (2 : ℕ) ^ i) =
        2 ^ a + ∑ i ∈ Finset.range a, 2 ^ i := by
      rw [Finset.sum_range_succ, add_comm]
    rw [hsplit] at hsum
    have hR := sum_range_two_pow_add_one a
    have hcancel : l * 2 ^ a = 1 * 2 ^ a := by omega
    have hpow_ne : (2 : ℕ) ^ a ≠ 0 := (pow_pos (by decide) a).ne'
    have hl1 : l = 1 := mul_right_cancel₀ hpow_ne hcancel
    exact ⟨hp2, hl1, hd1, ha⟩
  · rintro ⟨rfl, rfl, rfl, ha⟩
    refine ⟨one_dvd _, ?_, ?_⟩
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ha
      rw [pow_add, pow_one]
      have hpos : (0 : ℕ) < 2 ^ k := pow_pos (by decide) k
      omega
    · have hsigma : (∑ e ∈ ((2 : ℕ) ^ a).divisors, e) =
          ∑ i ∈ Finset.range (a + 1), 2 ^ i := by
        have h := ArithmeticFunction.sigma_one_apply_prime_pow (p := 2) (i := a)
          Nat.prime_two
        rwa [ArithmeticFunction.sigma_one_apply] at h
      have hR := sum_range_two_pow_add_one a
      simp only [pow_one, one_mul]
      rw [hsigma, Finset.sum_range_succ]
      omega

private theorem geom_two_modEq (p a : ℕ) :
    (∑ i ∈ Finset.range (a + 1), p ^ (i * 2)) ≡ 1 [MOD p ^ 2] := by
  rw [Finset.sum_range_succ', Nat.zero_mul, pow_zero]
  have htail : p ^ 2 ∣ ∑ i ∈ Finset.range a, p ^ ((i + 1) * 2) := by
    apply Finset.dvd_sum
    intro i _
    exact Nat.pow_dvd_pow p (show 2 ≤ (i + 1) * 2 by omega)
  simpa only [zero_add] using
    (Nat.modEq_zero_iff_dvd.mpr htail).add (Nat.ModEq.refl 1)

private theorem range_one_add_one_sum (p : ℕ) :
    (∑ i ∈ Finset.range (1 + 1), p ^ (i * 2)) = 1 + p ^ 2 := by
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp

/-- **$[2,\ell]$-deficient-perfect prime powers (corrected).** Let $p$ be a prime and let $a$ and
$\ell$ be natural numbers. If $p^a$ is $[2,\ell]$-deficient-perfect, then $\ell = 1$, and either
$a = 2$, or $p = 2$ and $a = 1$.

The printed statement allows only the exception $a = 2$, $\ell = 1$, and so omits the solution
$p = 2$, $a = 1$, $\ell = 1$, $d = 1$ (the number $2$ of Corollary 1).

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 3. -/
theorem isKLDeficientPerfect_prime_pow_two_imp
    (p a l : ℕ) (hp : p.Prime) :
    IsKLDeficientPerfect 2 l (p ^ a) →
      l = 1 ∧ (a = 2 ∨ (p = 2 ∧ a = 1)) := by
  rintro ⟨d, hd, hlt, hsum⟩
  have hS : (∑ e ∈ (p ^ a).divisors, e ^ 2)
      = ∑ i ∈ Finset.range (a + 1), p ^ (i * 2) := by
    rw [← ArithmeticFunction.sigma_apply,
      ArithmeticFunction.sigma_apply_prime_pow hp]
  rw [hS] at hsum
  obtain ⟨b, _, rfl⟩ := (Nat.dvd_prime_pow hp).mp hd
  have hba_lt : b < a := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
  have ha1 : 1 ≤ a := by omega
  by_cases ha2 : 2 ≤ a
  · exfalso
    have hgeom : (∑ i ∈ Finset.range (a + 1), p ^ (i * 2)) ≡ 1 [MOD p ^ 2] :=
      geom_two_modEq p a
    have hpow1 : p ^ 2 ∣ (p ^ a) ^ 2 := by
      rw [← pow_mul]
      exact Nat.pow_dvd_pow p (show 2 ≤ a * 2 by omega)
    have hpow2 : p ^ 2 ∣ l * p ^ a :=
      (Nat.pow_dvd_pow p ha2).trans (dvd_mul_left _ _)
    have hmod : (∑ i ∈ Finset.range (a + 1), p ^ (i * 2)) + (p ^ b) ^ 2
        ≡ 0 [MOD p ^ 2] := by
      rw [hsum]
      simpa only [add_zero] using
        (Nat.modEq_zero_iff_dvd.mpr hpow1).add (Nat.modEq_zero_iff_dvd.mpr hpow2)
    have h1 : (1 : ℕ) + (p ^ b) ^ 2 ≡ 0 [MOD p ^ 2] :=
      (hgeom.add (Nat.ModEq.refl ((p ^ b) ^ 2))).symm.trans hmod
    have hdvd : p ^ 2 ∣ 1 + (p ^ b) ^ 2 := Nat.modEq_zero_iff_dvd.mp h1
    rw [← pow_mul] at hdvd
    have h4 : (4 : ℕ) ≤ p ^ 2 := by
      have h := Nat.pow_le_pow_left hp.two_le 2
      rwa [show (2 : ℕ) ^ 2 = 4 by decide] at h
    by_cases hb0 : b = 0
    · subst hb0
      rw [zero_mul, pow_zero] at hdvd
      have hle := Nat.le_of_dvd (by decide : 0 < 1 + 1) hdvd
      omega
    · have hpb : p ^ 2 ∣ p ^ (b * 2) :=
        Nat.pow_dvd_pow p (show 2 ≤ b * 2 by omega)
      have h1dvd : p ^ 2 ∣ 1 := by
        have hsub := Nat.dvd_sub hdvd hpb
        rwa [Nat.add_sub_cancel] at hsub
      have hle := Nat.le_of_dvd (by decide : 0 < 1) h1dvd
      omega
  · have ha1' : a = 1 := by omega
    subst ha1'
    rw [range_one_add_one_sum] at hsum
    have hb0 : b = 0 := by omega
    subst hb0
    simp only [pow_zero, pow_one, one_pow] at hsum
    have hlp : l * p = 2 := by omega
    have hdiv : p ∣ 2 := ⟨l, hlp.symm.trans (Nat.mul_comm l p)⟩
    have hp2 : p = 2 :=
      ((Nat.dvd_prime Nat.prime_two).mp hdiv).resolve_left hp.ne_one
    subst hp2
    have hl1 : l = 1 := by omega
    exact ⟨hl1, Or.inr ⟨rfl, rfl⟩⟩

/-- **$[2,\ell]$-deficient-perfect prime powers, classified.** Let $p$ be a prime and let $a$ and
$\ell$ be natural numbers. Then $p^a$ is $[2,\ell]$-deficient-perfect if and only if $p = 2$,
$a = 1$ and $\ell = 1$.

The printed statement allows the exception $a = 2$, $\ell = 1$ and omits the number $2$. The
exception does not occur, and $2$ is $[2,1]$-deficient-perfect by Corollary 1.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 3 and Corollary 1. -/
theorem isKLDeficientPerfect_prime_pow_two_iff (p a l : ℕ) (hp : p.Prime) :
    IsKLDeficientPerfect 2 l (p ^ a) ↔ p = 2 ∧ a = 1 ∧ l = 1 := by
  constructor
  · intro h
    obtain ⟨rfl, ha⟩ := isKLDeficientPerfect_prime_pow_two_imp p a l hp h
    rcases ha with rfl | ⟨rfl, rfl⟩
    · exfalso
      obtain ⟨d, -, -, hsum⟩ := h
      rw [← ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply_prime_pow hp] at hsum
      simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hsum
      ring_nf at hsum
      omega
    · exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩
    simpa using isKLDeficientPerfect_two 2

end MathlibExt.NumberTheory.FkPerfectWanted
