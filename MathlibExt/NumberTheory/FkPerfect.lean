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

/-! # `[2,ℓ]`-deficient-perfect prime powers

A prime power `p ^ a` that is `[2,ℓ]`-deficient-perfect satisfies `ℓ = 1` and either `a = 2`
or `p = 2` with `a = 1`: reducing the divisor-sum equation modulo `p ^ 2` excludes every
exponent `a ≥ 2`, and at `a = 1` the equation gives `ℓ * p = 2`.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta, and Manjil P. Saikia, "On Near
`F_k`-Perfect and Deficient `F_k`-Perfect Numbers", Theorem 3.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FkPerfectWanted

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

end MathlibExt.NumberTheory.FkPerfectWanted
