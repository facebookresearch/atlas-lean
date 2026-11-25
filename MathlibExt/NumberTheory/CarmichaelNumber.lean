/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
public import Mathlib.RingTheory.ZMod

@[expose] public section

/-!
# Korselt's criterion

This file formalizes Korselt's criterion for Carmichael numbers.

A positive composite integer `n` is a Carmichael number if `a ^ n ≡ a [MOD n]`
for every `a : ℕ`, equivalently `∀ x : ZMod n, x ^ n = x`. By
`ZMod.natCast_zmod_val` the `ℕ`-quantified condition is equivalent to the
statement for all integers. We prove that `n` is Carmichael iff `n` is
squarefree and for every prime divisor `p ∣ n`, `p - 1 ∣ n - 1`. The proof uses
the Carmichael function `ArithmeticFunction.carmichael` as the exponent of
`(ZMod n)ˣ` to bridge the universal property and the divisibility condition.

References:

* A. Korselt, *Problème chinois*, 1899.
* T. Wright, *`(a, a)`-Carmichael numbers and greatest common divisors of `p - a`*,
  [arXiv:2607.02738v1](https://arxiv.org/abs/2607.02738v1), lines 95–103.
-/

/-- **Carmichael numbers.** A natural number $n$ is a Carmichael number if $n > 1$, $n$ is not
prime, and $a^n \equiv a \pmod{n}$ for every natural number $a$. -/
def Nat.IsCarmichaelNumber (n : ℕ) : Prop :=
  1 < n ∧ ¬n.Prime ∧ ∀ a : ℕ, a ^ n ≡ a [MOD n]

/-- **Carmichael numbers via the residue ring.** A natural number $n$ is a Carmichael number if
and only if $n > 1$, $n$ is not prime, and $x^n = x$ for every element $x$ of
$\mathbb{Z}/n\mathbb{Z}$. -/
theorem Nat.isCarmichaelNumber_iff_zmod (n : ℕ) :
    Nat.IsCarmichaelNumber n ↔
      1 < n ∧ ¬n.Prime ∧ ∀ x : ZMod n, x ^ n = x := by
  constructor
  · rintro ⟨hn, hNotPrime, hUniv⟩
    let _ : NeZero n := ⟨by omega⟩
    refine ⟨hn, hNotPrime, fun x ↦ ?_⟩
    have hCast : ((x.val ^ n : ℕ) : ZMod n) = ((x.val : ℕ) : ZMod n) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hUniv x.val)
    rw [← ZMod.natCast_zmod_val x, ← Nat.cast_pow]
    exact hCast
  · rintro ⟨hn, hNotPrime, hUniv⟩
    refine ⟨hn, hNotPrime, fun a ↦ ?_⟩
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa using hUniv (a : ZMod n)

private lemma carmichael_prime_eq (p : ℕ) (hp : p.Prime) :
    ArithmeticFunction.carmichael p = p - 1 := by
  by_cases hp2 : p = 2
  · subst hp2
    have h1 : ArithmeticFunction.carmichael (2 ^ 1) = 2 ^ (1 - 1) := by
      apply ArithmeticFunction.carmichael_two_pow_of_le_two
      decide
    simpa using h1
  · have h : ArithmeticFunction.carmichael (p ^ 1) = (p ^ 1).totient :=
      ArithmeticFunction.carmichael_pow_of_prime_ne_two 1 hp hp2
    simp only [pow_one] at h
    rw [h, Nat.totient_prime hp]

/-- **Korselt's criterion.** A natural number $n > 1$ is a Carmichael number if and only if
$n$ is squarefree, $p - 1$ divides $n - 1$ for every prime divisor $p$ of $n$, and $n$ is not
prime. -/
theorem Nat.isCarmichaelNumber_iff_korselt (n : ℕ) (hn : 1 < n) :
    Nat.IsCarmichaelNumber n ↔
      Squarefree n ∧
        (∀ p : ℕ, p.Prime → p ∣ n → (p - 1) ∣ (n - 1)) ∧ ¬n.Prime := by
  constructor
  · intro hCarmichael
    have hNotPrime : ¬n.Prime := hCarmichael.2.1
    have hUnivZMod : ∀ x : ZMod n, x ^ n = x :=
      ((Nat.isCarmichaelNumber_iff_zmod n).mp hCarmichael).2.2
    have hn0 : n ≠ 0 := by omega
    have _ : NeZero n := ⟨hn0⟩
    have hIsReduced : IsReduced (ZMod n) := by
      rw [isReduced_iff_pow_one_lt n hn]
      intro x hx
      have hPowEq : x ^ n = x := hUnivZMod x
      rw [hPowEq] at hx
      exact hx
    have hSF : Squarefree n := by
      have h := (isReduced_zmod (n := n)).mp hIsReduced
      rcases h with h | h
      · exact h
      · omega
    refine ⟨hSF, ?_, hNotPrime⟩
    have hCarmDvd : ArithmeticFunction.carmichael n ∣ (n - 1) := by
      rw [ArithmeticFunction.carmichael_eq_exponent hn0,
        Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro u
      let xu : ZMod n := (u : ZMod n)
      have hEq : xu ^ n = xu := hUnivZMod xu
      have hUN : u ^ n = u := by
        apply Units.ext
        show (↑(u ^ n) : ZMod n) = (↑u : ZMod n)
        rw [Units.val_pow_eq_pow_val]
        exact hEq
      have hn_eq : n = (n - 1) + 1 := by omega
      have hPow : u ^ ((n - 1) + 1) = u := by rw [← hn_eq]; exact hUN
      rw [pow_succ] at hPow
      have h1 : u ^ (n - 1) * u = 1 * u := by rw [hPow, one_mul]
      exact mul_right_cancel h1
    intro p hp hpn
    have h1 : ArithmeticFunction.carmichael p ∣ ArithmeticFunction.carmichael n :=
      ArithmeticFunction.carmichael_dvd hpn
    have h2 : ArithmeticFunction.carmichael p = p - 1 := carmichael_prime_eq p hp
    rw [h2] at h1
    exact dvd_trans h1 hCarmDvd
  · rintro ⟨hSF, hDiv, hNotPrime⟩
    refine ⟨hn, hNotPrime, ?_⟩
    intro a
    have hLe : a ≤ a ^ n := by
      by_cases ha0 : a = 0
      · simp [ha0]
      · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
        exact le_self_pow₀ ha1 (by omega)
    have hDvdPerPrime : ∀ p ∈ n.primeFactors, p ∣ a ^ n - a := by
      intro p hp
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hPP : p ∣ n := Nat.dvd_of_mem_primeFactors hp
      have hDivP : (p - 1) ∣ (n - 1) := hDiv p hpPrime hPP
      by_cases hDvd : p ∣ a
      · have hPowDvd : p ∣ a ^ n := dvd_pow hDvd (by omega)
        have h1 : a ^ n ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hPowDvd
        have h2 : a ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hDvd
        have h3 : a ^ n ≡ a [MOD p] := h1.trans h2.symm
        exact h3.symm.dvd'
      · have hCop : Nat.Coprime a p := (hpPrime.coprime_iff_not_dvd.mpr hDvd).symm
        have hFermat : a ^ (p - 1) ≡ 1 [MOD p] :=
          Nat.ModEq.pow_card_sub_one_eq_one hpPrime hCop
        have hPowOne : a ^ (n - 1) ≡ 1 [MOD p] := by
          obtain ⟨k, hk⟩ := hDivP
          have hn1_eq : n - 1 = (p - 1) * k := by omega
          rw [hn1_eq]
          have h1 : a ^ ((p - 1) * k) = (a ^ (p - 1)) ^ k := by rw [pow_mul]
          rw [h1]
          calc
            (a ^ (p - 1)) ^ k ≡ 1 ^ k [MOD p] := hFermat.pow k
            _ = 1 := by simp
        have hn_eq : n = (n - 1) + 1 := by omega
        have hGoal : a ^ n ≡ a [MOD p] := by
          conv_lhs => rw [hn_eq, pow_succ]
          have hMul : a ^ (n - 1) * a ≡ 1 * a [MOD p] :=
            hPowOne.mul (Nat.ModEq.refl a)
          simp only [one_mul] at hMul
          exact hMul
        exact hGoal.symm.dvd'
    let d := a ^ n - a
    have hProdDvd : n ∣ d := by
      by_cases hd0 : d = 0
      · simp [hd0]
      · have hProd : (∏ p ∈ n.primeFactors, p) ∣ d := by
          apply (Nat.prod_primeFactors_dvd_iff hd0).mpr
          intro p hp
          have hmem : p ∈ d.primeFactors :=
            Nat.mem_primeFactors.mpr
              ⟨Nat.prime_of_mem_primeFactors hp, hDvdPerPrime p hp, hd0⟩
          exact hmem
        rw [Nat.prod_primeFactors_of_squarefree hSF] at hProd
        exact hProd
    exact (Nat.modEq_of_dvd' hLe hProdDvd).symm
