/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Basic
public import MathlibExt.NumberTheory.NearPerfectTwoPrimePower
public import MathlibExt.NumberTheory.OddPrimeDeficientPerfect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.Ring

/-! # No prime power is deficient `F`-perfect or near `F`-perfect

For a prime `p` and `a : ℕ`, `p ^ a` is neither deficient `F`-perfect nor near
`F`-perfect. This is Theorem 1 of Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta, and
Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient `F_k`-Perfect Numbers".
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FkPerfectWanted

/-- **$[k,\ell]$-near-perfect numbers.** For natural numbers $k$, $\ell$ and $n$, write
$\sigma_k(n) = \sum_{e \mid n} e^k$. The number $n$ is $[k,\ell]$-near-perfect when there is a
divisor $d$ of $n$ with $d < n$ such that $\sigma_k(n) = n^k + d^k + \ell n$. -/
def IsKLNearPerfect (k l n : ℕ) : Prop :=
  ∃ d, KLNearPerfectWith k l n d

/-- **Deficient $F$-perfect numbers.** For a natural number $n$, write
$\sigma_2(n) = \sum_{e \mid n} e^2$. The number $n$ is deficient $F$-perfect when it is
$[2,3]$-deficient-perfect, that is, when there is a divisor $d$ of $n$ with $d < n$ such that
$\sigma_2(n) + d^2 = n^2 + 3n$. -/
def IsDeficientFPerfect (n : ℕ) : Prop :=
  IsKLDeficientPerfect 2 3 n

/-- **Near $F$-perfect numbers.** A natural number $n$ is near $F$-perfect when it is
$[2,3]$-near-perfect, that is, when some proper divisor $d$ of $n$ ($d \mid n$ and $d < n$)
satisfies $\sigma_2(n) = n^2 + d^2 + 3n$, where $\sigma_2(n) = \sum_{e \mid n} e^2$ is the sum
of the squares of the divisors of $n$. -/
def IsNearFPerfect (n : ℕ) : Prop :=
  IsKLNearPerfect 2 3 n

private theorem sigma_two_prime_pow (p a : ℕ) (hp : p.Prime) :
    (∑ e ∈ (p ^ a).divisors, e ^ 2) = ∑ i ∈ Finset.range (a + 1), p ^ (i * 2) := by
  have h := Nat.sum_divisors_prime_pow (f := fun e => e ^ 2) hp (k := a)
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  rw [← pow_mul]

private theorem sum_range_modEq_one (p a : ℕ) (ha : 1 ≤ a) :
    (∑ i ∈ Finset.range a, p ^ (i * 2)) ≡ 1 [MOD p] := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le ha
  have hshape : 1 + n = n + 1 := by omega
  rw [hshape, Finset.sum_range_succ']
  simp only [Nat.zero_mul, pow_zero]
  have htail : (∑ i ∈ Finset.range n, p ^ ((i + 1) * 2)) ≡ 0 [MOD p] := by
    rw [Nat.modEq_zero_iff_dvd]
    apply Finset.dvd_sum
    intro i _
    apply dvd_pow_self p
    omega
  have h1 : (1 : ℕ) ≡ 1 [MOD p] := Nat.ModEq.refl 1
  have h := htail.add h1
  simpa only [zero_add] using h

private theorem pow_two_mul_modEq_zero (p b : ℕ) (hb : 1 ≤ b) :
    p ^ (b * 2) ≡ 0 [MOD p] := by
  rw [Nat.modEq_zero_iff_dvd]
  apply dvd_pow_self p
  omega

private theorem three_mul_pow_modEq_zero (p a : ℕ) (ha : 1 ≤ a) :
    3 * p ^ a ≡ 0 [MOD p] := by
  rw [Nat.modEq_zero_iff_dvd]
  calc p ∣ p ^ a := dvd_pow_self p (by omega)
    _ ∣ 3 * p ^ a := dvd_mul_left _ _

private theorem growth_two (a : ℕ) (ha : 4 ≤ a) :
    3 * 2 ^ a < ∑ i ∈ Finset.range a, 2 ^ (i * 2) := by
  induction a, ha using Nat.le_induction with
  | base =>
    decide
  | succ n hn ih =>
    rw [Finset.sum_range_succ]
    have hpow : 2 ^ (n * 2) = 2 ^ n * 2 ^ n := by
      have hnn : n * 2 = n + n := by omega
      rw [hnn, pow_add]
    have h4 : 4 ≤ 2 ^ n := by
      calc (4 : ℕ) = 2 ^ 2 := by decide
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
    have h3 : 3 * 2 ^ n ≤ 2 ^ (n * 2) := by
      rw [hpow]
      calc 3 * 2 ^ n ≤ 4 * 2 ^ n := by omega
        _ = 2 ^ n * 4 := by ring
        _ ≤ 2 ^ n * 2 ^ n := by
          apply Nat.mul_le_mul_left
          exact h4
    have h2s : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    omega

private theorem not_isDeficientFPerfect_prime_pow (p a : ℕ) (hp : p.Prime) :
    ¬ IsDeficientFPerfect (p ^ a) := by
  rintro ⟨d, hdvd, hlt, hsum⟩
  rcases Nat.eq_zero_or_pos a with rfl | ha1
  · simp only [pow_zero] at hdvd hlt
    have hd1 : d = 1 := Nat.dvd_one.mp hdvd
    omega
  · obtain ⟨b, hb_le, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hba : b < a := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
    have hsig := sigma_two_prime_pow p a hp
    rw [hsig, Finset.sum_range_succ] at hsum
    have hpow_b : (p ^ b) ^ 2 = p ^ (b * 2) := by rw [← pow_mul]
    have hpow_a : (p ^ a) ^ 2 = p ^ (a * 2) := by rw [← pow_mul]
    rw [hpow_b, hpow_a] at hsum
    have hred : (∑ i ∈ Finset.range a, p ^ (i * 2)) + p ^ (b * 2) = 3 * p ^ a := by
      omega
    have hX := sum_range_modEq_one p a ha1
    have hR := three_mul_pow_modEq_zero p a ha1
    have hmod : (∑ i ∈ Finset.range a, p ^ (i * 2)) + p ^ (b * 2) ≡ 0 [MOD p] := by
      rw [hred]
      exact hR
    rcases Nat.eq_zero_or_pos b with rfl | hb1
    · simp only [Nat.zero_mul, pow_zero] at hred hmod
      have h := hX.add (Nat.ModEq.refl (1 : ℕ))
      have hpdvd2 : p ∣ 2 := by
        have h11 : p ∣ 1 + 1 := Nat.modEq_zero_iff_dvd.mp (h.symm.trans hmod)
        simpa using h11
      have hple := Nat.le_of_dvd (by decide : 0 < 2) hpdvd2
      have hp2 := hp.two_le
      have hp_eq : p = 2 := by omega
      subst hp_eq
      by_cases ha4 : 4 ≤ a
      · have hgt := growth_two a ha4
        omega
      · have ha_small : a < 4 := by omega
        have ha123 : a = 1 ∨ a = 2 ∨ a = 3 := by omega
        rcases ha123 with rfl | rfl | rfl <;> revert hred <;> decide
    · have hQ := pow_two_mul_modEq_zero p b hb1
      have h := hX.add hQ
      have hpdvd1 : p ∣ 1 := by
        have h10 : p ∣ 1 + 0 := Nat.modEq_zero_iff_dvd.mp (h.symm.trans hmod)
        simpa using h10
      have hle := Nat.le_of_dvd (by decide : 0 < 1) hpdvd1
      have hp2 := hp.two_le
      omega

private theorem not_isNearFPerfect_prime_pow (p a : ℕ) (hp : p.Prime) :
    ¬ IsNearFPerfect (p ^ a) := by
  rintro ⟨d, hdvd, hlt, hsum⟩
  rcases Nat.eq_zero_or_pos a with rfl | ha1
  · simp only [pow_zero] at hdvd hlt
    have hd1 : d = 1 := Nat.dvd_one.mp hdvd
    omega
  · obtain ⟨b, hb_le, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hba : b < a := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
    have hsig := sigma_two_prime_pow p a hp
    rw [hsig, Finset.sum_range_succ] at hsum
    have hpow_b : (p ^ b) ^ 2 = p ^ (b * 2) := by rw [← pow_mul]
    have hpow_a : (p ^ a) ^ 2 = p ^ (a * 2) := by rw [← pow_mul]
    rw [hpow_b, hpow_a] at hsum
    have hred : (∑ i ∈ Finset.range a, p ^ (i * 2)) = p ^ (b * 2) + 3 * p ^ a := by
      omega
    have hX := sum_range_modEq_one p a ha1
    have hR := three_mul_pow_modEq_zero p a ha1
    rcases Nat.eq_zero_or_pos b with rfl | hb1
    · simp only [Nat.zero_mul, pow_zero] at hred
      have h1 : (∑ i ∈ Finset.range a, p ^ (i * 2)) = 1 + 3 * p ^ a := hred
      rcases Nat.eq_zero_or_pos (a - 1) with ha10 | ha1pos
      · have ha_eq1 : a = 1 := by omega
        subst ha_eq1
        have hX1 : (∑ i ∈ Finset.range 1, p ^ (i * 2)) = 1 := by simp
        have hp2 := hp.two_le
        omega
      · have ha2 : 2 ≤ a := by omega
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le ha2
        have hsplit : (∑ i ∈ Finset.range (2 + m), p ^ (i * 2))
            = (∑ i ∈ Finset.range (1 + m), p ^ ((i + 1) * 2)) + 1 := by
          have hshape : 2 + m = (1 + m) + 1 := by omega
          rw [hshape, Finset.sum_range_succ']
          simp only [Nat.zero_mul, pow_zero]
        rw [hsplit] at h1
        have htail : (∑ i ∈ Finset.range (1 + m), p ^ ((i + 1) * 2)) = 3 * p ^ (2 + m) := by
          omega
        have hterm : ∀ i : ℕ, p ^ ((i + 1) * 2) = p ^ 2 * p ^ (i * 2) := by
          intro i
          have heq : (i + 1) * 2 = 2 + i * 2 := by ring
          rw [heq, pow_add]
        have htail_eq : (∑ i ∈ Finset.range (1 + m), p ^ ((i + 1) * 2))
            = p ^ 2 * (∑ i ∈ Finset.range (1 + m), p ^ (i * 2)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [hterm i]
        rw [htail_eq] at htail
        have hpa : p ^ (2 + m) = p ^ 2 * p ^ m := by rw [pow_add]
        rw [hpa] at htail
        have hp2ne : p ^ 2 ≠ 0 := pow_ne_zero 2 hp.ne_zero
        have h2 : (∑ i ∈ Finset.range (1 + m), p ^ (i * 2)) = 3 * p ^ m := by
          have htail2 : p ^ 2 * (∑ i ∈ Finset.range (1 + m), p ^ (i * 2))
              = p ^ 2 * (3 * p ^ m) := by
            calc p ^ 2 * (∑ i ∈ Finset.range (1 + m), p ^ (i * 2)) = 3 * (p ^ 2 * p ^ m) := htail
              _ = p ^ 2 * (3 * p ^ m) := by ring
          exact mul_left_cancel₀ hp2ne htail2
        rcases Nat.eq_zero_or_pos m with rfl | hm1
        · have hX1 : (∑ i ∈ Finset.range (1 + 0), p ^ (i * 2)) = 1 := by simp
          simp only [pow_zero, mul_one] at h2
          omega
        · have hX' := sum_range_modEq_one p (1 + m) (by omega)
          have hR' : 3 * p ^ m ≡ 0 [MOD p] := three_mul_pow_modEq_zero p m hm1
          have hmod' : (∑ i ∈ Finset.range (1 + m), p ^ (i * 2)) ≡ 0 [MOD p] := by
            rw [h2]
            exact hR'
          have hpdvd1 : p ∣ 1 := Nat.modEq_zero_iff_dvd.mp (hX'.symm.trans hmod')
          have hle := Nat.le_of_dvd (by decide : 0 < 1) hpdvd1
          have hp2 := hp.two_le
          omega
    · have hQ := pow_two_mul_modEq_zero p b hb1
      have hQR := hQ.add hR
      have hmodQR : p ^ (b * 2) + 3 * p ^ a ≡ 0 + 0 [MOD p] := hQR
      have hback : p ^ (b * 2) + 3 * p ^ a ≡ 1 [MOD p] := by
        rw [← hred]
        exact hX
      have h1eq0 : (1 : ℕ) ≡ 0 [MOD p] := by
        simpa using (hback.symm.trans hmodQR)
      have hpdvd1 : p ∣ 1 := Nat.modEq_zero_iff_dvd.mp h1eq0
      have hle := Nat.le_of_dvd (by decide : 0 < 1) hpdvd1
      have hp2 := hp.two_le
      omega

/-- **No prime power is deficient $F$-perfect or near $F$-perfect.** For every prime $p$ and
every natural number $a$, the number $n = p^a$ is neither deficient $F$-perfect nor near
$F$-perfect: there is no divisor $d$ of $n$ with $d < n$ and $\sigma_2(n) + d^2 = n^2 + 3n$, and
no divisor $d$ of $n$ with $d < n$ and $\sigma_2(n) = n^2 + d^2 + 3n$, where $\sigma_2(n)$ is the
sum of the squares of the divisors of $n$.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 1. -/
theorem prime_pow_not_fPerfect (p a : ℕ)
    (hp : p.Prime) :
    ¬ IsDeficientFPerfect (p ^ a) ∧ ¬ IsNearFPerfect (p ^ a) :=
  ⟨not_isDeficientFPerfect_prime_pow p a hp, not_isNearFPerfect_prime_pow p a hp⟩

end MathlibExt.NumberTheory.FkPerfectWanted
