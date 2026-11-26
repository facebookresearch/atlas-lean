/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.NumberTheory.Divisors
public import MathlibExt.NumberTheory.NearPerfectTwoPrimePower
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-! # Prime powers that are `[k,ℓ]`-near-perfect

`klNearPerfectWith_prime_pow_iff` characterizes when a prime power is
`[k,ℓ]`-near-perfect with a given divisor, from Theorem 4 of Flora Jeba S,
Anirban Roy, Pankaj Jyoti Mahanta, and Manjil P. Saikia, "On Near `F_k`-Perfect
and Deficient `F_k`-Perfect Numbers".
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FkPerfectWanted

private theorem sigma_prime_pow_eq (p a k : ℕ) (hp : p.Prime) :
    (∑ e ∈ (p ^ a).divisors, e ^ k) = ∑ j ∈ Finset.range (a + 1), p ^ (j * k) := by
  rw [← ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply_prime_pow hp]

private theorem geom_sum_modEq_one (p m k : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) :
    ∑ i ∈ Finset.range m, p ^ (i * k) ≡ 1 [MOD p] := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [show (1 : ℕ) + m' = m' + 1 from add_comm _ _]
  rw [Finset.sum_range_succ']
  have htail : p ∣ ∑ i ∈ Finset.range m', p ^ ((i + 1) * k) := by
    apply Finset.dvd_sum
    intro i _
    exact dvd_pow_self p (mul_ne_zero (by omega) (by omega))
  have h0 : p ^ (0 * k) = 1 := by simp
  rw [h0]
  simpa only [zero_add] using
    (Nat.modEq_zero_iff_dvd.mpr htail).add (Nat.ModEq.refl 1)

/-- **Prime powers that are $[k,\ell]$-near-perfect.** Let $p$ be a prime, let $a$, $k$, $\ell$
and $d$ be natural numbers with $k \ge 1$ and $\ell \ge 1$, and write
$\sigma_k(m) = \sum_{e \mid m} e^k$. Then $d$ is a proper divisor of $p^a$ ($d \mid p^a$ and
$d < p^a$) with $\sigma_k(p^a) = (p^a)^k + d^k + \ell p^a$ if and only if $2 \le a \le k$,
$d = 1$ and $\ell = p^{k-a} \sum_{i=0}^{a-2} p^{ik}$.

The source prints the conclusion $a = k$, which is false: for $p = 2$, $a = 2$, $k = 3$,
$\ell = 2$, $d = 1$ one has $\sigma_3(4) = 73 = 4^3 + 1^3 + 2 \cdot 4$ with $a \ne k$. The
printed form is the case $a = k$ of the identity $\sum_{i=1}^{a-1} p^{ik} = \ell p^a$.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 4. -/
theorem klNearPerfectWith_prime_pow_iff
    (p a k l d : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (hl : 1 ≤ l) :
    KLNearPerfectWith k l (p ^ a) d ↔
      2 ≤ a ∧ a ≤ k ∧ d = 1 ∧
        l = p ^ (k - a) *
          ∑ i ∈ Finset.range (a - 1), p ^ (i * k) := by
  constructor
  · rintro ⟨hdvd, hlt, hsum⟩
    rw [sigma_prime_pow_eq p a k hp] at hsum
    obtain ⟨j, _, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hja' : j < a := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
    have e1 : (p ^ a) ^ k = p ^ (a * k) := by rw [← pow_mul]
    have e2 : (p ^ j) ^ k = p ^ (j * k) := by rw [← pow_mul]
    rw [Finset.sum_range_succ, e1, e2] at hsum
    have hmain : (∑ i ∈ Finset.range a, p ^ (i * k)) = p ^ (j * k) + l * p ^ a := by
      omega
    rcases eq_zero_or_pos j with rfl | hj
    · simp only [Nat.zero_mul, pow_zero] at hmain
      have ha1 : 1 ≤ a := by omega
      obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le ha1
      rw [show (1 : ℕ) + a' = a' + 1 from add_comm _ _] at hmain ⊢
      rw [Finset.sum_range_succ'] at hmain
      simp only [Nat.zero_mul, pow_zero] at hmain
      have htail : (∑ i ∈ Finset.range a', p ^ ((i + 1) * k)) = l * p ^ (a' + 1) := by
        omega
      have hfactor : (∑ i ∈ Finset.range a', p ^ ((i + 1) * k))
          = p ^ k * ∑ i ∈ Finset.range a', p ^ (i * k) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [show (i + 1) * k = k + i * k by ring, pow_add]
      rw [hfactor] at htail
      have ha2 : 2 ≤ a' + 1 := by
        rcases eq_zero_or_pos a' with rfl | h
        · simp only [Finset.range_zero, Finset.sum_empty, mul_zero, zero_add] at htail
          have hpos : 0 < l * p ^ 1 := Nat.mul_pos hl (pow_pos hp.pos 1)
          omega
        · omega
      have hak : a' + 1 ≤ k := by
        by_contra hcon
        have hle : k ≤ a' + 1 := by omega
        have hsplit : p ^ (a' + 1) = p ^ k * p ^ (a' + 1 - k) := by
          conv_lhs => rw [← Nat.add_sub_cancel' hle]
          rw [pow_add]
        rw [hsplit] at htail
        have hcancel : (∑ i ∈ Finset.range a', p ^ (i * k)) = l * p ^ (a' + 1 - k) := by
          apply mul_left_cancel₀ (pow_ne_zero k hp.ne_zero)
          rw [htail]
          ring
        have hmod1 := geom_sum_modEq_one p a' k hk (by omega : 1 ≤ a')
        rw [hcancel] at hmod1
        have hmod0 : l * p ^ (a' + 1 - k) ≡ 0 [MOD p] :=
          Nat.modEq_zero_iff_dvd.mpr ((dvd_pow_self p (by omega)).trans (dvd_mul_left _ _))
        have h10 : (1 : ℕ) ≡ 0 [MOD p] := hmod1.symm.trans hmod0
        exact hp.not_dvd_one (Nat.modEq_zero_iff_dvd.mp h10)
      have hsplit2 : p ^ k = p ^ (a' + 1) * p ^ (k - (a' + 1)) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hsplit2] at htail
      have hl_eq : l = p ^ (k - (a' + 1)) * ∑ i ∈ Finset.range a', p ^ (i * k) := by
        have h0 : p ^ (a' + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
        have h2 : l * p ^ (a' + 1)
            = (p ^ (k - (a' + 1)) * ∑ i ∈ Finset.range a', p ^ (i * k)) * p ^ (a' + 1) := by
          rw [← htail]
          ring
        exact mul_right_cancel₀ h0 h2
      refine ⟨ha2, hak, pow_zero p, ?_⟩
      rw [Nat.add_sub_cancel a' 1]
      exact hl_eq
    · have ha1 : 1 ≤ a := by omega
      have hmodL := geom_sum_modEq_one p a k hk ha1
      rw [hmain] at hmodL
      have hmod0 : p ^ (j * k) + l * p ^ a ≡ 0 [MOD p] := by
        have hd1 : p ∣ p ^ (j * k) := dvd_pow_self p (mul_ne_zero (by omega) (by omega))
        have hd2 : p ∣ l * p ^ a := (dvd_pow_self p (by omega)).trans (dvd_mul_left _ _)
        simpa only [add_zero] using
          (Nat.modEq_zero_iff_dvd.mpr hd1).add (Nat.modEq_zero_iff_dvd.mpr hd2)
      have h10 : (1 : ℕ) ≡ 0 [MOD p] := hmodL.symm.trans hmod0
      exact absurd (Nat.modEq_zero_iff_dvd.mp h10) hp.not_dvd_one
  · rintro ⟨ha2, hak, rfl, rfl⟩
    have ha1 : 1 ≤ a := by omega
    obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le ha1
    rw [show (1 : ℕ) + a' = a' + 1 from add_comm _ _]
    have hS : a' + 1 - 1 = a' := Nat.add_sub_cancel a' 1
    refine ⟨one_dvd _, ?_, ?_⟩
    · calc (1 : ℕ) < p := hp.one_lt
        _ ≤ p ^ (a' + 1) := Nat.le_self_pow (by omega) p
    · rw [hS, sigma_prime_pow_eq p (a' + 1) k hp, Finset.sum_range_succ]
      have e1 : (p ^ (a' + 1)) ^ k = p ^ ((a' + 1) * k) := by rw [← pow_mul]
      rw [e1, one_pow]
      have hmain : (∑ j ∈ Finset.range (a' + 1), p ^ (j * k))
          = 1 + (p ^ (k - (a' + 1)) * ∑ i ∈ Finset.range a', p ^ (i * k)) * p ^ (a' + 1) := by
        rw [Finset.sum_range_succ']
        simp only [Nat.zero_mul, pow_zero]
        have htail : (∑ i ∈ Finset.range a', p ^ ((i + 1) * k))
            = p ^ k * ∑ i ∈ Finset.range a', p ^ (i * k) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [show (i + 1) * k = k + i * k by ring, pow_add]
        have hL : (p ^ (k - (a' + 1)) * ∑ i ∈ Finset.range a', p ^ (i * k)) * p ^ (a' + 1)
            = p ^ k * ∑ i ∈ Finset.range a', p ^ (i * k) := by
          have hkk : p ^ (k - (a' + 1)) * p ^ (a' + 1) = p ^ k := by
            rw [← pow_add]
            congr 1
            omega
          calc (p ^ (k - (a' + 1)) * ∑ i ∈ Finset.range a', p ^ (i * k)) * p ^ (a' + 1)
              = (p ^ (k - (a' + 1)) * p ^ (a' + 1)) * ∑ i ∈ Finset.range a', p ^ (i * k) := by
                ring
            _ = p ^ k * ∑ i ∈ Finset.range a', p ^ (i * k) := by rw [hkk]
        rw [htail, hL]
        omega
      omega

end MathlibExt.NumberTheory.FkPerfectWanted
