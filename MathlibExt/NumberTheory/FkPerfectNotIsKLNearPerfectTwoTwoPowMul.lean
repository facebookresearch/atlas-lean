/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Basic
public import MathlibExt.NumberTheory.NearPerfectTwoPrimePower
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Ring
public import MathlibExt.NumberTheory.FkPerfect

/-! # No `[2,ℓ]`-near-perfect number of the form `2 ^ a * p`

This module proves that `2 ^ a * p` is not `[2,ℓ]`-near-perfect (`IsKLNearPerfect`, defined in
`MathlibExt.NumberTheory.FkPerfect`) when `ℓ ≥ 1` and `p` is an odd prime. At `a = 0` the
only proper divisor is `1`, at `a = 1` parity forces the divisor `2` and `p` divides `1`, and
at `a ≥ 2` the divisor sum is `2` modulo `4` while every term of `n ^ 2 + d ^ 2 + ℓ * n` is
`0` modulo `4`.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", *INTEGERS* 25 (2025), Article A86
(<https://math.colgate.edu/~integers/z86/z86.pdf>), Theorem 10.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FkPerfectWanted

/-- **No $[2,\ell]$-near-perfect number of the form $2^a p$.** Let $\ell$ and $a$ be natural
numbers with $\ell \ge 1$, and let $p$ be an odd prime. Then $2^a p$ is not
$[2,\ell]$-near-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 10. -/
theorem not_isKLNearPerfect_two_two_pow_mul
    (l p a : ℕ) (hl : 1 ≤ l) (hp : p.Prime) (hpo : Odd p) :
    ¬ IsKLNearPerfect 2 l (2 ^ a * p) := by
  rintro ⟨d, hdvd, hlt, hsum⟩
  have hcop : Nat.Coprime 2 p := Nat.coprime_two_left.mpr hpo
  have hcopA : Nat.Coprime (2 ^ a) p := hcop.pow_left a
  have hsigp : ArithmeticFunction.sigma 2 p = 1 + p ^ 2 := by
    rw [ArithmeticFunction.sigma_apply, hp.divisors]
    have h1 : (1 : ℕ) ∉ ({p} : Finset ℕ) := by
      simpa only [Finset.mem_singleton] using hp.ne_one.symm
    rw [Finset.sum_insert h1, Finset.sum_singleton, one_pow]
  have hsig : (∑ e ∈ (2 ^ a * p).divisors, e ^ 2) =
      (∑ i ∈ Finset.range (a + 1), 2 ^ (i * 2)) * (1 + p ^ 2) := by
    rw [← ArithmeticFunction.sigma_apply,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopA,
      ArithmeticFunction.sigma_apply_prime_pow Nat.prime_two, hsigp]
  rw [hsig] at hsum
  have hodd2 : Odd (p ^ 2) := hpo.pow
  have heven1p2 : Even (1 + p ^ 2) := odd_one.add_odd hodd2
  have ha3 : a = 0 ∨ a = 1 ∨ 2 ≤ a := by omega
  rcases ha3 with rfl | rfl | ha2
  · simp only [pow_zero, one_mul] at hdvd hlt
    simp only [zero_add, Finset.sum_range_one, Nat.zero_mul, pow_zero, one_mul] at hsum
    have hd1 : d = 1 := by
      rcases (Nat.dvd_prime hp).mp hdvd with rfl | hcon
      · rfl
      · omega
    rw [hd1, one_pow] at hsum
    have hlp : 0 < l * p := Nat.mul_pos hl hp.pos
    omega
  · have hS : (∑ i ∈ Finset.range (1 + 1), 2 ^ (i * 2)) = 5 := by decide
    rw [hS] at hsum
    simp only [pow_one] at hdvd hlt hsum
    have h2n : (2 : ℕ) ∣ 2 * p := dvd_mul_right 2 p
    have eN : Even ((2 * p) ^ 2) :=
      even_iff_two_dvd.mpr (h2n.trans (dvd_pow_self (2 * p) (by decide : 2 ≠ 0)))
    have eLN : Even (l * (2 * p)) := even_iff_two_dvd.mpr (h2n.trans (dvd_mul_left _ _))
    have hevenL : Even (5 * (1 + p ^ 2)) :=
      even_iff_two_dvd.mpr (dvd_mul_of_dvd_right (even_iff_two_dvd.mp heven1p2) 5)
    have hevenR : Even ((2 * p) ^ 2 + d ^ 2 + l * (2 * p)) := by
      rw [← hsum]
      exact hevenL
    have ed2 : Even (d ^ 2) := by
      have hR := even_iff_two_dvd.mp hevenR
      have hX := even_iff_two_dvd.mp eN
      have hY := even_iff_two_dvd.mp eLN
      have h : 2 ∣ d ^ 2 := by omega
      exact even_iff_two_dvd.mpr h
    have hed : Even d := (Nat.even_pow.mp ed2).1
    have h2d : 2 ∣ d := even_iff_two_dvd.mp hed
    obtain ⟨e, he⟩ := h2d
    have h2edvd : 2 * e ∣ 2 * p := by
      rw [← he]
      exact hdvd
    have hep : e ∣ p :=
      (Nat.mul_dvd_mul_iff_left (show (0 : ℕ) < 2 by decide)).mp h2edvd
    have hd2 : d = 2 := by
      rcases (Nat.dvd_prime hp).mp hep with rfl | rfl
      · omega
      · omega
    rw [hd2] at hsum
    have h1 : (2 * p) ^ 2 = 4 * p ^ 2 := by ring
    have h22 : (2 : ℕ) ^ 2 = 4 := by decide
    have h3 : l * (2 * p) = p * (2 * l) := by ring
    rw [h1, h22, h3] at hsum
    have key : p ^ 2 + 1 = p * (2 * l) := by omega
    have hcontra : p ∣ 1 := by
      have hsub := Nat.dvd_sub ⟨2 * l, key⟩ (dvd_pow_self p (by decide : 2 ≠ 0))
      rwa [Nat.add_sub_cancel_left] at hsub
    exact hp.not_dvd_one hcontra
  · have ha0 : a ≠ 0 := by omega
    have h2n : (2 : ℕ) ∣ 2 ^ a * p := dvd_mul_of_dvd_left (dvd_pow_self 2 ha0) p
    have h4n : (4 : ℕ) ∣ 2 ^ a * p := by
      have h : (2 : ℕ) ^ 2 ∣ 2 ^ a := Nat.pow_dvd_pow 2 ha2
      have h44 : (2 : ℕ) ^ 2 = 4 := by decide
      rw [h44] at h
      exact dvd_mul_of_dvd_left h p
    have hevenL : Even ((∑ i ∈ Finset.range (a + 1), 2 ^ (i * 2)) * (1 + p ^ 2)) :=
      even_iff_two_dvd.mpr (dvd_mul_of_dvd_right (even_iff_two_dvd.mp heven1p2) _)
    have hevenR : Even ((2 ^ a * p) ^ 2 + d ^ 2 + l * (2 ^ a * p)) := by
      rw [← hsum]
      exact hevenL
    have eN : Even ((2 ^ a * p) ^ 2) :=
      even_iff_two_dvd.mpr (h2n.trans (dvd_pow_self (2 ^ a * p) (by decide : 2 ≠ 0)))
    have eLN : Even (l * (2 ^ a * p)) := even_iff_two_dvd.mpr (h2n.trans (dvd_mul_left _ _))
    have ed2 : Even (d ^ 2) := by
      have hR := even_iff_two_dvd.mp hevenR
      have hX := even_iff_two_dvd.mp eN
      have hY := even_iff_two_dvd.mp eLN
      have h : 2 ∣ d ^ 2 := by omega
      exact even_iff_two_dvd.mpr h
    have hed : Even d := (Nat.even_pow.mp ed2).1
    have h4d2 : (4 : ℕ) ∣ d ^ 2 := by
      have h2d := even_iff_two_dvd.mp hed
      have h := pow_dvd_pow_of_dvd h2d 2
      have h44 : (2 : ℕ) ^ 2 = 4 := by decide
      rw [h44] at h
      exact h
    have htail : (4 : ℕ) ∣ ∑ i ∈ Finset.range a, 2 ^ ((i + 1) * 2) := by
      apply Finset.dvd_sum
      intro i _
      have h : (2 : ℕ) ^ 2 ∣ 2 ^ ((i + 1) * 2) := Nat.pow_dvd_pow 2 (by omega)
      have h44 : (2 : ℕ) ^ 2 = 4 := by decide
      rw [h44] at h
      exact h
    have hS1 : (∑ i ∈ Finset.range (a + 1), 2 ^ (i * 2)) ≡ 1 [MOD 4] := by
      rw [Finset.sum_range_succ', Nat.zero_mul, pow_zero]
      simpa only [zero_add] using (Nat.modEq_zero_iff_dvd.mpr htail).add (Nat.ModEq.refl 1)
    have hp1 : p ^ 2 ≡ 1 [MOD 4] := by
      obtain ⟨k, hk⟩ := hpo
      rw [hk]
      have e : (2 * k + 1) ^ 2 = 4 * (k * k) + 4 * k + 1 := by ring
      rw [e]
      change (4 * (k * k) + 4 * k + 1) % 4 = 1 % 4
      omega
    have h1p2 : (1 + p ^ 2) ≡ 2 [MOD 4] := by
      have h := (Nat.ModEq.refl (1 : ℕ)).add hp1
      have h11 : (1 : ℕ) + 1 = 2 := rfl
      rwa [h11] at h
    have hL2 : (∑ i ∈ Finset.range (a + 1), 2 ^ (i * 2)) * (1 + p ^ 2) ≡ 2 [MOD 4] := by
      have h := hS1.mul h1p2
      rwa [one_mul] at h
    have hR0 : (2 ^ a * p) ^ 2 + d ^ 2 + l * (2 ^ a * p) ≡ 0 [MOD 4] := by
      have hN0 : (2 ^ a * p) ^ 2 ≡ 0 [MOD 4] :=
        Nat.modEq_zero_iff_dvd.mpr (h4n.trans (dvd_pow_self (2 ^ a * p) (by decide : 2 ≠ 0)))
      have hD0 : d ^ 2 ≡ 0 [MOD 4] := Nat.modEq_zero_iff_dvd.mpr h4d2
      have hL0 : l * (2 ^ a * p) ≡ 0 [MOD 4] :=
        Nat.modEq_zero_iff_dvd.mpr (h4n.trans (dvd_mul_left _ _))
      simpa only [add_zero] using (hN0.add hD0).add hL0
    have hcon : (2 : ℕ) ≡ 0 [MOD 4] := by
      rw [← hsum] at hR0
      exact hL2.symm.trans hR0
    exact absurd hcon (by decide)

end MathlibExt.NumberTheory.FkPerfectWanted
