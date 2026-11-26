/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import MathlibExt.NumberTheory.TwoNearPerfectOmittedDivisors
import MathlibExt.NumberTheory.TwoNearPerfectPowerOfTwoDivisors
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Two-near perfect numbers of the form `2^k p^2`

This module classifies two-near perfect numbers of the form `2^k p^2`, where `p` is prime.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61 (arXiv:2310.01305), Theorem 2.
-/

namespace MetaMathlibExt

private theorem divisor_form {k p d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : d ∣ 2 ^ k * p ^ 2) : ∃ a ≤ k, ∃ b ≤ 2, d = 2 ^ a * p ^ b := by
  have hc := Nat.coprime_pow_primes k 2 Nat.prime_two hp hp2.symm
  have he := (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hc).mpr hd
  obtain ⟨a, ha, hea⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Nat.gcd_dvd_right d (2 ^ k))
  obtain ⟨b, hb, heb⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right d (p ^ 2))
  exact ⟨a, ha, b, hb, by simpa only [hea, heb] using he.symm⟩

private theorem case_two {x y p : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y) (hyx : y ≤ x)
    (hp : 3 ≤ p) (hodd : p % 2 = 1) (hxodd : x % 2 = 0)
    (m : ℕ) (hm : m = 1 ∨ m = 2)
    (h : 2 * x * (p + 1) = p ^ 2 + p + 1 + p ^ m + y) : False := by
  rcases hm with rfl | rfl
  · simp only [pow_one] at h
    by_cases hle : p ≤ 2 * x - 2
    · have hle' : p ≤ 2 * x - 3 := by omega
      have ht : p + 3 ≤ 2 * x := by omega
      nlinarith [mul_nonneg (by omega : 0 ≤ p) (by omega : 0 ≤ 2 * x - (p + 3))]
    · have ht : 2 * x ≤ p + 1 := by omega
      nlinarith [mul_nonneg (by omega : 0 ≤ p) (by omega : 0 ≤ p + 1 - 2 * x)]
  · by_cases hle : p < x
    · have ht : p + 1 ≤ x := by omega
      nlinarith [mul_nonneg (by omega : 0 ≤ p) (by omega : 0 ≤ x - (p + 1))]
    · have ht : x + 1 ≤ p := by omega
      nlinarith [mul_nonneg (by omega : 0 ≤ p) (by omega : 0 ≤ p - (x + 1))]

private theorem case_one_prime {x y p : ℕ} (hy : 2 ≤ y) (hyx : y ≤ x)
    (hp : 3 ≤ p) (hodd : p % 2 = 1)
    (h : 2 * x * (p + 1) = p ^ 2 + p + 2 + y * p) : False := by
  have hf : (p + 1) * p + 2 = (p + 1) * (2 * x - y) + y := by
    have hle : y ≤ 2 * x := by omega
    nlinarith [Nat.sub_add_cancel hle]
  rcases eq_or_lt_of_le hy with rfl | hy'
  · have : p = 2 * x - 2 := by nlinarith [Nat.sub_add_cancel (by omega : 2 ≤ 2 * x)]
    omega
  · have hgt : 2 * x - y < p := by
      by_contra hn
      have hm := Nat.mul_le_mul_left (p + 1) (by omega : p ≤ 2 * x - y)
      omega
    nlinarith [Nat.sub_add_cancel (by omega : y ≤ 2 * x),
      Nat.mul_le_mul_left (p + 1) (by omega : 2 * x - y + 1 ≤ p)]

private theorem case_both_prime {x y p : ℕ} (hy : 2 ≤ y) (hyx : y ≤ x)
    (h : 2 * x * (p + 1) = p ^ 2 + 2 * p + 1 + y * p) : False := by
  by_cases hle : p + y < 2 * x
  · have ht : p + y + 1 ≤ 2 * x := by omega
    nlinarith [Nat.mul_le_mul_left p ht]
  · have ht : 2 * x ≤ p + y := by omega
    nlinarith [Nat.mul_le_mul_left (p + 1) ht]

private theorem square_bound {b p c : ℕ} (hb : 1 ≤ b) (hp : 3 ≤ p)
    (hodd : p % 2 = 1) (hc : c = 1 ∨ c = 2)
    (hC : (2 : ℤ) ^ b ∣ (c : ℤ) * p ^ 2 + p + 3 - c)
    (hs : (p + 1 : ℤ) ∣ 2 ^ b + 2) : p ≤ 5 := by
  have hy : (2 : ℤ) ≤ 2 ^ b := pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2) hb
  obtain ⟨z, hz⟩ := hs
  have hzpos : 0 < z := by nlinarith
  by_cases hb1 : b = 1
  · subst b
    norm_num at hz
    have hpz : (3 : ℤ) ≤ p := by exact_mod_cast hp
    have hz1 : 1 ≤ z := by omega
    nlinarith
  · have hb2 : 2 ≤ b := by omega
    have hy4 : (2 : ℤ) ^ b % 4 = 0 := by
      obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hb2
      rw [ht, pow_add]
      norm_num
    have hzodd : z % 2 = 1 := by
      have hm : ((2 : ℤ) ^ b + 2) % 4 =
          (((p : ℤ) + 1) % 4 * (z % 4)) % 4 := by rw [hz, Int.mul_emod]
      rw [Int.add_emod, hy4] at hm
      have hp4 : ((p : ℤ) + 1) % 4 = 0 ∨ ((p : ℤ) + 1) % 4 = 2 := by omega
      rcases hp4 with hp4 | hp4 <;> rw [hp4] at hm <;> omega
    have hprod : (2 : ℤ) ^ b ∣ ((p : ℤ) + 1) * (c * p + z + 1 - c) := by
      convert dvd_add hC (dvd_refl ((2 : ℤ) ^ b)) using 1; nlinarith [hz]
    have ht : (2 : ℤ) ^ b ∣ 2 * (c * (p : ℤ) + z + 1 - c) := by
      convert dvd_sub (hprod.mul_left z)
        (dvd_mul_right ((2 : ℤ) ^ b) (c * (p : ℤ) + z + 1 - c)) using 1;
        linear_combination (c * (p : ℤ) + z + 1 - c) * hz
    have hpz : (3 : ℤ) ≤ p := by exact_mod_cast hp
    have hcz : (c : ℤ) = 1 ∨ (c : ℤ) = 2 := by exact_mod_cast hc
    have hbound : (2 : ℤ) ^ b ≤ 2 * (c * (p : ℤ) + z + 1 - c) :=
      Int.le_of_dvd (by rcases hcz with hcz | hcz <;> rw [hcz] <;> nlinarith) ht
    by_contra hn
    have hp7 : (7 : ℤ) ≤ p := by omega
    have hz4 : z ≤ 4 := by
      by_contra hnz
      have hz5 : 5 ≤ z := by omega
      rcases hcz with hcz | hcz <;> rw [hcz] at hbound <;>
        nlinarith [mul_nonneg (by omega : 0 ≤ z - 5) (by omega : 0 ≤ (p : ℤ) - 1)]
    have hz13 : z = 1 ∨ z = 3 := by omega
    rcases hz13 with rfl | rfl
    · have hfour : (2 : ℤ) ^ b ∣ 4 := by
        rcases hcz with hcz | hcz
        · convert dvd_sub ht (dvd_mul_right ((2 : ℤ) ^ b) 2) using 1; nlinarith [hz]
        · convert dvd_sub ht (dvd_mul_right ((2 : ℤ) ^ b) 4) using 1; nlinarith [hz]
      have := Int.le_of_dvd (by decide : (0 : ℤ) < 4) hfour
      nlinarith
    · rcases hcz with hcz | hcz
      · rw [hcz] at hbound
        nlinarith
      · have height : (2 : ℤ) ^ b ∣ 8 := by
          convert dvd_sub (ht.mul_left 3) (dvd_mul_right ((2 : ℤ) ^ b) 4) using 1;
            nlinarith [hz, hcz]
        have := Int.le_of_dvd (by decide : (0 : ℤ) < 8) height
        nlinarith

private theorem odd_divisor_two_pow {d k : ℕ} (hodd : d % 2 = 1)
    (hd : d ∣ 2 ^ k) : d = 1 := by
  obtain ⟨a, _, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  cases a with
  | zero => rfl
  | succ a => simp only [pow_succ] at hodd; omega

private theorem pow_sum {a b c u : ℕ} (hu : 2 ≤ u) (hodd : u % 2 = 1)
    (h : 2 ^ a = 2 ^ b * u + 2 ^ c) : b = c := by
  rcases lt_trichotomy b c with hbc | hbc | hbc
  · have hec : 2 ^ c = 2 ^ b * 2 ^ (c - b) := by
      rw [← pow_add, show b + (c - b) = c by omega]
    have ht : u + 2 ^ (c - b) ∣ 2 ^ a := by
      refine ⟨2 ^ b, ?_⟩
      rw [h, hec]
      ring
    have ho : (u + 2 ^ (c - b)) % 2 = 1 := by
      cases he : c - b with
      | zero => omega
      | succ t => simpa [pow_succ] using hodd
    exfalso
    have hone : u + 2 ^ (c - b) = 1 := odd_divisor_two_pow ho ht
    nlinarith only [hu, hone, Nat.zero_le (2 ^ (c - b))]
  · exact hbc
  · have heb : 2 ^ b = 2 ^ c * 2 ^ (b - c) := by
      rw [← pow_add, show c + (b - c) = b by omega]
    have ht : 2 ^ (b - c) * u + 1 ∣ 2 ^ a := by
      refine ⟨2 ^ c, ?_⟩
      rw [h, heb]
      ring
    have ho : (2 ^ (b - c) * u + 1) % 2 = 1 := by
      cases he : b - c with
      | zero => omega
      | succ t =>
          rw [pow_succ, show 2 ^ t * 2 * u = 2 * (2 ^ t * u) by ring]
          omega
    exfalso
    have hone : 2 ^ (b - c) * u + 1 = 1 := odd_divisor_two_pow ho ht
    have hpos : 0 < 2 ^ (b - c) := by positivity
    nlinarith

private theorem no_prime_square_sum {p k : ℕ} (hp : 3 ≤ p) (hodd : p % 2 = 1)
    (hd : p ^ 2 + 1 ∣ 2 ^ k) : False := by
  obtain ⟨a, _, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have ha2 : 2 ≤ a := by
    by_contra hn
    interval_cases a <;> norm_num at ha <;> nlinarith
  have hfour : 2 ^ a % 4 = 0 := by
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le ha2
    rw [ht, pow_add]
    omega
  have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
  have hm := congrArg (fun n : ℕ => n % 4) ha
  rcases hp4 with hp4 | hp4 <;>
    rw [Nat.add_mod, Nat.pow_mod, hp4, hfour] at hm <;> norm_num at hm

private theorem case_prime_square {k b p : ℕ} (hp : 3 ≤ p) (hodd : p % 2 = 1)
    (h : 2 * 2 ^ k * (p + 1) = p ^ 2 + 2 * p + 1 + 2 ^ b * p ^ 2) : False := by
  have hc : (p + 1).Coprime (p ^ 2) :=
    (show p.Coprime (p + 1) by simp [Nat.coprime_self_add_right]).symm.pow_right 2
  have hd : p + 1 ∣ 2 ^ b := by
    apply hc.dvd_of_dvd_mul_right
    have hh : (p + 1 : ℤ) ∣ (2 : ℤ) ^ b * p ^ 2 := by
      refine ⟨2 * 2 ^ k - (p + 1), ?_⟩
      zify at h
      nlinarith [h]
    exact_mod_cast hh
  obtain ⟨c, _, hec⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have he : 2 ^ (k + 1 + c) = 2 ^ b * p ^ 2 + 2 ^ (c + c) := by
    rw [pow_add (2 : ℕ) (k + 1) c, pow_add (2 : ℕ) c c, pow_succ', ← hec]
    nlinarith [h]
  have heb : b = c + c := pow_sum (by nlinarith : 2 ≤ p ^ 2)
    (Nat.odd_iff.mp ((Nat.odd_iff.mpr hodd).pow)) he
  have hsmall : p ^ 2 + 1 ∣ 2 ^ (k + 1) := by
    refine ⟨p + 1, ?_⟩
    have hh : (p + 1) * (2 * 2 ^ k) = (p + 1) * ((p ^ 2 + 1) * (p + 1)) := by
      rw [heb, pow_add, ← hec] at h
      nlinarith [h]
    have hh' := Nat.mul_left_cancel (show 0 < p + 1 by omega) hh
    simpa only [pow_succ'] using hh'
  exact no_prime_square_sum hp hodd hsmall

private theorem case_square_prime {k b p : ℕ} (hb : 1 ≤ b) (hbk : b ≤ k)
    (hp : 3 ≤ p) (hodd : p % 2 = 1)
    (h : 2 * 2 ^ k * (p + 1) = 2 * p ^ 2 + p + 1 + 2 ^ b * p) :
    2 ^ k * p ^ 2 = 200 := by
  have hb2 : 2 ≤ b := by
    by_contra hn
    have hb1 : b = 1 := by omega
    rw [hb1] at h
    norm_num at h
    have he : (p + 1) * (2 * 2 ^ k) = (p + 1) * (2 * p + 1) := by nlinarith [h]
    have := Nat.mul_left_cancel (show 0 < p + 1 by omega) he
    omega
  have hkb : k = b := by
    by_contra hn
    have hlt : b + 1 ≤ k := by omega
    have hx : 4 * 2 ^ (b - 1) ≤ 2 ^ k := by
      have he : 4 * 2 ^ (b - 1) = 2 ^ (b + 1) := by
        rw [show b + 1 = (b - 1) + 2 by omega, pow_add]
        ring
      rw [he]
      exact Nat.pow_le_pow_right (by decide) hlt
    have hy : 2 ^ b = 2 * 2 ^ (b - 1) := by
      calc
        2 ^ b = 2 ^ ((b - 1) + 1) := by congr 1; omega
        _ = 2 * 2 ^ (b - 1) := pow_succ' _ _
    have hxmod : 2 ^ k % 2 = 0 := by
      cases k with
      | zero => omega
      | succ t => simp [pow_succ]
    have hymod : 2 ^ (b - 1) % 2 = 0 := by
      cases he : b - 1 with
      | zero => omega
      | succ t => simp [pow_succ]
    rw [hy] at h
    by_cases hle : p + 2 ^ (b - 1) < 2 ^ k
    · have ht : p + 2 ^ (b - 1) + 1 ≤ 2 ^ k := by omega
      have hm : 2 * p ^ 2 + 2 * 2 ^ (b - 1) * p + 2 * p ≤ 2 * 2 ^ k * p := by
        nlinarith only [Nat.mul_le_mul_left p ht]
      nlinarith only [h, hm, hp, Nat.zero_le (2 ^ k)]
    · have ht : 2 ^ k + 1 ≤ p + 2 ^ (b - 1) := by omega
      nlinarith [Nat.mul_le_mul_left (p + 1) ht]
  rw [hkb] at h ⊢
  have he : 2 ^ b * (p + 2) = 2 * p ^ 2 + p + 1 := by nlinarith [h]
  have hd : (p + 2 : ℤ) ∣ 7 := by
    refine ⟨(2 : ℤ) ^ b - 2 * p + 3, ?_⟩
    zify at he
    nlinarith [he]
  have hple := Int.le_of_dvd (by decide : (0 : ℤ) < 7) hd
  have hp35 : p = 3 ∨ p = 5 := by omega
  rcases hp35 with rfl | rfl
  · norm_num at he
    omega
  · norm_num at he ⊢
    omega

private theorem case_squares {k b p c : ℕ} (hb : 1 ≤ b) (hbk : b ≤ k)
    (hp : 3 ≤ p) (hodd : p % 2 = 1) (hc : c = 1 ∨ c = 2)
    (h : (2 : ℤ) ^ (k + 1) * (p + 1) = (2 ^ b + c) * p ^ 2 + p + 3 - c) :
    2 ^ k * p ^ 2 = 36 ∧ c = 1 := by
  have hdy : (2 : ℤ) ^ b ∣ 2 ^ (k + 1) := pow_dvd_pow 2 (by omega)
  have hC : (2 : ℤ) ^ b ∣ (c : ℤ) * p ^ 2 + p + 3 - c := by
    convert dvd_sub (hdy.mul_right ((p : ℤ) + 1))
      (dvd_mul_right ((2 : ℤ) ^ b) ((p : ℤ) ^ 2)) using 1; nlinarith [h]
  have hs : (p + 1 : ℤ) ∣ 2 ^ b + 2 := by
    refine ⟨2 ^ (k + 1) - (2 ^ b + c) * (p - 1) - 1, ?_⟩
    nlinarith [h]
  have hp5 := square_bound hb hp hodd hc hC hs
  have hp35 : p = 3 ∨ p = 5 := by omega
  have hy56 : (2 : ℤ) ^ b ≤ 56 := by
    have hpz : (c : ℤ) * p ^ 2 + p + 3 - c > 0 := by
      rcases hp35 with rfl | rfl <;> rcases hc with rfl | rfl <;> norm_num
    have hle := Int.le_of_dvd hpz hC
    rcases hp35 with rfl | rfl <;> rcases hc with rfl | rfl <;> norm_num at hle <;> omega
  have hb5 : b ≤ 5 := by
    by_contra hn
    have hle : (64 : ℤ) ≤ 2 ^ b :=
      pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2) (by omega : 6 ≤ b)
    omega
  have hy32 : (2 : ℤ) ^ b ≤ 32 :=
    pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2) hb5
  rw [pow_succ'] at h
  have hk7 : k ≤ 7 := by
    by_contra hn
    have hx256 : (256 : ℤ) ≤ 2 ^ k :=
      pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2) (by omega : 8 ≤ k)
    rcases hp35 with rfl | rfl <;> rcases hc with rfl | rfl <;> norm_num at h <;> nlinarith
  rcases hp35 with rfl | rfl <;> rcases hc with rfl | rfl <;>
    interval_cases b <;> interval_cases k <;> norm_num at h
  norm_num

private theorem ordered {k p d₁ d₂ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd₁ : d₁ ∣ 2 ^ k * p ^ 2) (hd₂ : d₂ ∣ 2 ^ k * p ^ 2) (hne : d₁ ≠ d₂)
    (hσ : ArithmeticFunction.sigma 1 (2 ^ k * p ^ 2) = 2 * (2 ^ k * p ^ 2) + d₁ + d₂)
    (hodd : d₁ % 2 = 1) :
    2 ^ k * p ^ 2 = 18 ∨ 2 ^ k * p ^ 2 = 36 ∨ 2 ^ k * p ^ 2 = 200 := by
  obtain ⟨hsum, hpar⟩ := omitted_divisors_sum_two_pow_mul_prime_sq
    hp hp2 hd₁ hd₂ hne hσ
  obtain ⟨a, _, m, hm, rfl⟩ := divisor_form hp hp2 hd₁
  obtain ⟨b, hbk, j, hj, rfl⟩ := divisor_form hp hp2 hd₂
  have ha : a = 0 := by
    cases a with
    | zero => rfl
    | succ a =>
        rw [pow_succ, show 2 ^ a * 2 * p ^ m = 2 * (2 ^ a * p ^ m) by ring] at hodd
        omega
  subst a
  simp only [pow_zero, one_mul] at hσ hsum hpar hodd hne
  have hpodd := hp.odd_of_ne_two hp2
  have hpmod := Nat.odd_iff.mp hpodd
  have hb : 1 ≤ b := by
    by_contra hn
    have hb0 : b = 0 := by omega
    have hjodd := Nat.odd_iff.mp (hpodd.pow (n := j))
    simp only [hb0, pow_zero, one_mul] at hpar
    omega
  have he : 2 * 2 ^ k * (p + 1) = p ^ 2 + p + 1 + p ^ m + 2 ^ b * p ^ j := by
    zify
    push_cast at hsum
    rw [pow_succ' (2 : ℤ) k] at hsum
    nlinarith only [hsum]
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hx : 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ k)
  have hy : 2 ≤ 2 ^ b := Nat.pow_le_pow_right (by decide : 0 < 2) hb
  have hyx : 2 ^ b ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) hbk
  have hxmod : 2 ^ k % 2 = 0 := by
    cases k with
    | zero => omega
    | succ t => simp [pow_succ]
  interval_cases m <;> interval_cases j <;>
    simp only [pow_zero, pow_one, one_mul, mul_one] at he hd₁
  · left
    exact (two_near_perfect_two_pow_mul_prime_sq_case_one hp hp2
      (Nat.zero_le k) hbk (by omega : 0 ≠ b) (by simpa using hσ)).1
  · exfalso
    exact case_one_prime hy hyx hp3 hpmod (by omega)
  · right; left
    apply (case_squares hb hbk hp3 hpmod (Or.inl rfl) ?_).1
    zify at he
    rw [pow_succ']
    norm_num
    nlinarith [he]
  · exfalso
    exact case_two hx hy hyx hp3 hpmod hxmod 1 (Or.inl rfl) (by simpa using he)
  · exfalso
    apply case_both_prime hy hyx
    nlinarith [he]
  · exfalso
    apply case_prime_square (b := b) hp3 hpmod
    nlinarith [he]
  · exfalso
    exact case_two hx hy hyx hp3 hpmod hxmod 2 (Or.inr rfl) (by simpa using he)
  · right; right
    apply case_square_prime hb hbk hp3 hpmod
    nlinarith [he]
  · exfalso
    have hh := case_squares (c := 2) hb hbk hp3 hpmod (Or.inr rfl) (by
      zify at he
      rw [pow_succ']
      norm_num
      nlinarith [he])
    omega

/-- **$2$-near perfect numbers of the form $2^k p^2$.** Let $p$ be a prime, let $k$ be a natural
number and let $n = 2^k p^2$. If $n$ has divisors $d_1 \ne d_2$ with
$\sigma(n) = 2n + d_1 + d_2$, where $\sigma$ is the sum-of-divisors function (that is, $n$ is
$2$-near perfect with omitted divisors $d_1, d_2$), then $n$ is $18$, $36$ or $200$.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Theorem 2
(`integers-2024-A61-thm-2`). -/
public theorem two_near_perfect_two_pow_mul_prime_sq {k p d₁ d₂ : ℕ} (hp : p.Prime)
    (hd₁ : d₁ ∣ 2 ^ k * p ^ 2) (hd₂ : d₂ ∣ 2 ^ k * p ^ 2) (hne : d₁ ≠ d₂)
    (hσ : ArithmeticFunction.sigma 1 (2 ^ k * p ^ 2) = 2 * (2 ^ k * p ^ 2) + d₁ + d₂) :
    2 ^ k * p ^ 2 = 18 ∨ 2 ^ k * p ^ 2 = 36 ∨ 2 ^ k * p ^ 2 = 200 := by
  by_cases hp2 : p = 2
  · subst p
    rw [← pow_add] at hσ
    have ht : ArithmeticFunction.sigma 1 (2 ^ (k + 2)) + 1 = 2 * 2 ^ (k + 2) := by
      rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
      simpa only [one_add_one_eq_two, mul_one, pow_succ'] using
        geom_sum_mul_add (1 : ℕ) (k + 2 + 1)
    omega
  · by_cases hodd : d₁ % 2 = 1
    · exact ordered hp hp2 hd₁ hd₂ hne hσ hodd
    · have hpar := (omitted_divisors_sum_two_pow_mul_prime_sq
        hp hp2 hd₁ hd₂ hne hσ).2
      exact ordered hp hp2 hd₂ hd₁ hne.symm (by simpa [add_comm, add_left_comm] using hσ)
        (by omega)

end MetaMathlibExt
