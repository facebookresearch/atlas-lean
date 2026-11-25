/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Pillai equations and Steuerwald's theorem
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

@[expose] public section

/-- Geometric sum of powers of two, stated to avoid natural subtraction. -/
private lemma sum_pow_two_add_one (n : ℕ) :
    (∑ i ∈ Finset.range n, 2 ^ i) + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

/-- Twice the geometric sum of powers of three, stated to avoid subtraction. -/
private lemma two_mul_sum_pow_three_add_one (n : ℕ) :
    2 * (∑ i ∈ Finset.range n, 3 ^ i) + 1 = 3 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

/-- The divisor sum of a power of two: `σ(2^a) = 2^{a+1} - 1`. -/
private lemma sigma_prime_pow_two (a : ℕ) :
    (ArithmeticFunction.sigma 1) (2 ^ a) = 2 ^ (a + 1) - 1 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
  have h := sum_pow_two_add_one (a + 1)
  omega

/-- Twice the divisor sum of a power of three: `2 * σ(3^b) = 3^{b+1} - 1`. -/
private lemma two_mul_sigma_prime_pow_three (b : ℕ) :
    2 * (ArithmeticFunction.sigma 1) (3 ^ b) = 3 ^ (b + 1) - 1 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_three]
  have h := two_mul_sum_pow_three_add_one (b + 1)
  omega

/-- If `p ^ e = p` with `2 ≤ p` then `e = 1`. -/
private lemma pow_eq_base_of_two_le {p e : ℕ} (hp : 2 ≤ p) (h : p ^ e = p) :
    e = 1 := by
  by_contra hc
  rcases lt_or_gt_of_ne hc with hlt | hgt
  · have he0 : e = 0 := by omega
    subst he0
    simp at h
    omega
  · have hle : p ^ 2 ≤ p ^ e := pow_le_pow_right₀ (by omega) hgt
    rw [h] at hle
    have hp0 : 0 < p := by omega
    have hmul : p * p ≤ p * 1 := by simpa [pow_two] using hle
    have := Nat.le_of_mul_le_mul_left hmul hp0
    omega

/-- First exponential Diophantine lemma: `2 ^ x = 3 ^ y + 1` with `x ≥ 2`
    forces `(x, y) = (2, 1)`. -/
private lemma pillaiA {x y : ℕ} (hx : 2 ≤ x) (h : 2 ^ x = 3 ^ y + 1) :
    x = 2 ∧ y = 1 := by
  have hy1 : 1 ≤ y := by
    rcases Nat.eq_zero_or_pos y with rfl | hpos
    · simp only [pow_zero] at h
      norm_num at h
      have hle : (2 : ℕ) ^ 2 ≤ 2 ^ x := pow_le_pow_right₀ (by norm_num) hx
      norm_num at hle
      omega
    · exact hpos
  have hxeven : Even x := by
    by_contra hc
    rw [Nat.not_even_iff_odd] at hc
    obtain ⟨u, rfl⟩ := hc
    have h1 : (2 : ℕ) ^ (2 * u) = 4 ^ u := by
      rw [pow_mul]
      norm_num
    have e1 : (2 : ℕ) ^ (2 * u + 1) = 2 * 4 ^ u := by
      calc (2 : ℕ) ^ (2 * u + 1) = 2 ^ (2 * u) * 2 ^ 1 := pow_add 2 (2 * u) 1
        _ = 2 * 4 ^ u := by rw [h1]; ring
    have e2 : (4 ^ u) % 3 = 1 := by
      have hpm := Nat.pow_mod 4 u 3
      rw [show (4 : ℕ) % 3 = 1 from rfl] at hpm
      simpa using hpm
    have h2 : (2 ^ (2 * u + 1)) % 3 = 2 := by
      rw [e1, Nat.mul_mod, e2, show (2 : ℕ) % 3 = 2 from rfl]
    have hz : (3 ^ y) % 3 = 0 := by
      have hpm := Nat.pow_mod 3 y 3
      rw [show (3 : ℕ) % 3 = 0 from rfl] at hpm
      rw [zero_pow (by omega : y ≠ 0)] at hpm
      simpa using hpm
    have hcon := congrArg (· % 3) h
    rw [Nat.add_mod, hz] at hcon
    norm_num at hcon
    rw [h2] at hcon
    norm_num at hcon
  obtain ⟨u, rfl⟩ := hxeven
  have hu1 : 1 ≤ u := by omega
  have ht2 : 2 ≤ (2 : ℕ) ^ u :=
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ u := pow_le_pow_right₀ (by norm_num) hu1
  have hsq : ((2 : ℕ) ^ u) ^ 2 = 3 ^ y + 1 := by
    rw [pow_two]
    have hpow : (2 : ℕ) ^ (u + u) = 2 ^ u * 2 ^ u := pow_add 2 u u
    rw [hpow] at h
    exact h
  obtain ⟨v, hv⟩ := Nat.exists_eq_succ_of_ne_zero (show (2 : ℕ) ^ u ≠ 0 by positivity)
  have hv' : (2 : ℕ) ^ u = v + 1 := hv
  have hfactor : ((2 : ℕ) ^ u - 1) * ((2 : ℕ) ^ u + 1) = 3 ^ y := by
    rw [hv', Nat.add_sub_cancel]
    have e : (v + 1) ^ 2 = v * (v + 1 + 1) + 1 := by ring
    rw [hv'] at hsq
    omega
  have hdvd1 : ((2 : ℕ) ^ u - 1) ∣ 3 ^ y := ⟨(2 : ℕ) ^ u + 1, hfactor.symm⟩
  have hdvd2 : ((2 : ℕ) ^ u + 1) ∣ 3 ^ y :=
    ⟨(2 : ℕ) ^ u - 1, by rw [mul_comm]; exact hfactor.symm⟩
  obtain ⟨s, -, hs_eq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd1
  obtain ⟨t, -, ht_eq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd2
  have hsub : (3 : ℕ) ^ t - 3 ^ s = 2 := by omega
  have hlt : (3 : ℕ) ^ s < 3 ^ t := by omega
  have hst : s < t := by
    by_contra hc
    have hc' : t ≤ s := not_lt.mp hc
    have hle : (3 : ℕ) ^ t ≤ 3 ^ s := pow_le_pow_right₀ (by norm_num) hc'
    omega
  have hdvdst : (3 : ℕ) ^ s ∣ 3 ^ t := pow_dvd_pow 3 (le_of_lt hst)
  have htplus : (3 : ℕ) ^ t = 3 ^ s + 2 := by omega
  have h3s2 : (3 : ℕ) ^ s ∣ 2 := by
    have hmem : (3 : ℕ) ^ s ∣ 3 ^ s + 2 := by
      rw [← htplus]
      exact hdvdst
    exact (Nat.dvd_add_right (dvd_refl ((3 : ℕ) ^ s))).mp hmem
  have hs0 : s = 0 := by
    by_contra hc
    have hs1 : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hc
    have h3dvd : (3 : ℕ) ∣ 3 ^ s := by
      have htrans := pow_dvd_pow (3 : ℕ) hs1
      simp only [pow_one] at htrans
      exact htrans
    have h32 : (3 : ℕ) ∣ 2 := dvd_trans h3dvd h3s2
    obtain ⟨k, hk⟩ := h32
    omega
  have ht3 : (3 : ℕ) ^ t = 3 := by
    rw [hs0] at hsub
    simp at hsub
    omega
  have ht1 : t = 1 := pow_eq_base_of_two_le (by norm_num) ht3
  have hy3 : (3 : ℕ) ^ y = 3 := by
    have htmp := hfactor
    rw [hs_eq, ht_eq, hs0, ht1] at htmp
    norm_num at htmp
    exact htmp.symm
  have hy_eq : y = 1 := pow_eq_base_of_two_le (by norm_num) hy3
  have hu2 : (2 : ℕ) ^ u = 2 := by
    have h1 : (2 : ℕ) ^ u = ((2 : ℕ) ^ u - 1) + 1 := by omega
    rw [h1, hs_eq, hs0]
    norm_num
  have hu_eq : u = 1 := pow_eq_base_of_two_le (by norm_num) hu2
  exact ⟨by omega, hy_eq⟩

/-- Injectivity of `b ^ ·` for `2 ≤ b`. -/
private lemma pow_eq_pow_of_two_le {b m n : ℕ} (hb : 2 ≤ b) (h : b ^ m = b ^ n) :
    m = n := by
  by_contra hc
  rcases lt_or_gt_of_ne hc with hlt | hgt
  · have hlt' := (pow_lt_pow_iff_right₀ (by omega : (1 : ℕ) < b)).mpr hlt
    omega
  · have hgt' := (pow_lt_pow_iff_right₀ (by omega : (1 : ℕ) < b)).mpr hgt
    omega

/-- Second exponential Diophantine lemma: `3 ^ y = 2 ^ x + 1` with `y ≥ 2`
    forces `(x, y) = (3, 2)`. -/
private lemma pillaiB {x y : ℕ} (hy : 2 ≤ y) (h : 3 ^ y = 2 ^ x + 1) :
    x = 3 ∧ y = 2 := by
  have h9 : (9 : ℕ) ≤ 3 ^ y := by
    have hle : (3 : ℕ) ^ 2 ≤ 3 ^ y := pow_le_pow_right₀ (by norm_num) hy
    norm_num at hle
    exact hle
  have hx3 : 3 ≤ x := by
    by_contra hc
    have hx2 : x ≤ 2 := by omega
    have hle : (2 : ℕ) ^ x ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) hx2
    norm_num at hle
    omega
  have hyeven : Even y := by
    by_contra hc
    rw [Nat.not_even_iff_odd] at hc
    obtain ⟨w, rfl⟩ := hc
    have h1 : (3 : ℕ) ^ (2 * w) = 9 ^ w := by
      rw [pow_mul]
      norm_num
    have e1 : (3 : ℕ) ^ (2 * w + 1) = 3 * 9 ^ w := by
      calc (3 : ℕ) ^ (2 * w + 1) = 3 ^ (2 * w) * 3 ^ 1 := pow_add 3 (2 * w) 1
        _ = 3 * 9 ^ w := by rw [h1]; ring
    have e2 : (9 ^ w) % 4 = 1 := by
      have hpm := Nat.pow_mod 9 w 4
      rw [show (9 : ℕ) % 4 = 1 from rfl] at hpm
      simpa using hpm
    have h3 : (3 ^ (2 * w + 1)) % 4 = 3 := by
      rw [e1, Nat.mul_mod, e2, show (3 : ℕ) % 4 = 3 from rfl]
    have hx2 : (2 ^ x) % 4 = 0 := by
      obtain ⟨v, hv⟩ := Nat.exists_eq_add_of_le (show 2 ≤ x by omega)
      rw [hv, pow_add, Nat.mul_mod, show (2 : ℕ) ^ 2 % 4 = 0 from rfl]
      simp
    have hcon := congrArg (· % 4) h
    rw [Nat.add_mod, hx2] at hcon
    norm_num at hcon
    rw [h3] at hcon
    norm_num at hcon
  obtain ⟨v, rfl⟩ := hyeven
  have hv1 : 1 ≤ v := by omega
  have h3v1 : 1 ≤ (3 : ℕ) ^ v := one_le_pow₀ (by norm_num)
  have hsq : ((3 : ℕ) ^ v) ^ 2 = 2 ^ x + 1 := by
    rw [pow_two]
    have hpow : (3 : ℕ) ^ (v + v) = 3 ^ v * 3 ^ v := pow_add 3 v v
    rw [hpow] at h
    exact h
  obtain ⟨w, hw⟩ := Nat.exists_eq_succ_of_ne_zero (show (3 : ℕ) ^ v ≠ 0 by positivity)
  have hw' : (3 : ℕ) ^ v = w + 1 := hw
  have hfactor : ((3 : ℕ) ^ v - 1) * ((3 : ℕ) ^ v + 1) = 2 ^ x := by
    rw [hw', Nat.add_sub_cancel]
    have e : (w + 1) ^ 2 = w * (w + 1 + 1) + 1 := by ring
    rw [hw'] at hsq
    omega
  have hdvd1 : ((3 : ℕ) ^ v - 1) ∣ 2 ^ x := ⟨(3 : ℕ) ^ v + 1, hfactor.symm⟩
  have hdvd2 : ((3 : ℕ) ^ v + 1) ∣ 2 ^ x :=
    ⟨(3 : ℕ) ^ v - 1, by rw [mul_comm]; exact hfactor.symm⟩
  obtain ⟨s, -, hs_eq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd1
  obtain ⟨t, -, ht_eq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
  have hsub : (2 : ℕ) ^ t - 2 ^ s = 2 := by omega
  have hlt : (2 : ℕ) ^ s < 2 ^ t := by omega
  have hst : s < t := by
    by_contra hc
    have hc' : t ≤ s := not_lt.mp hc
    have hle : (2 : ℕ) ^ t ≤ 2 ^ s := pow_le_pow_right₀ (by norm_num) hc'
    omega
  have hdvdst : (2 : ℕ) ^ s ∣ 2 ^ t := pow_dvd_pow 2 (le_of_lt hst)
  have htplus : (2 : ℕ) ^ t = 2 ^ s + 2 := by omega
  have hs1 : 1 ≤ s := by
    have hodd : Odd ((3 : ℕ) ^ v) := Odd.pow ⟨1, rfl⟩
    have heven : Even ((3 : ℕ) ^ v - 1) := Nat.Odd.sub_odd hodd ⟨0, rfl⟩
    rw [hs_eq] at heven
    by_contra hc
    have hc0 : s = 0 := by omega
    rw [hc0] at heven
    obtain ⟨k, hk⟩ := heven
    norm_num at hk
    omega
  have h2s2 : (2 : ℕ) ^ s ∣ 2 := by
    have hmem : (2 : ℕ) ^ s ∣ 2 ^ s + 2 := by
      rw [← htplus]
      exact hdvdst
    exact (Nat.dvd_add_right (dvd_refl ((2 : ℕ) ^ s))).mp hmem
  have hs_eq1 : s = 1 := by
    by_contra hc
    have hs2 : 2 ≤ s := by omega
    have h4dvd : (2 : ℕ) ^ 2 ∣ 2 ^ s := pow_dvd_pow 2 hs2
    have h42 : (2 : ℕ) ^ 2 ∣ 2 := dvd_trans h4dvd h2s2
    obtain ⟨k, hk⟩ := h42
    norm_num at hk
    omega
  have ht4 : (2 : ℕ) ^ t = 4 := by
    rw [hs_eq1] at htplus
    norm_num at htplus
    exact htplus
  have ht_eq2 : t = 2 := by
    have h4 : (2 : ℕ) ^ t = 2 ^ 2 := by rw [ht4]; norm_num
    exact pow_eq_pow_of_two_le (by norm_num) h4
  have hx8 : (2 : ℕ) ^ x = 8 := by
    have htmp := hfactor
    rw [hs_eq, ht_eq, hs_eq1, ht_eq2] at htmp
    norm_num at htmp
    omega
  have hx_eq : x = 3 := by
    have h83 : (2 : ℕ) ^ x = 2 ^ 3 := by rw [hx8]; norm_num
    exact pow_eq_pow_of_two_le (by norm_num) h83
  have hv3 : (3 : ℕ) ^ v = 3 := by
    have h1 : (3 : ℕ) ^ v = ((3 : ℕ) ^ v - 1) + 1 := by omega
    rw [h1, hs_eq, hs_eq1]
    norm_num
  have hv_eq : v = 1 := pow_eq_base_of_two_le (by norm_num) hv3
  exact ⟨hx_eq, by omega⟩

/-- Odd powers of two are `2` mod `3`. -/
private lemma odd_pow_two_mod_three {n : ℕ} (h : Odd n) : (2 ^ n) % 3 = 2 := by
  obtain ⟨u, rfl⟩ := h
  have h1 : (2 : ℕ) ^ (2 * u) = 4 ^ u := by
    rw [pow_mul]
    norm_num
  have h4 : (4 ^ u) % 3 = 1 := by
    have hpm := Nat.pow_mod 4 u 3
    rw [show (4 : ℕ) % 3 = 1 from rfl] at hpm
    simpa using hpm
  have e : (2 : ℕ) ^ (2 * u + 1) = 2 * 4 ^ u := by
    calc (2 : ℕ) ^ (2 * u + 1) = 2 ^ (2 * u) * 2 ^ 1 := pow_add 2 (2 * u) 1
      _ = 2 * 4 ^ u := by rw [h1]; ring
  rw [e, Nat.mul_mod, h4, show (2 : ℕ) % 3 = 2 from rfl]

/-- Odd powers of three are `3` mod `4`. -/
private lemma odd_pow_three_mod_four {n : ℕ} (h : Odd n) : (3 ^ n) % 4 = 3 := by
  obtain ⟨u, rfl⟩ := h
  have h1 : (3 : ℕ) ^ (2 * u) = 9 ^ u := by
    rw [pow_mul]
    norm_num
  have h9 : (9 ^ u) % 4 = 1 := by
    have hpm := Nat.pow_mod 9 u 4
    rw [show (9 : ℕ) % 4 = 1 from rfl] at hpm
    simpa using hpm
  have e : (3 : ℕ) ^ (2 * u + 1) = 3 * 9 ^ u := by
    calc (3 : ℕ) ^ (2 * u + 1) = 3 ^ (2 * u) * 3 ^ 1 := pow_add 3 (2 * u) 1
      _ = 3 * 9 ^ u := by rw [h1]; ring
  rw [e, Nat.mul_mod, h9, show (3 : ℕ) % 4 = 3 from rfl]

/-- Even powers of four are `1` mod `5`. -/
private lemma pow_four_mod_five_even {n : ℕ} (h : Even n) : (4 ^ n) % 5 = 1 := by
  obtain ⟨u, hu⟩ := h
  have h16 : (4 : ℕ) ^ (u + u) = 16 ^ u := by
    rw [pow_add, ← mul_pow]
    norm_num
  rw [hu, h16]
  have hpm := Nat.pow_mod 16 u 5
  rw [show (16 : ℕ) % 5 = 1 from rfl] at hpm
  simpa using hpm

/-- Odd powers of four are `4` mod `5`. -/
private lemma pow_four_mod_five_odd {n : ℕ} (h : Odd n) : (4 ^ n) % 5 = 4 := by
  obtain ⟨u, hu⟩ := h
  have h16 : (4 : ℕ) ^ (2 * u) = 16 ^ u := by
    rw [pow_mul]
    norm_num
  have e : (4 : ℕ) ^ (2 * u + 1) = 4 * 16 ^ u := by
    calc (4 : ℕ) ^ (2 * u + 1) = 4 ^ (2 * u) * 4 ^ 1 := pow_add 4 (2 * u) 1
      _ = 4 * 16 ^ u := by rw [h16]; ring
  have h16m : (16 ^ u) % 5 = 1 := by
    have hpm := Nat.pow_mod 16 u 5
    rw [show (16 : ℕ) % 5 = 1 from rfl] at hpm
    simpa using hpm
  rw [hu, e, Nat.mul_mod, h16m, show (4 : ℕ) % 5 = 4 from rfl]

/-- Even powers of nine are `1` mod `5`. -/
private lemma pow_nine_mod_five_even {n : ℕ} (h : Even n) : (9 ^ n) % 5 = 1 := by
  obtain ⟨u, hu⟩ := h
  have h81 : (9 : ℕ) ^ (u + u) = 81 ^ u := by
    rw [pow_add, ← mul_pow]
    norm_num
  rw [hu, h81]
  have hpm := Nat.pow_mod 81 u 5
  rw [show (81 : ℕ) % 5 = 1 from rfl] at hpm
  simpa using hpm

/-- Odd powers of nine are `4` mod `5`. -/
private lemma pow_nine_mod_five_odd {n : ℕ} (h : Odd n) : (9 ^ n) % 5 = 4 := by
  obtain ⟨u, hu⟩ := h
  have h81 : (9 : ℕ) ^ (2 * u) = 81 ^ u := by
    rw [pow_mul]
    norm_num
  have e : (9 : ℕ) ^ (2 * u + 1) = 9 * 81 ^ u := by
    calc (9 : ℕ) ^ (2 * u + 1) = 9 ^ (2 * u) * 9 ^ 1 := pow_add 9 (2 * u) 1
      _ = 9 * 81 ^ u := by rw [h81]; ring
  have h81m : (81 ^ u) % 5 = 1 := by
    have hpm := Nat.pow_mod 81 u 5
    rw [show (81 : ℕ) % 5 = 1 from rfl] at hpm
    simpa using hpm
  rw [hu, e, Nat.mul_mod, h81m, show (9 : ℕ) % 5 = 4 from rfl]

/-- Powers `2 ^ e` with `e ≥ 1` are even. -/
private lemma even_two_pow {e : ℕ} (h : 1 ≤ e) : Even ((2 : ℕ) ^ e) := by
  obtain ⟨v, hv⟩ := Nat.exists_eq_add_of_le h
  have e2 : (2 : ℕ) ^ (1 + v) = 2 ^ v + 2 ^ v := by
    rw [pow_add]
    ring
  rw [hv]
  exact ⟨2 ^ v, e2⟩

/-- Second half of the third Diophantine lemma: from the doubled equation and
    `V` odd, conclude `(X, Y, Z) = (4, 2, 3)`. -/
private lemma pillaiC_finish {U V W : ℕ} (hVod : Odd V)
    (h : 2 ^ (U + U) + 1 = 3 ^ (V + V) + 2 ^ (2 * W + 1)) :
    U + U = 4 ∧ V + V = 2 ∧ 2 * W + 1 = 3 := by
  obtain ⟨v, hvV⟩ := hVod
  have hY2 : 2 ≤ V + V := by omega
  have h3Y9 : (9 : ℕ) ≤ 3 ^ (V + V) := by
    have hle : (3 : ℕ) ^ 2 ≤ 3 ^ (V + V) := pow_le_pow_right₀ (by norm_num) hY2
    norm_num at hle
    exact hle
  have hYf : V + V = 4 * v + 2 := by omega
  have h3Y8 : ∃ T, 3 ^ (V + V) - 1 = 8 * T ∧ Odd T := by
    rw [hYf]
    have h81v : (81 : ℕ) ^ v = 16 * (81 ^ v / 16) + 1 := by
      have hpm := Nat.pow_mod 81 v 16
      rw [show (81 : ℕ) % 16 = 1 from rfl] at hpm
      have h1 : (81 ^ v) % 16 = 1 := by simpa using hpm
      omega
    have h3f : (3 : ℕ) ^ (4 * v + 2) = 9 * 81 ^ v := by
      have h1 : (3 : ℕ) ^ (4 * v) = 81 ^ v := by
        rw [pow_mul]
        norm_num
      calc (3 : ℕ) ^ (4 * v + 2) = 3 ^ (4 * v) * 3 ^ 2 := pow_add 3 (4 * v) 2
        _ = 9 * 81 ^ v := by rw [h1]; ring
    refine ⟨18 * (81 ^ v / 16) + 1, ?_, ?_⟩
    · rw [h3f]
      omega
    · exact ⟨9 * (81 ^ v / 16), by ring⟩
  have hXgtZ : 2 * W + 1 < U + U := by
    by_contra hc
    have hc' : U + U ≤ 2 * W + 1 := not_lt.mp hc
    have hle : (2 : ℕ) ^ (U + U) ≤ 2 ^ (2 * W + 1) :=
      pow_le_pow_right₀ (by norm_num) hc'
    omega
  have hfactorZ : (2 : ℕ) ^ (2 * W + 1) * (2 ^ ((U + U) - (2 * W + 1)) - 1)
      = 3 ^ (V + V) - 1 := by
    have hXZ : (2 * W + 1) + ((U + U) - (2 * W + 1)) = U + U :=
      Nat.add_sub_cancel' (le_of_lt hXgtZ)
    have hpow : (2 : ℕ) ^ (U + U)
        = 2 ^ (2 * W + 1) * 2 ^ ((U + U) - (2 * W + 1)) := by
      conv_lhs => rw [← hXZ]
      rw [pow_add]
    obtain ⟨w, hw⟩ := Nat.exists_eq_succ_of_ne_zero
      (show (2 : ℕ) ^ ((U + U) - (2 * W + 1)) ≠ 0 by positivity)
    have hw' : (2 : ℕ) ^ ((U + U) - (2 * W + 1)) = w + 1 := hw
    rw [hw', Nat.add_sub_cancel]
    have hexp : (2 : ℕ) ^ (2 * W + 1) * (w + 1)
        = 2 ^ (2 * W + 1) * w + 2 ^ (2 * W + 1) := by ring
    rw [hpow, hw', hexp] at h
    have h1 : (2 : ℕ) ^ (2 * W + 1) * w + 1 + 2 ^ (2 * W + 1)
        = 3 ^ (V + V) + 2 ^ (2 * W + 1) := by
      rw [← h]
      ring
    have h2 : (2 : ℕ) ^ (2 * W + 1) * w + 1 = 3 ^ (V + V) :=
      Nat.add_right_cancel h1
    have e : (2 : ℕ) ^ (2 * W + 1) * w + 1 - 1
        = (2 ^ (2 * W + 1)) * w := Nat.add_sub_cancel _ _
    rw [h2] at e
    exact e.symm
  obtain ⟨T, hT8, hTodd⟩ := h3Y8
  rw [hT8] at hfactorZ
  have hO1 : Odd ((2 : ℕ) ^ ((U + U) - (2 * W + 1)) - 1) := by
    have hXZ1 : 1 ≤ (U + U) - (2 * W + 1) := by omega
    have heven : Even ((2 : ℕ) ^ ((U + U) - (2 * W + 1))) :=
      even_two_pow hXZ1
    have h1lt : 1 ≤ (2 : ℕ) ^ ((U + U) - (2 * W + 1)) :=
      one_le_pow₀ (by norm_num)
    exact Nat.Even.sub_odd h1lt heven ⟨0, rfl⟩
  have hZ3 : 2 * W + 1 = 3 := by
    by_contra hc
    rcases lt_or_gt_of_ne hc with hlt | hgt
    · have hle : 2 * W + 1 ≤ 3 := by omega
      have hZZ : (2 * W + 1) + (3 - (2 * W + 1)) = 3 :=
        Nat.add_sub_cancel' hle
      have h8 : (8 : ℕ) = 2 ^ (2 * W + 1) * 2 ^ (3 - (2 * W + 1)) := by
        have h3 : (2 : ℕ) ^ 3
            = 2 ^ (2 * W + 1) * 2 ^ (3 - (2 * W + 1)) := by
          conv_lhs => rw [← hZZ]
          rw [pow_add]
        norm_num at h3 ⊢
        exact h3
      have h9 : (2 : ℕ) ^ (2 * W + 1) * ((2 : ℕ) ^ ((U + U) - (2 * W + 1)) - 1)
          = 2 ^ (2 * W + 1) * (2 ^ (3 - (2 * W + 1)) * T) := by
        rw [hfactorZ, h8]
        ring
      have hcancel : (2 : ℕ) ^ ((U + U) - (2 * W + 1)) - 1
          = 2 ^ (3 - (2 * W + 1)) * T :=
        mul_left_cancel₀ (by positivity) h9
      have hevenR : Even ((2 : ℕ) ^ (3 - (2 * W + 1)) * T) :=
        Even.mul_right (even_two_pow (by omega)) T
      rw [← hcancel] at hevenR
      obtain ⟨a, ha⟩ := hO1
      obtain ⟨b, hb⟩ := hevenR
      omega
    · have hge : 3 ≤ 2 * W + 1 := by omega
      have hZZ : 3 + ((2 * W + 1) - 3) = 2 * W + 1 :=
        Nat.add_sub_cancel' hge
      have h2Z : (2 : ℕ) ^ (2 * W + 1) = 8 * 2 ^ ((2 * W + 1) - 3) := by
        conv_lhs => rw [← hZZ]
        rw [pow_add]
        norm_num
      have h9 : (8 : ℕ) * ((2 : ℕ) ^ ((2 * W + 1) - 3)
            * ((2 : ℕ) ^ ((U + U) - (2 * W + 1)) - 1)) = 8 * T := by
        have h10 : (2 : ℕ) ^ (2 * W + 1)
            * ((2 : ℕ) ^ ((U + U) - (2 * W + 1)) - 1)
            = 8 * ((2 : ℕ) ^ ((2 * W + 1) - 3)
              * ((2 : ℕ) ^ ((U + U) - (2 * W + 1)) - 1)) := by
          rw [h2Z]
          ring
        rw [hfactorZ] at h10
        exact h10.symm
      have hcancel : (2 : ℕ) ^ ((2 * W + 1) - 3)
          * ((2 : ℕ) ^ ((U + U) - (2 * W + 1)) - 1) = T :=
        mul_left_cancel₀ (by norm_num) h9
      have hevenL : Even ((2 : ℕ) ^ ((2 * W + 1) - 3)
          * ((2 : ℕ) ^ ((U + U) - (2 * W + 1)) - 1)) :=
        Even.mul_right (even_two_pow (by omega)) _
      rw [hcancel] at hevenL
      obtain ⟨a, ha⟩ := hTodd
      obtain ⟨b, hb⟩ := hevenL
      omega
  rw [hZ3] at h
  norm_num at h
  have hXY7 : (2 : ℕ) ^ (U + U) = 3 ^ (V + V) + 7 := by omega
  have hsq2U : ((2 : ℕ) ^ U) ^ 2 = 2 ^ (U + U) := by
    rw [pow_two, pow_add]
  have hsq3V : ((3 : ℕ) ^ V) ^ 2 = 3 ^ (V + V) := by
    rw [pow_two, pow_add]
  have h2Ugt : (3 : ℕ) ^ V < 2 ^ U := by
    have hlt : ((3 : ℕ) ^ V) ^ 2 < ((2 : ℕ) ^ U) ^ 2 := by omega
    by_contra hc
    have hc' : (2 : ℕ) ^ U ≤ 3 ^ V := not_lt.mp hc
    have hle : ((2 : ℕ) ^ U) ^ 2 ≤ ((3 : ℕ) ^ V) ^ 2 :=
      Nat.pow_le_pow_left hc' 2
    omega
  obtain ⟨D, hD⟩ := Nat.exists_eq_add_of_le (le_of_lt h2Ugt)
  have hD1 : 1 ≤ D := by omega
  have hD7 : D * (2 * (3 : ℕ) ^ V + D) = 7 := by
    have e : ((2 : ℕ) ^ U) ^ 2 - ((3 : ℕ) ^ V) ^ 2 = 7 := by omega
    rw [hD] at e
    have e2' : ((3 : ℕ) ^ V + D) ^ 2 - (3 ^ V) ^ 2
        = D * (2 * 3 ^ V + D) := by
      have hr : ((3 : ℕ) ^ V + D) ^ 2
          = (3 ^ V) ^ 2 + D * (2 * 3 ^ V + D) := by ring
      omega
    rw [e2'] at e
    exact e
  have hDvd7 : D ∣ 7 := ⟨2 * (3 : ℕ) ^ V + D, hD7.symm⟩
  have hD17 : D = 1 ∨ D = 7 := by
    have h7 : Nat.Prime 7 := Nat.prime_seven
    rcases (Nat.dvd_prime h7).mp hDvd7 with h1 | h7eq
    · exact Or.inl h1
    · exact Or.inr h7eq
  have hD1eq : D = 1 := by
    rcases hD17 with h1 | h7eq
    · exact h1
    · exfalso
      rw [h7eq] at hD7
      omega
  have h3V3 : (3 : ℕ) ^ V = 3 := by
    rw [hD1eq] at hD7
    norm_num at hD7
    omega
  have hV1 : V = 1 := pow_eq_base_of_two_le (by norm_num) h3V3
  have h2U4 : (2 : ℕ) ^ U = 4 := by omega
  have hU2 : U = 2 := by
    have h4 : (2 : ℕ) ^ U = 2 ^ 2 := by rw [h2U4]; norm_num
    exact pow_eq_pow_of_two_le (by norm_num) h4
  refine ⟨?_, ?_, hZ3⟩ <;> omega

/-- Third exponential Diophantine lemma: `2 ^ X + 1 = 3 ^ Y + 2 ^ Z` with
    `Y ≥ 2` and `Z ≥ 1` forces `(X, Y, Z) = (4, 2, 3)`. -/
private lemma pillaiC {X Y Z : ℕ} (hY : 2 ≤ Y) (hZ : 1 ≤ Z)
    (h : 2 ^ X + 1 = 3 ^ Y + 2 ^ Z) : X = 4 ∧ Y = 2 ∧ Z = 3 := by
  have h3Y9 : (9 : ℕ) ≤ 3 ^ Y := by
    have hle : (3 : ℕ) ^ 2 ≤ 3 ^ Y := pow_le_pow_right₀ (by norm_num) hY
    norm_num at hle
    exact hle
  have h3Y0 : (3 ^ Y) % 3 = 0 := by
    have hpm := Nat.pow_mod 3 Y 3
    rw [show (3 : ℕ) % 3 = 0 from rfl] at hpm
    rw [zero_pow (by omega : Y ≠ 0)] at hpm
    simpa using hpm
  rcases eq_or_ne Z 1 with rfl | hZne
  · have hX2 : 2 ≤ X := by
      by_contra hc
      have hc' : X < 2 := not_le.mp hc
      have hx1 : X ≤ 1 := by omega
      have hle : (2 : ℕ) ^ X ≤ 2 ^ 1 := pow_le_pow_right₀ (by norm_num) hx1
      norm_num at h
      norm_num at hle
      omega
    have hA : (2 : ℕ) ^ X = 3 ^ Y + 1 := by
      norm_num at h
      omega
    obtain ⟨-, hY1eq⟩ := pillaiA hX2 hA
    omega
  · have hZ2 : 2 ≤ Z := by omega
    rcases Nat.even_or_odd Z with hZe | hZo
    · obtain ⟨W, rfl⟩ := hZe
      have h2Z1 : (2 ^ (W + W)) % 3 = 1 := by
        have h4 : (4 ^ W) % 3 = 1 := by
          have hpm := Nat.pow_mod 4 W 3
          rw [show (4 : ℕ) % 3 = 1 from rfl] at hpm
          simpa using hpm
        have e : (2 : ℕ) ^ (W + W) = 4 ^ W := by
          rw [pow_add, ← mul_pow]
          norm_num
        rw [e]
        exact h4
      have hcon := congrArg (· % 3) h
      rw [Nat.add_mod (2 ^ X) 1 3, Nat.add_mod (3 ^ Y) (2 ^ (W + W)) 3,
        h3Y0, h2Z1] at hcon
      norm_num at hcon
      have hE0 : (2 ^ X) % 3 = 0 := by
        have hElt : (2 ^ X) % 3 < 3 := Nat.mod_lt _ (by norm_num)
        omega
      have hdvd : (3 : ℕ) ∣ 2 ^ X := ⟨2 ^ X / 3, by omega⟩
      have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
      obtain ⟨k, hk⟩ := h32
      omega
    · obtain ⟨W, rfl⟩ := hZo
      have h2Z2 : (2 ^ (2 * W + 1)) % 3 = 2 := odd_pow_two_mod_three ⟨W, rfl⟩
      have hcon3 := congrArg (· % 3) h
      rw [Nat.add_mod (2 ^ X) 1 3, Nat.add_mod (3 ^ Y) (2 ^ (2 * W + 1)) 3,
        h3Y0, h2Z2] at hcon3
      norm_num at hcon3
      have h2X1 : (2 ^ X) % 3 = 1 := by
        have hElt : (2 ^ X) % 3 < 3 := Nat.mod_lt _ (by norm_num)
        omega
      have hXeven : Even X := by
        by_contra hc
        rw [Nat.not_even_iff_odd] at hc
        have h2 := odd_pow_two_mod_three hc
        omega
      have hX1 : 1 ≤ X := by
        rcases Nat.eq_zero_or_pos X with rfl | hpos
        · norm_num at h
          have hle : (9 : ℕ) ≤ 2 := by
            calc (9 : ℕ) ≤ 3 ^ Y := h3Y9
              _ ≤ 3 ^ Y + 2 ^ (2 * W + 1) := Nat.le_add_right _ _
              _ = 2 := h.symm
          norm_num at hle
        · exact hpos
      obtain ⟨U, rfl⟩ := hXeven
      have h2X0 : (2 ^ (U + U)) % 4 = 0 := by
        have hX2 : 2 ≤ U + U := by omega
        obtain ⟨v, hv⟩ := Nat.exists_eq_add_of_le hX2
        rw [hv, pow_add, Nat.mul_mod, show (2 : ℕ) ^ 2 % 4 = 0 from rfl]
        simp
      have h2Z0 : (2 ^ (2 * W + 1)) % 4 = 0 := by
        obtain ⟨v, hv⟩ := Nat.exists_eq_add_of_le hZ2
        rw [hv, pow_add, Nat.mul_mod, show (2 : ℕ) ^ 2 % 4 = 0 from rfl]
        simp
      have hcon4 := congrArg (· % 4) h
      rw [Nat.add_mod (2 ^ (U + U)) 1 4, Nat.add_mod (3 ^ Y) (2 ^ (2 * W + 1)) 4,
        h2X0, h2Z0] at hcon4
      norm_num at hcon4
      have h3Y1 : (3 ^ Y) % 4 = 1 := by omega
      have hYeven : Even Y := by
        by_contra hc
        rw [Nat.not_even_iff_odd] at hc
        have h3 := odd_pow_three_mod_four hc
        omega
      obtain ⟨V, rfl⟩ := hYeven
      have h2X4 : (2 : ℕ) ^ (U + U) = 4 ^ U := by
        rw [pow_add, ← mul_pow]
        norm_num
      have h3Y9v : (3 : ℕ) ^ (V + V) = 9 ^ V := by
        rw [pow_add, ← mul_pow]
        norm_num
      have h2Z24 : (2 : ℕ) ^ (2 * W + 1) = 2 * 4 ^ W := by
        have h1 : (2 : ℕ) ^ (2 * W) = 4 ^ W := by
          rw [pow_mul]
          norm_num
        calc (2 : ℕ) ^ (2 * W + 1) = 2 ^ (2 * W) * 2 ^ 1 := pow_add 2 (2 * W) 1
          _ = 2 * 4 ^ W := by rw [h1]; ring
      have hcon5 := congrArg (· % 5) h
      rw [Nat.add_mod (2 ^ (U + U)) 1 5,
        Nat.add_mod (3 ^ (V + V)) (2 ^ (2 * W + 1)) 5, h2X4, h3Y9v, h2Z24,
        Nat.mul_mod] at hcon5
      have hU14 : (4 ^ U) % 5 = 1 ∨ (4 ^ U) % 5 = 4 := by
        rcases Nat.even_or_odd U with hUe | hUo
        · exact Or.inl (pow_four_mod_five_even hUe)
        · exact Or.inr (pow_four_mod_five_odd hUo)
      have hV14 : (9 ^ V) % 5 = 1 ∨ (9 ^ V) % 5 = 4 := by
        rcases Nat.even_or_odd V with hVe | hVo
        · exact Or.inl (pow_nine_mod_five_even hVe)
        · exact Or.inr (pow_nine_mod_five_odd hVo)
      have hW14 : (4 ^ W) % 5 = 1 ∨ (4 ^ W) % 5 = 4 := by
        rcases Nat.even_or_odd W with hWe | hWo
        · exact Or.inl (pow_four_mod_five_even hWe)
        · exact Or.inr (pow_four_mod_five_odd hWo)
      have hUeven : (4 ^ U) % 5 = 1 → Even U := by
        intro h1
        by_contra hc
        rw [Nat.not_even_iff_odd] at hc
        have h4 := pow_four_mod_five_odd hc
        omega
      have hVodd : (9 ^ V) % 5 = 4 → Odd V := by
        intro h4
        by_contra hc
        rw [Nat.not_odd_iff_even] at hc
        have h1 := pow_nine_mod_five_even hc
        omega
      have hWodd : (4 ^ W) % 5 = 4 → Odd W := by
        intro h4
        by_contra hc
        rw [Nat.not_odd_iff_even] at hc
        have h1 := pow_four_mod_five_even hc
        omega
      have hpar : Even U ∧ Odd V ∧ Odd W := by
        rcases hU14 with hU | hU <;> rcases hV14 with hV | hV <;>
          rcases hW14 with hW | hW
        all_goals
          rw [hU, hV, hW] at hcon5
          norm_num at hcon5
        exact ⟨hUeven hU, hVodd hV, hWodd hW⟩
      obtain ⟨-, hVod, -⟩ := hpar
      exact pillaiC_finish hVod h

/-- **Two Pillai equations in powers of two and three.** For natural numbers $a$ and $b$, the
integer equation $2^a - 3^b = -1$ holds if and only if $(a, b) = (1, 1)$ or $(a, b) = (3, 2)$.
For natural numbers $a$, $b$ and $c$, the integer equation $2^a - 3^b = 2^c - 1$ holds if and
only if $(a, b, c) = (2, 1, 1)$, or $(a, b, c) = (4, 2, 3)$, or $b = 0$ and $c = a$.

Source: Paulo J. Almeida and Gabriel Cardoso, *An Extension of the
Euclid–Euler Theorem to Certain α-Perfect Numbers*, Journal of Integer
Sequences 25 (2022), Article 22.8.4, Lemma `pillai`, lines 176–184,
<https://cs.uwaterloo.ca/journals/JIS/VOL25/Almeida/almeida9.tex>. -/
public theorem pillai_equations_two_pow_three_pow :
    (∀ a b : ℕ, (2 : ℤ) ^ a - 3 ^ b = -1 ↔
        (a = 1 ∧ b = 1) ∨ (a = 3 ∧ b = 2)) ∧
      (∀ a b c : ℕ, (2 : ℤ) ^ a - 3 ^ b = 2 ^ c - 1 ↔
        (a = 2 ∧ b = 1 ∧ c = 1) ∨ (a = 4 ∧ b = 2 ∧ c = 3) ∨
        (b = 0 ∧ c = a)) := by
  constructor
  · intro a b
    constructor
    · intro h
      have hz : (2 : ℤ) ^ a + 1 = 3 ^ b := by omega
      have hn : (2 : ℕ) ^ a + 1 = 3 ^ b := by exact_mod_cast hz
      by_cases hb2 : 2 ≤ b
      · exact Or.inr (pillaiB hb2 hn.symm)
      · have hb01 : b = 0 ∨ b = 1 := by omega
        rcases hb01 with rfl | rfl
        · norm_num at hn
        · norm_num at hn
          have haPow : (2 : ℕ) ^ a = 2 := by omega
          exact Or.inl ⟨pow_eq_base_of_two_le (by norm_num) haPow, rfl⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num
  · intro a b c
    constructor
    · intro h
      have hz : (2 : ℤ) ^ a + 1 = 3 ^ b + 2 ^ c := by omega
      have hn : (2 : ℕ) ^ a + 1 = 3 ^ b + 2 ^ c := by exact_mod_cast hz
      rcases Nat.eq_zero_or_pos b with rfl | hbpos
      · norm_num at hn
        have hac : a = c := pow_eq_pow_of_two_le (b := 2) (by norm_num) (by omega)
        exact Or.inr (Or.inr ⟨rfl, hac.symm⟩)
      · rcases Nat.eq_zero_or_pos c with rfl | hcpos
        · norm_num at hn
          have hpow : (2 : ℕ) ^ a = 3 ^ b := by omega
          have ha1 : 1 ≤ a := by
            by_contra ha
            have ha0 : a = 0 := by omega
            have h3 : (3 : ℕ) ≤ 3 ^ b := by
              calc
                (3 : ℕ) = 3 ^ 1 := by norm_num
                _ ≤ 3 ^ b := pow_le_pow_right₀ (by norm_num) hbpos
            rw [ha0] at hpow
            norm_num at hpow
            omega
          have heven := even_two_pow ha1
          have hodd : Odd ((3 : ℕ) ^ b) := Odd.pow ⟨1, rfl⟩
          rw [hpow] at heven
          obtain ⟨u, hu⟩ := heven
          obtain ⟨v, hv⟩ := hodd
          omega
        · by_cases hb2 : 2 ≤ b
          · exact Or.inr (Or.inl (pillaiC hb2 hcpos hn))
          · have hb1 : b = 1 := by omega
            subst b
            norm_num at hn
            have heq : (2 : ℕ) ^ a = 2 ^ c + 2 := by omega
            have hca : c < a := by
              by_contra hca
              have hac : a ≤ c := Nat.le_of_not_gt hca
              have hle : (2 : ℕ) ^ a ≤ 2 ^ c :=
                pow_le_pow_right₀ (by norm_num) hac
              omega
            have hc1 : c = 1 := by
              by_contra hc1
              have hc2 : 2 ≤ c := by omega
              have ha2 : 2 ≤ a := by omega
              obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le ha2
              obtain ⟨v, hv⟩ := Nat.exists_eq_add_of_le hc2
              have hma : ((2 : ℕ) ^ a) % 4 = 0 := by
                rw [hu, pow_add, Nat.mul_mod]
                norm_num
              have hmc : ((2 : ℕ) ^ c) % 4 = 0 := by
                rw [hv, pow_add, Nat.mul_mod]
                norm_num
              have hmod := congrArg (· % 4) heq
              rw [Nat.add_mod, hma, hmc] at hmod
              norm_num at hmod
            subst c
            norm_num at heq
            have haPow : (2 : ℕ) ^ a = 2 ^ 2 := by
              norm_num
              exact heq
            exact Or.inl ⟨pow_eq_pow_of_two_le (by norm_num) haPow, rfl, rfl⟩
    · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · norm_num
      · norm_num
      · simp

/-- Two and three are coprime. -/
private lemma coprime_two_three : Nat.Coprime 2 3 :=
  (Nat.coprime_primes Nat.prime_two Nat.prime_three).mpr (by norm_num)

/-- The main equation `σ(m) * den = m * num`, from multiplicativity of `σ`
    and the prime-power values. -/
private lemma main_equation {N a b m : ℕ}
    (hperfect : (ArithmeticFunction.sigma 1) N = 3 * N)
    (hform : N = 2 ^ a * 3 ^ b * m)
    (hcop : Nat.Coprime (2 ^ a * 3 ^ b) m)
    (hcop23 : Nat.Coprime (2 ^ a) (3 ^ b)) :
    (ArithmeticFunction.sigma 1) m * ((2 ^ (a + 1) - 1) * (3 ^ (b + 1) - 1))
      = m * (2 ^ (a + 1) * 3 ^ (b + 1)) := by
  have hmult : (ArithmeticFunction.sigma 1).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_sigma
  have e1 := hmult.map_mul_of_coprime hcop
  have e2 := hmult.map_mul_of_coprime hcop23
  rw [hform, e1, e2, sigma_prime_pow_two a] at hperfect
  have hC := two_mul_sigma_prime_pow_three b
  have eA : (2 : ℕ) ^ (a + 1) = 2 * 2 ^ a := by
    rw [pow_succ]
    ring
  have eB : (3 : ℕ) ^ (b + 1) = 3 * 3 ^ b := by
    rw [pow_succ]
    ring
  have goal2 : (ArithmeticFunction.sigma 1) m
      * ((2 ^ (a + 1) - 1) * (2 * (ArithmeticFunction.sigma 1) (3 ^ b)))
      = m * (2 ^ (a + 1) * 3 ^ (b + 1)) := by
    have e : (ArithmeticFunction.sigma 1) m
        * ((2 ^ (a + 1) - 1) * (2 * (ArithmeticFunction.sigma 1) (3 ^ b)))
        = 2 * (((2 ^ (a + 1) - 1) * (ArithmeticFunction.sigma 1) (3 ^ b))
          * (ArithmeticFunction.sigma 1) m) := by ring
    rw [e, hperfect, eA, eB]
    ring
  rw [← hC]
  exact goal2

/-- Reduction of the main equation: with `d = gcd num den = 2 ^ s * 3 ^ t`,
    `m = (P * Q) * k` and `S = N'' * k`, plus valuation bounds and the
    explicit quotient formula for `N''`. -/
private lemma gcd_reduction {a b m S : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hm0 : m ≠ 0)
    (hS : S * ((2 ^ (a + 1) - 1) * (3 ^ (b + 1) - 1))
      = m * (2 ^ (a + 1) * 3 ^ (b + 1))) :
    ∃ s t P Q k N'' d,
      1 ≤ s ∧ s ≤ a + 1 ∧ t ≤ b + 1 ∧
      d = Nat.gcd (2 ^ (a + 1) * 3 ^ (b + 1))
        ((2 ^ (a + 1) - 1) * (3 ^ (b + 1) - 1)) ∧
      d = 2 ^ s * 3 ^ t ∧ s = d.factorization 2 ∧ t = d.factorization 3 ∧
      (2 ^ (a + 1) - 1 = 3 ^ t * P) ∧ (3 ^ (b + 1) - 1 = 2 ^ s * Q) ∧
      1 ≤ P ∧ 1 ≤ Q ∧ m = (P * Q) * k ∧ S = N'' * k ∧ 1 ≤ k ∧
      N'' = 2 ^ (a + 1 - s) * 3 ^ (b + 1 - t) ∧
      N'' * (2 ^ s * 3 ^ t) = 2 ^ (a + 1) * 3 ^ (b + 1) := by
  set num : ℕ := 2 ^ (a + 1) * 3 ^ (b + 1) with hnum
  set den : ℕ := (2 ^ (a + 1) - 1) * (3 ^ (b + 1) - 1) with hden
  set d : ℕ := Nat.gcd num den with hd
  set s : ℕ := d.factorization 2 with hs
  set t : ℕ := d.factorization 3 with ht
  have hnumpos : 0 < num := by
    rw [hnum]
    positivity
  have hApos : 0 < 2 ^ (a + 1) - 1 := by
    have h2 : (2 : ℕ) ^ 2 ≤ 2 ^ (a + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega : 2 ≤ a + 1)
    norm_num at h2
    omega
  have hCpos : 0 < 3 ^ (b + 1) - 1 := by
    have h2 : (3 : ℕ) ^ 2 ≤ 3 ^ (b + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega : 2 ≤ b + 1)
    norm_num at h2
    omega
  have hdenpos : 0 < den := by
    rw [hden]
    exact mul_pos hApos hCpos
  have hdvdnum : d ∣ num := Nat.gcd_dvd_left num den
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvdnum hnumpos
  have hprimes : d.primeFactors ⊆ ({2, 3} : Finset ℕ) := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ d := (Nat.mem_primeFactors.mp hp).2.1
    have hpnum : p ∣ num := dvd_trans hpdvd hdvdnum
    rw [hnum] at hpnum
    have h2or3 : p ∣ 2 ^ (a + 1) ∨ p ∣ 3 ^ (b + 1) :=
      (hprime.dvd_mul).mp hpnum
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases h2or3 with h2 | h3
    · left
      have h2' : p ∣ 2 := hprime.dvd_of_dvd_pow h2
      rcases (Nat.dvd_prime Nat.prime_two).mp h2' with h1 | h2eq
      · exact absurd h1 hprime.ne_one
      · exact h2eq
    · right
      have h3' : p ∣ 3 := hprime.dvd_of_dvd_pow h3
      rcases (Nat.dvd_prime Nat.prime_three).mp h3' with h1 | h3eq
      · exact absurd h1 hprime.ne_one
      · exact h3eq
  have hdecomp : d = 2 ^ s * 3 ^ t := by
    have h0 : d ≠ 0 := ne_of_gt hdpos
    have hprod := Nat.prod_factorization_pow_eq_self h0
    have hsup : d.factorization.support ⊆ ({2, 3} : Finset ℕ) := by
      rw [Nat.support_factorization d]
      exact hprimes
    have hmid : d.factorization.prod (fun x1 x2 => x1 ^ x2)
        = ∏ x ∈ ({2, 3} : Finset ℕ), x ^ (d.factorization x) :=
      Finsupp.prod_of_support_subset d.factorization hsup _
        (fun i _ => pow_zero i)
    have h23 : (∏ x ∈ ({2, 3} : Finset ℕ), x ^ (d.factorization x))
        = 2 ^ s * 3 ^ t := by
      rw [Finset.prod_insert (by simp : (2 : ℕ) ∉ ({3} : Finset ℕ)),
        Finset.prod_singleton]
    exact hprod.symm.trans (hmid.trans h23)
  have h2num : (2 : ℕ) ∣ num := by
    rw [hnum]
    exact dvd_mul_of_dvd_left ⟨2 ^ a, by rw [pow_succ]; ring⟩ _
  have h2den : (2 : ℕ) ∣ den := by
    rw [hden]
    apply dvd_mul_of_dvd_right
    have hodd : Odd ((3 : ℕ) ^ (b + 1)) := Odd.pow ⟨1, rfl⟩
    have heven : Even ((3 : ℕ) ^ (b + 1) - 1) := Nat.Odd.sub_odd hodd ⟨0, rfl⟩
    exact even_iff_two_dvd.mp heven
  have h2d : (2 : ℕ) ∣ d := Nat.dvd_gcd h2num h2den
  have hs1 : 1 ≤ s := by
    rw [hdecomp] at h2d
    have h3odd : Odd ((3 : ℕ) ^ t) := Odd.pow ⟨1, rfl⟩
    have h2ns3 : ¬ (2 : ℕ) ∣ 3 ^ t := by
      intro hcon
      have heven : Even ((3 : ℕ) ^ t) := even_iff_two_dvd.mpr hcon
      obtain ⟨a, ha⟩ := h3odd
      obtain ⟨b, hb⟩ := heven
      omega
    have h2s : (2 : ℕ) ∣ 2 ^ s := by
      rcases (Nat.prime_two.dvd_mul).mp h2d with h | h
      · exact h
      · exact absurd h h2ns3
    by_contra hc
    have hs0 : s = 0 := by omega
    rw [hs0] at h2s
    norm_num at h2s
  have h3td : (3 : ℕ) ^ t ∣ d := by
    rw [hdecomp]
    exact dvd_mul_left _ _
  have h3tden : (3 : ℕ) ^ t ∣ den := dvd_trans h3td (Nat.gcd_dvd_right num den)
  have hndvd3 : ¬ (3 : ℕ) ∣ 3 ^ (b + 1) - 1 := by
    intro hcon
    have h3pow : (3 : ℕ) ∣ 3 ^ (b + 1) := ⟨3 ^ b, by rw [pow_succ]; ring⟩
    have hsub := Nat.dvd_sub h3pow hcon
    have heq : (3 : ℕ) ^ (b + 1) - (3 ^ (b + 1) - 1) = 1 := by
      have h1 : 1 ≤ (3 : ℕ) ^ (b + 1) := one_le_pow₀ (by norm_num)
      omega
    rw [heq] at hsub
    obtain ⟨k, hk⟩ := hsub
    omega
  have hcop3t : Nat.Coprime ((3 : ℕ) ^ t) (3 ^ (b + 1) - 1) :=
    Nat.Coprime.pow_left t ((Nat.prime_three.coprime_iff_not_dvd).mpr hndvd3)
  have h3tA : (3 : ℕ) ^ t ∣ 2 ^ (a + 1) - 1 := by
    rw [hden] at h3tden
    exact Nat.Coprime.dvd_of_dvd_mul_right hcop3t h3tden
  have h2sd : (2 : ℕ) ^ s ∣ d := by
    rw [hdecomp]
    exact dvd_mul_right _ _
  have h2sden : (2 : ℕ) ^ s ∣ den := dvd_trans h2sd (Nat.gcd_dvd_right num den)
  have hndvd2 : ¬ (2 : ℕ) ∣ 2 ^ (a + 1) - 1 := by
    have heven : Even ((2 : ℕ) ^ (a + 1)) := even_two_pow (by omega : 1 ≤ a + 1)
    have hodd : Odd ((2 : ℕ) ^ (a + 1) - 1) :=
      Nat.Even.sub_odd (one_le_pow₀ (by norm_num)) heven ⟨0, rfl⟩
    intro hcon
    have heven2 : Even ((2 : ℕ) ^ (a + 1) - 1) := even_iff_two_dvd.mpr hcon
    obtain ⟨a, ha⟩ := hodd
    obtain ⟨b, hb⟩ := heven2
    omega
  have hcop2s : Nat.Coprime ((2 : ℕ) ^ s) (2 ^ (a + 1) - 1) :=
    Nat.Coprime.pow_left s ((Nat.prime_two.coprime_iff_not_dvd).mpr hndvd2)
  have h2sC : (2 : ℕ) ^ s ∣ 3 ^ (b + 1) - 1 := by
    rw [hden] at h2sden
    exact Nat.Coprime.dvd_of_dvd_mul_left hcop2s h2sden
  have hs_le : s ≤ a + 1 := by
    have h2snum : (2 : ℕ) ^ s ∣ 2 ^ (a + 1) * 3 ^ (b + 1) := by
      have h := dvd_trans h2sd hdvdnum
      rwa [hnum] at h
    have hcop23 : Nat.Coprime ((2 : ℕ) ^ s) (3 ^ (b + 1)) :=
      Nat.Coprime.pow_right (b + 1) (Nat.Coprime.pow_left s coprime_two_three)
    have h2s2a : (2 : ℕ) ^ s ∣ 2 ^ (a + 1) :=
      Nat.Coprime.dvd_of_dvd_mul_right hcop23 h2snum
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h2s2a
  have ht_le : t ≤ b + 1 := by
    have h3tnum : (3 : ℕ) ^ t ∣ 2 ^ (a + 1) * 3 ^ (b + 1) := by
      have h := dvd_trans h3td hdvdnum
      rwa [hnum] at h
    have hcop32 : Nat.Coprime ((3 : ℕ) ^ t) (2 ^ (a + 1)) :=
      Nat.Coprime.pow_right (a + 1)
        (Nat.Coprime.pow_left t coprime_two_three.symm)
    have h3t3b : (3 : ℕ) ^ t ∣ 3 ^ (b + 1) :=
      Nat.Coprime.dvd_of_dvd_mul_left hcop32 h3tnum
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).mp h3t3b
  obtain ⟨P, hP⟩ := h3tA
  obtain ⟨Q, hQ⟩ := h2sC
  have hP1 : 1 ≤ P := by
    by_contra hc
    have hP0 : P = 0 := by omega
    rw [hP0] at hP
    simp at hP
    omega
  have hQ1 : 1 ≤ Q := by
    by_contra hc
    have hQ0 : Q = 0 := by omega
    rw [hQ0] at hQ
    simp at hQ
    omega
  have hdenPQ : den = d * (P * Q) := by
    rw [hden, hdecomp, hP, hQ]
    ring
  obtain ⟨N'', hN''⟩ := hdvdnum
  have hred : S * (P * Q) = m * N'' := by
    have hS' := hS
    rw [hdenPQ, hN''] at hS'
    have e1 : S * (d * (P * Q)) = d * (S * (P * Q)) := by ring
    have e2 : m * (d * N'') = d * (m * N'') := by ring
    rw [e1, e2] at hS'
    exact Nat.mul_left_cancel hdpos hS'
  have hgcdpos : 0 < Nat.gcd num den := hdpos
  have hNdiv : num / d = N'' := by
    have hN''' : num = N'' * d := by
      rw [hN'']
      ring
    exact Nat.div_eq_of_eq_mul_left hdpos hN'''
  have hPQdiv : den / d = P * Q := by
    have hden' : den = (P * Q) * d := by
      rw [hdenPQ]
      ring
    exact Nat.div_eq_of_eq_mul_left hdpos hden'
  have hcopdiv : Nat.Coprime N'' (P * Q) := by
    have h0 : Nat.Coprime (num / d) (den / d) :=
      Nat.coprime_div_gcd_div_gcd hgcdpos
    rw [hNdiv, hPQdiv] at h0
    exact h0
  have hDvd : (P * Q) ∣ m := by
    have h1 : (P * Q) ∣ m * N'' := by
      rw [← hred]
      exact dvd_mul_left _ _
    exact Nat.Coprime.dvd_of_dvd_mul_right hcopdiv.symm h1
  obtain ⟨k, hk⟩ := hDvd
  have hSk : S = N'' * k := by
    have h2 : S * (P * Q) = (N'' * k) * (P * Q) := by
      rw [hred, hk]
      ring
    exact Nat.mul_right_cancel (mul_pos (by omega) (by omega)) h2
  have hk1 : 1 ≤ k := by
    by_contra hc
    have hk0 : k = 0 := by omega
    have hm : m = 0 :=
      calc m = (P * Q) * k := hk
        _ = 0 := by rw [hk0, mul_zero]
    exact hm0 hm
  have hNd : N'' * (2 ^ s * 3 ^ t) = num := by
    rw [hdecomp.symm, mul_comm N'' d, ← hN'']
  have hSTpos : 0 < 2 ^ s * 3 ^ t :=
    mul_pos (pow_pos (by norm_num) _) (pow_pos (by norm_num) _)
  have hpow2_split : (2 : ℕ) ^ (a + 1) = 2 ^ s * 2 ^ (a + 1 - s) := by
    have h := pow_add 2 s (a + 1 - s)
    rw [show s + (a + 1 - s) = a + 1 from by omega] at h
    exact h
  have hpow3_split : (3 : ℕ) ^ (b + 1) = 3 ^ t * 3 ^ (b + 1 - t) := by
    have h := pow_add 3 t (b + 1 - t)
    rw [show t + (b + 1 - t) = b + 1 from by omega] at h
    exact h
  have hNformula : N'' = 2 ^ (a + 1 - s) * 3 ^ (b + 1 - t) := by
    have h1 : N'' * (2 ^ s * 3 ^ t)
        = (2 ^ (a + 1 - s) * 3 ^ (b + 1 - t)) * (2 ^ s * 3 ^ t) := by
      rw [hNd, hnum, hpow2_split, hpow3_split]
      ring
    exact Nat.mul_right_cancel hSTpos h1
  exact ⟨s, t, P, Q, k, N'', d, hs1, hs_le, ht_le, hd, hdecomp, hs, ht,
    hP, hQ, hP1, hQ1, hk, hSk, hk1, hNformula, hNd⟩

/-- The divisor sum `σ(m)` dominates the sum over any finset of divisors. -/
private lemma sigma_ge_sum_divisors {m : ℕ} (D : Finset ℕ)
    (hD : ∀ d ∈ D, d ∈ m.divisors) :
    ∑ d ∈ D, d ≤ (ArithmeticFunction.sigma 1) m := by
  rw [ArithmeticFunction.sigma_one_apply]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun d hd => hD d hd)
    (fun d _ _ => Nat.zero_le d)

/-- The divisor sum dominates the sum of three distinct divisors. -/
private lemma sigma_ge_three {m d1 d2 d3 : ℕ} (h1 : d1 ∈ m.divisors)
    (h2 : d2 ∈ m.divisors) (h3 : d3 ∈ m.divisors)
    (h12 : d1 ≠ d2) (h13 : d1 ≠ d3) (h23 : d2 ≠ d3) :
    d1 + d2 + d3 ≤ (ArithmeticFunction.sigma 1) m := by
  have h := sigma_ge_sum_divisors (D := ({d1, d2, d3} : Finset ℕ)) (by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3)
  rw [Finset.sum_insert (show d1 ∉ ({d2, d3} : Finset ℕ) from by simp [h12, h13]),
    Finset.sum_insert (show d2 ∉ ({d3} : Finset ℕ) from by simp [h23]),
    Finset.sum_singleton] at h
  omega

/-- The divisor sum dominates the sum of four distinct divisors. -/
private lemma sigma_ge_four {m d1 d2 d3 d4 : ℕ} (h1 : d1 ∈ m.divisors)
    (h2 : d2 ∈ m.divisors) (h3 : d3 ∈ m.divisors) (h4 : d4 ∈ m.divisors)
    (h12 : d1 ≠ d2) (h13 : d1 ≠ d3) (h14 : d1 ≠ d4)
    (h23 : d2 ≠ d3) (h24 : d2 ≠ d4) (h34 : d3 ≠ d4) :
    d1 + d2 + d3 + d4 ≤ (ArithmeticFunction.sigma 1) m := by
  have h := sigma_ge_sum_divisors (D := ({d1, d2, d3, d4} : Finset ℕ)) (by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4)
  rw [Finset.sum_insert
      (show d1 ∉ ({d2, d3, d4} : Finset ℕ) from by simp [h12, h13, h14]),
    Finset.sum_insert (show d2 ∉ ({d3, d4} : Finset ℕ) from by simp [h23, h24]),
    Finset.sum_insert (show d3 ∉ ({d4} : Finset ℕ) from by simp [h34]),
    Finset.sum_singleton] at h
  omega

/-- Key inequality for the first case: with `X ≥ 2`, `Y ≥ 3`, `P, Q ≤ M`,
    `P * Y + Q * X + 1 < (M + 1) * X * Y`. -/
private lemma caseA_ineq {P Q M X Y : ℕ} (hPM : P ≤ M) (hQM : Q ≤ M)
    (hX : 2 ≤ X) (hY : 3 ≤ Y) :
    P * Y + Q * X + 1 < (M + 1) * X * Y := by
  obtain ⟨u, rfl, hu⟩ : ∃ u, X = u + 1 ∧ 1 ≤ u := ⟨X - 1, by omega, by omega⟩
  obtain ⟨v, rfl, hv⟩ : ∃ v, Y = v + 1 ∧ 2 ≤ v := ⟨Y - 1, by omega, by omega⟩
  have hle : P * (v + 1) + Q * (u + 1) + 1
      ≤ M * (v + 1) + M * (u + 1) + 1 := by
    have h1 : P * (v + 1) ≤ M * (v + 1) := Nat.mul_le_mul_right _ hPM
    have h2 : Q * (u + 1) ≤ M * (u + 1) := Nat.mul_le_mul_right _ hQM
    omega
  have huv1 : 1 ≤ u * v := by
    have h := Nat.mul_le_mul hu (show 1 ≤ v by omega)
    simpa using h
  have hle_inner : u + v + 2 ≤ u * v + u + v + 1 := by omega
  have hge : M * (u + v + 2) ≤ M * (u * v + u + v + 1) :=
    Nat.mul_le_mul le_rfl hle_inner
  have hgt : 1 < u * v + u + v + 1 := by omega
  have hfin : M * (u + v + 2) + 1
      < M * (u * v + u + v + 1) + (u * v + u + v + 1) :=
    add_lt_add_of_le_of_lt hge hgt
  have e1 : (M + 1) * (u + 1) * (v + 1)
      = M * (u * v + u + v + 1) + (u * v + u + v + 1) := by ring
  have e2 : M * (v + 1) + M * (u + 1) = M * (u + v + 2) := by ring
  calc P * (v + 1) + Q * (u + 1) + 1 ≤ M * (v + 1) + M * (u + 1) + 1 := hle
    _ = M * (u + v + 2) + 1 := by rw [e2]
    _ < M * (u * v + u + v + 1) + (u * v + u + v + 1) := hfin
    _ = (M + 1) * (u + 1) * (v + 1) := e1.symm

/-- Key inequality for the second case: `N'' * X = P * Q * X + P + Q * X + 1`
    with `X ≥ 2` forces `N'' < P * Q + P + Q + 1`. -/
private lemma caseB_ineq {P Q N'' X : ℕ} (hX2 : 2 ≤ X)
    (hid : N'' * X = P * Q * X + P + Q * X + 1) :
    N'' < P * Q + P + Q + 1 := by
  obtain ⟨w, hXw, hw⟩ : ∃ w, X = w + 1 ∧ 1 ≤ w := ⟨X - 1, by omega, by omega⟩
  rw [hXw] at hid
  have eB : (P * Q + P + Q + 1) * (w + 1) = N'' * (w + 1) + (P + 1) * w := by
    rw [hid]
    ring
  have hpos : 0 < (P + 1) * w := mul_pos (by omega) (by omega)
  have hlt : N'' * (w + 1) < (P * Q + P + Q + 1) * (w + 1) := by
    rw [eB]
    exact lt_add_of_pos_right _ hpos
  have hltX : N'' * X < (P * Q + P + Q + 1) * X := by
    rw [hXw]
    exact hlt
  exact (Nat.mul_lt_mul_right (by omega)).mp hltX

/-- First case (`t ≥ 1`): the divisor bound forces `P = 1` or `Q = 1`,
    and the first two Diophantine lemmas give `a = 1 ∨ b = 1`. -/
private lemma caseA {a b m s t P Q k N'' : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hm0 : m ≠ 0)
    (hs1 : 1 ≤ s) (ht1 : 1 ≤ t)
    (hPf : 2 ^ (a + 1) - 1 = 3 ^ t * P)
    (hQf : 3 ^ (b + 1) - 1 = 2 ^ s * Q)
    (hP1 : 1 ≤ P) (hQ1 : 1 ≤ Q)
    (hmk : m = (P * Q) * k)
    (hSk : (ArithmeticFunction.sigma 1) m = N'' * k) (hk1 : 1 ≤ k)
    (hNd : N'' * (2 ^ s * 3 ^ t) = 2 ^ (a + 1) * 3 ^ (b + 1)) :
    a = 1 ∨ b = 1 := by
  set M : ℕ := max P Q with hMdef
  have hPM : P ≤ M := le_max_left _ _
  have hQM : Q ≤ M := le_max_right _ _
  have hX : (2 : ℕ) ≤ 2 ^ s := by
    have h := pow_le_pow_right₀ (show (1 : ℕ) ≤ 2 by norm_num) hs1
    rwa [pow_one] at h
  have hY : (3 : ℕ) ≤ 3 ^ t := by
    have h := pow_le_pow_right₀ (show (1 : ℕ) ≤ 3 by norm_num) ht1
    rwa [pow_one] at h
  have h2e : (2 : ℕ) ^ (a + 1) = 3 ^ t * P + 1 := by
    have h1 : 1 ≤ (2 : ℕ) ^ (a + 1) := one_le_pow₀ (by norm_num)
    omega
  have h3e : (3 : ℕ) ^ (b + 1) = 2 ^ s * Q + 1 := by
    have h1 : 1 ≤ (3 : ℕ) ^ (b + 1) := one_le_pow₀ (by norm_num)
    omega
  have hid : N'' * 2 ^ s * 3 ^ t
      = P * Q * 2 ^ s * 3 ^ t + P * 3 ^ t + Q * 2 ^ s + 1 := by
    have h1 : N'' * 2 ^ s * 3 ^ t = 2 ^ (a + 1) * 3 ^ (b + 1) := by
      calc N'' * 2 ^ s * 3 ^ t = N'' * (2 ^ s * 3 ^ t) := by ring
        _ = 2 ^ (a + 1) * 3 ^ (b + 1) := hNd
    rw [h1, h2e, h3e]
    ring
  have hXYpos : 0 < 2 ^ s * 3 ^ t :=
    mul_pos (pow_pos (by norm_num) _) (pow_pos (by norm_num) _)
  have hltXY : N'' * (2 ^ s * 3 ^ t) < (P * Q + M + 1) * (2 ^ s * 3 ^ t) := by
    have h1 : N'' * (2 ^ s * 3 ^ t)
        = (P * Q) * (2 ^ s * 3 ^ t) + (P * 3 ^ t + Q * 2 ^ s + 1) := by
      rw [show N'' * (2 ^ s * 3 ^ t) = N'' * 2 ^ s * 3 ^ t from by ring, hid]
      ring
    have h2 : (P * Q + M + 1) * (2 ^ s * 3 ^ t)
        = (P * Q) * (2 ^ s * 3 ^ t) + (M + 1) * (2 ^ s * 3 ^ t) := by ring
    have hineq : P * 3 ^ t + Q * 2 ^ s + 1 < (M + 1) * (2 ^ s * 3 ^ t) := by
      have h := caseA_ineq hPM hQM hX hY
      rwa [show (M + 1) * 2 ^ s * 3 ^ t = (M + 1) * (2 ^ s * 3 ^ t) from by ring] at h
    rw [h1, h2]
    exact add_lt_add_of_le_of_lt le_rfl hineq
  have hsmaller : N'' < P * Q + M + 1 := (Nat.mul_lt_mul_right hXYpos).mp hltXY
  have hMkdvd : (M * k) ∣ m := by
    rcases le_total P Q with hle | hle
    · have hM : M = Q := by rw [hMdef]; exact max_eq_right hle
      exact ⟨P, by rw [hmk, hM]; ring⟩
    · have hM : M = P := by rw [hMdef]; exact max_eq_left hle
      exact ⟨Q, by rw [hmk, hM]; ring⟩
  rcases eq_or_ne (M * k) m with hMeq | hMne
  · have hMPQ : M = P * Q := by
      have h1 : M * k = (P * Q) * k := by rw [← hmk]; exact hMeq
      exact Nat.mul_right_cancel (by omega) h1
    rcases le_total P Q with hle | hle
    · have hM : M = Q := by rw [hMdef]; exact max_eq_right hle
      have hPQ : P * Q = 1 * Q := by rw [one_mul]; omega
      have hP1eq : P = 1 := Nat.mul_right_cancel (by omega) hPQ
      have hA : (2 : ℕ) ^ (a + 1) = 3 ^ t + 1 := by
        have h1 : 1 ≤ (2 : ℕ) ^ (a + 1) := one_le_pow₀ (by norm_num)
        have hPf' := hPf
        rw [hP1eq, mul_one] at hPf'
        omega
      have hcon := pillaiA (by omega : 2 ≤ a + 1) hA
      omega
    · have hM : M = P := by rw [hMdef]; exact max_eq_left hle
      have hPQ' : P * Q = P * 1 := by rw [mul_one]; omega
      have hQ1eq : Q = 1 := Nat.mul_left_cancel (by omega) hPQ'
      have hB : (3 : ℕ) ^ (b + 1) = 2 ^ s + 1 := by
        have h1 : 1 ≤ (3 : ℕ) ^ (b + 1) := one_le_pow₀ (by norm_num)
        have hQf' := hQf
        rw [hQ1eq, mul_one] at hQf'
        omega
      have hcon := pillaiB (by omega : 2 ≤ b + 1) hB
      omega
  · rcases eq_or_ne M 1 with hM1eq | hM1ne
    · have hP1eq : P = 1 := by omega
      have hA : (2 : ℕ) ^ (a + 1) = 3 ^ t + 1 := by
        have h1 : 1 ≤ (2 : ℕ) ^ (a + 1) := one_le_pow₀ (by norm_num)
        have hPf' := hPf
        rw [hP1eq, mul_one] at hPf'
        omega
      have hcon := pillaiA (by omega : 2 ≤ a + 1) hA
      omega
    · have hmem_m : m ∈ m.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, hm0⟩
      have hmem_Mk : M * k ∈ m.divisors := Nat.mem_divisors.mpr ⟨hMkdvd, hm0⟩
      have hmem_k : k ∈ m.divisors :=
        Nat.mem_divisors.mpr ⟨⟨P * Q, by rw [hmk]; ring⟩, hm0⟩
      have hne1 : m ≠ M * k := fun h => hMne h.symm
      have hne2 : m ≠ k := by
        intro hcon
        have h1 : (P * Q) * k = 1 * k := by rw [← hmk, hcon, one_mul]
        have h2 : P * Q = 1 := Nat.mul_right_cancel (by omega) h1
        have hP1eq : P = 1 := by
          have hle : P ≤ 1 := Nat.le_of_dvd (by norm_num) ⟨Q, h2.symm⟩
          omega
        have hQ1eq : Q = 1 := by
          have hle : Q ≤ 1 :=
            Nat.le_of_dvd (by norm_num) ⟨P, by rw [mul_comm Q P]; exact h2.symm⟩
          omega
        have hM1' : M = 1 := by
          rw [hMdef, hP1eq, hQ1eq]
          exact max_eq_left le_rfl
        exact hM1ne hM1'
      have hne3 : M * k ≠ k := by
        intro hcon
        have h1 : M * k = 1 * k := by rw [one_mul]; exact hcon
        have hM1' : M = 1 := Nat.mul_right_cancel (by omega) h1
        exact hM1ne hM1'
      have hdiv := sigma_ge_three hmem_m hmem_Mk hmem_k hne1 hne2 hne3
      have hlt : (ArithmeticFunction.sigma 1) m < m + M * k + k := by
        have h2 : m + M * k + k = (P * Q + M + 1) * k := by rw [hmk]; ring
        rw [hSk, h2]
        exact mul_lt_mul_of_pos_right hsmaller (by omega)
      omega

/-- Second case (`t = 0`, `P ≠ Q`): four divisors force a contradiction unless
    `Q = 1`, and the second Diophantine lemma gives `b = 1`. -/
private lemma caseB {a b m s t P Q k N'' : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hm0 : m ≠ 0)
    (hs1 : 1 ≤ s) (ht0 : t = 0) (hPQne : P ≠ Q)
    (hPf : 2 ^ (a + 1) - 1 = 3 ^ t * P)
    (hQf : 3 ^ (b + 1) - 1 = 2 ^ s * Q)
    (hP1 : 1 ≤ P) (hQ1 : 1 ≤ Q)
    (hmk : m = (P * Q) * k)
    (hSk : (ArithmeticFunction.sigma 1) m = N'' * k) (hk1 : 1 ≤ k)
    (hNd : N'' * (2 ^ s * 3 ^ t) = 2 ^ (a + 1) * 3 ^ (b + 1)) :
    b = 1 := by
  have hPf0 : 2 ^ (a + 1) - 1 = P := by
    have h := hPf
    rw [ht0] at h
    simp only [pow_zero, one_mul] at h
    exact h
  rcases eq_or_ne (min P Q) 1 with hmin1 | hminne
  · have hPQ1 : P = 1 ∨ Q = 1 := by omega
    rcases hPQ1 with hPeq | hQeq
    · have h4 : (4 : ℕ) ≤ 2 ^ (a + 1) := by
        have h :=
          pow_le_pow_right₀ (show (1 : ℕ) ≤ 2 by norm_num) (show 2 ≤ a + 1 by omega)
        norm_num at h
        exact h
      omega
    · have hB : (3 : ℕ) ^ (b + 1) = 2 ^ s + 1 := by
        have h1 : 1 ≤ (3 : ℕ) ^ (b + 1) := one_le_pow₀ (by norm_num)
        have hQf' := hQf
        rw [hQeq, mul_one] at hQf'
        omega
      have hcon := pillaiB (by omega : 2 ≤ b + 1) hB
      omega
  · have hP2 : 1 < P := by omega
    have hQ2 : 1 < Q := by omega
    have hmem_m : m ∈ m.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, hm0⟩
    have hmem_Pk : P * k ∈ m.divisors :=
      Nat.mem_divisors.mpr ⟨⟨Q, by rw [hmk]; ring⟩, hm0⟩
    have hmem_Qk : Q * k ∈ m.divisors :=
      Nat.mem_divisors.mpr ⟨⟨P, by rw [hmk]; ring⟩, hm0⟩
    have hmem_k : k ∈ m.divisors :=
      Nat.mem_divisors.mpr ⟨⟨P * Q, by rw [hmk]; ring⟩, hm0⟩
    have hne_mPk : m ≠ P * k := by
      intro hcon
      have h1 : (P * Q) * k = P * k := by rw [← hmk]; exact hcon
      have h2 : P * Q = P := Nat.mul_right_cancel (by omega) h1
      have h3 : P * Q = P * 1 := by rw [mul_one]; exact h2
      have hQ1eq : Q = 1 := Nat.mul_left_cancel (by omega) h3
      omega
    have hne_mQk : m ≠ Q * k := by
      intro hcon
      have h1 : (P * Q) * k = Q * k := by rw [← hmk]; exact hcon
      have h2 : P * Q = Q := Nat.mul_right_cancel (by omega) h1
      have h3 : Q * P = Q * 1 := by rw [mul_comm Q P, mul_one]; exact h2
      have hP1eq : P = 1 := Nat.mul_left_cancel (by omega) h3
      omega
    have hne_mk : m ≠ k := by
      intro hcon
      have h1 : (P * Q) * k = 1 * k := by rw [← hmk, hcon, one_mul]
      have h2 : P * Q = 1 := Nat.mul_right_cancel (by omega) h1
      have hP1eq : P = 1 := by
        have hle : P ≤ 1 := Nat.le_of_dvd (by norm_num) ⟨Q, h2.symm⟩
        omega
      omega
    have hne_PkQk : P * k ≠ Q * k := by
      intro hcon
      exact hPQne (Nat.mul_right_cancel (by omega) hcon)
    have hne_Pkk : P * k ≠ k := by
      intro hcon
      have h1 : P * k = 1 * k := by rw [one_mul]; exact hcon
      have hP1eq : P = 1 := Nat.mul_right_cancel (by omega) h1
      omega
    have hne_Qkk : Q * k ≠ k := by
      intro hcon
      have h1 : Q * k = 1 * k := by rw [one_mul]; exact hcon
      have hQ1eq : Q = 1 := Nat.mul_right_cancel (by omega) h1
      omega
    have hdiv :=
      sigma_ge_four hmem_m hmem_Pk hmem_Qk hmem_k
        hne_mPk hne_mQk hne_mk hne_PkQk hne_Pkk hne_Qkk
    have hid : N'' * 2 ^ s = P * Q * 2 ^ s + P + Q * 2 ^ s + 1 := by
      have hNd' : N'' * 2 ^ s = 2 ^ (a + 1) * 3 ^ (b + 1) := by
        have h := hNd
        rw [ht0] at h
        simp only [pow_zero, mul_one] at h
        exact h
      have h2e : (2 : ℕ) ^ (a + 1) = P + 1 := by
        have h1 : 1 ≤ (2 : ℕ) ^ (a + 1) := one_le_pow₀ (by norm_num)
        omega
      have h3e : (3 : ℕ) ^ (b + 1) = 2 ^ s * Q + 1 := by
        have h1 : 1 ≤ (3 : ℕ) ^ (b + 1) := one_le_pow₀ (by norm_num)
        omega
      rw [hNd', h2e, h3e]
      ring
    have hX : (2 : ℕ) ≤ 2 ^ s := by
      have h := pow_le_pow_right₀ (show (1 : ℕ) ≤ 2 by norm_num) hs1
      rwa [pow_one] at h
    have hNlt : N'' < P * Q + P + Q + 1 := caseB_ineq hX hid
    have hlt : (ArithmeticFunction.sigma 1) m < m + P * k + Q * k + k := by
      have h2 : m + P * k + Q * k + k = (P * Q + P + Q + 1) * k := by
        rw [hmk]
        ring
      rw [hSk, h2]
      exact mul_lt_mul_of_pos_right hNlt (by omega)
    omega

/-- Third case (`t = 0`, `P = Q`): the third Diophantine lemma forces
    `a = 0`, contradicting `a ≥ 1`. -/
private lemma caseC {a b s t P Q : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hs1 : 1 ≤ s) (ht0 : t = 0) (hPQeq : P = Q)
    (hPf : 2 ^ (a + 1) - 1 = 3 ^ t * P)
    (hQf : 3 ^ (b + 1) - 1 = 2 ^ s * Q) :
    False := by
  have hPf0 : 2 ^ (a + 1) - 1 = P := by
    have h := hPf
    rw [ht0] at h
    simp only [pow_zero, one_mul] at h
    exact h
  have hQfP : 3 ^ (b + 1) - 1 = 2 ^ s * P := by
    rw [← hPQeq] at hQf
    exact hQf
  have hC : (2 : ℕ) ^ (a + 1 + s) + 1 = 3 ^ (b + 1) + 2 ^ s := by
    have hpa : (2 : ℕ) ^ (a + 1 + s) = 2 ^ (a + 1) * 2 ^ s := pow_add 2 (a + 1) s
    have hA2 : (2 : ℕ) ^ (a + 1) = P + 1 := by
      have h1 : 1 ≤ (2 : ℕ) ^ (a + 1) := one_le_pow₀ (by norm_num)
      omega
    have hB3 : (3 : ℕ) ^ (b + 1) = 2 ^ s * P + 1 := by
      have h1 : 1 ≤ (3 : ℕ) ^ (b + 1) := one_le_pow₀ (by norm_num)
      omega
    rw [hpa, hA2, hB3]
    ring
  have hcon := pillaiC (by omega : 2 ≤ b + 1) hs1 hC
  omega

/-- **Steuerwald's theorem on 3-perfect numbers.** Let $N$, $a$, $b$ and $m$ be natural numbers
with $N = 2^a 3^b m$, $a \ge 1$, $b \ge 1$, and $m$ coprime to $6$. If $\sigma(N) = 3N$, where
$\sigma(N)$ is the sum of the divisors of $N$, then either $a = 1$ and $b \ne 1$, or $a \ne 1$
and $b = 1$.

Source: https://cs.uwaterloo.ca/journals/JIS/VOL25/Almeida/almeida9.tex, lines 210-219,
text SHA cfc728d5cbd8ccc703d9bfda34db0857b0ba43251881d2ba3a73b45503209f75,
file SHA 47d90eedae7bb76cfb0845e93958ce17dff96d5d9a65ca310917738a33a1eea6. -/
public theorem steuerwald_three_perfect_exponents
    (N a b m : ℕ)
    (hperfect : ArithmeticFunction.sigma 1 N = 3 * N)
    (hform : N = 2 ^ a * 3 ^ b * m)
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hcoprime : Nat.Coprime 6 m) :
    (a = 1 ∧ b ≠ 1) ∨ (a ≠ 1 ∧ b = 1) := by
  have hm0 : m ≠ 0 := by
    intro hcon
    subst hcon
    exact absurd ((Nat.coprime_zero_right 6).mp hcoprime) (by norm_num)
  have hcop23 : Nat.Coprime (2 ^ a) (3 ^ b) :=
    Nat.Coprime.pow_right b (Nat.Coprime.pow_left a coprime_two_three)
  have hcop2m : Nat.Coprime (2 ^ a) m :=
    Nat.Coprime.pow_left a
      (hcoprime.coprime_dvd_left (show (2 : ℕ) ∣ 6 by norm_num))
  have hcop3m : Nat.Coprime (3 ^ b) m :=
    Nat.Coprime.pow_left b
      (hcoprime.coprime_dvd_left (show (3 : ℕ) ∣ 6 by norm_num))
  have hcop : Nat.Coprime (2 ^ a * 3 ^ b) m :=
    Nat.Coprime.mul_left hcop2m hcop3m
  have hme := main_equation hperfect hform hcop hcop23
  obtain ⟨s, t, P, Q, k, N'', -, hs1, -, -, -, -, -, -,
    hPf, hQf, hP1, hQ1, hmk, hSk, hk1, -, hNd⟩ :=
    gcd_reduction ha hb hm0 hme
  have hstep3 : a = 1 ∨ b = 1 := by
    rcases eq_or_ne t 0 with ht0 | htne
    · rcases eq_or_ne P Q with hPQeq | hPQne
      · exact False.elim (caseC ha hb hs1 ht0 hPQeq hPf hQf)
      · exact Or.inr
          (caseB ha hb hm0 hs1 ht0 hPQne hPf hQf hP1 hQ1 hmk hSk hk1 hNd)
    · have ht1 : 1 ≤ t := Nat.pos_of_ne_zero htne
      exact caseA ha hb hm0 hs1 ht1 hPf hQf hP1 hQ1 hmk hSk hk1 hNd
  have hstep4 : ¬(a = 1 ∧ b = 1) := by
    rintro ⟨ha1, hb1⟩
    have h2S3m : 2 * (ArithmeticFunction.sigma 1) m = 3 * m := by
      have h := hme
      rw [ha1, hb1] at h
      norm_num at h
      omega
    have h2nm : ¬ (2 : ℕ) ∣ m := by
      intro h2m
      have hdvd1 : (2 : ℕ) ∣ 1 := by
        have h := Nat.dvd_gcd (show (2 : ℕ) ∣ 6 by norm_num) h2m
        rwa [show Nat.gcd 6 m = 1 from hcoprime] at h
      omega
    have hodd : Odd m := by
      rcases Nat.even_or_odd m with he | ho
      · exfalso
        exact h2nm (even_iff_two_dvd.mp he)
      · exact ho
    have heven : Even (2 * (ArithmeticFunction.sigma 1) m) :=
      even_iff_two_dvd.mpr ⟨(ArithmeticFunction.sigma 1) m, rfl⟩
    have hodd' : Odd (3 * m) := Odd.mul ⟨1, rfl⟩ hodd
    rw [h2S3m] at heven
    obtain ⟨x, hx⟩ := heven
    obtain ⟨y, hy⟩ := hodd'
    omega
  rcases hstep3 with ha1 | hb1
  · exact Or.inl ⟨ha1, fun hb1 => hstep4 ⟨ha1, hb1⟩⟩
  · exact Or.inr ⟨fun ha1 => hstep4 ⟨ha1, hb1⟩, hb1⟩

end

end MetaMathlibExt
