/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryDivisorParity
import MathlibExt.NumberTheory.ArithmeticFunction.UnitaryConvolution
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.PrimeFin

/-!
# Biunitary triperfect numbers divisible by `27`

Powers of two dividing the biunitary divisor sum of an odd number: for every odd natural number
`n`, `2 ^ ω(n)` divides `σ**(n)`, where `ω(n)` is the number of distinct prime factors of `n`
and `σ**(n)` is the biunitary divisor sum. The biunitary divisor sum is multiplicative, and its
value at an odd prime power is even.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 2 (`jis-2025-25.4.5-lem-2`).
-/

namespace MetaMathlibExt

open Finset

private theorem ne_zero_of_dvd_ne_zero {d m : ℕ} (hd : d ∣ m) (hm : m ≠ 0) : d ≠ 0 := by
  rintro rfl
  obtain ⟨k, hk⟩ := hd
  exact hm (by simpa using hk)

private theorem div_ne_zero_of_dvd {d m : ℕ} (hd : d ∣ m) (hm : m ≠ 0) : m / d ≠ 0 := by
  intro h
  apply hm
  rw [← Nat.div_mul_cancel hd, h, zero_mul]

private theorem gcd_mul_gcd_eq_of_dvd_mul {d m n : ℕ} (hmn : m.Coprime n)
    (hd : d ∣ m * n) : d.gcd m * d.gcd n = d := by
  rw [← Nat.Coprime.gcd_mul d hmn, Nat.gcd_eq_left hd]

private theorem gcdUnitary_eq_one_iff {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    gcdUnitary a b = 1 ↔ ∀ u ∈ a.unitaryDivisors ∩ b.unitaryDivisors, u = 1 := by
  constructor
  · intro h u hu
    obtain ⟨hua, hub⟩ := mem_inter.mp hu
    have hle := le_gcdUnitary hua hub
    rw [h] at hle
    have hu0 : u ≠ 0 :=
      ne_zero_of_dvd_ne_zero (Nat.dvd_of_mem_unitaryDivisors hua) ha
    omega
  · intro h
    have h1mem : 1 ∈ a.unitaryDivisors ∩ b.unitaryDivisors :=
      mem_inter.mpr ⟨by simp [ha], by simp [hb]⟩
    simp only [gcdUnitary]
    apply le_antisymm
    · apply Finset.sup_le
      intro u hu
      rw [h u hu]
      exact le_refl 1
    · simpa using Finset.le_sup (f := id) h1mem

private theorem mul_mem_inter_unitaryDivisors {d1 e1 d2 e2 u1 u2 : ℕ}
    (h12d : d1.Coprime d2) (h12e : e1.Coprime e2)
    (h1 : u1 ∈ d1.unitaryDivisors ∩ e1.unitaryDivisors)
    (h2 : u2 ∈ d2.unitaryDivisors ∩ e2.unitaryDivisors) :
    u1 * u2 ∈ (d1 * d2).unitaryDivisors ∩ (e1 * e2).unitaryDivisors := by
  rw [mem_inter] at h1 h2 ⊢
  exact ⟨Nat.mul_mem_unitaryDivisors_mul h12d h1.1 h2.1,
    Nat.mul_mem_unitaryDivisors_mul h12e h1.2 h2.2⟩

private theorem gcd_mem_inter_unitaryDivisors {m n d1 d2 e1 e2 u : ℕ} (hmn : m.Coprime n)
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hd1 : d1 ∣ m) (hd2 : d2 ∣ n) (he1 : e1 ∣ m) (he2 : e2 ∣ n)
    (hu : u ∈ (d1 * d2).unitaryDivisors ∩ (e1 * e2).unitaryDivisors) :
    u.gcd m ∈ d1.unitaryDivisors ∩ e1.unitaryDivisors ∧
      u.gcd n ∈ d2.unitaryDivisors ∩ e2.unitaryDivisors ∧ u.gcd m * u.gcd n = u := by
  obtain ⟨hud, hue⟩ := mem_inter.mp hu
  have huDdvd : u ∣ d1 * d2 := Nat.dvd_of_mem_unitaryDivisors hud
  have huEdvd : u ∣ e1 * e2 := Nat.dvd_of_mem_unitaryDivisors hue
  have huDcop : u.Coprime ((d1 * d2) / u) := Nat.coprime_div_of_mem_unitaryDivisors hud
  have huEcop : u.Coprime ((e1 * e2) / u) := Nat.coprime_div_of_mem_unitaryDivisors hue
  have hu1m : u.gcd m ∣ m := Nat.gcd_dvd_right u m
  have hu2n : u.gcd n ∣ n := Nat.gcd_dvd_right u n
  have hu1u : u.gcd m ∣ u := Nat.gcd_dvd_left u m
  have hu2u : u.gcd n ∣ u := Nat.gcd_dvd_left u n
  have hc1d2 : (u.gcd m).Coprime d2 := (hmn.coprime_dvd_left hu1m).coprime_dvd_right hd2
  have hc1e2 : (u.gcd m).Coprime e2 := (hmn.coprime_dvd_left hu1m).coprime_dvd_right he2
  have hc2d1 : (u.gcd n).Coprime d1 :=
    (hmn.symm.coprime_dvd_left hu2n).coprime_dvd_right hd1
  have hc2e1 : (u.gcd n).Coprime e1 :=
    (hmn.symm.coprime_dvd_left hu2n).coprime_dvd_right he1
  have hu1d1 : u.gcd m ∣ d1 := hc1d2.dvd_of_dvd_mul_right (hu1u.trans huDdvd)
  have hu2d2 : u.gcd n ∣ d2 := hc2d1.dvd_of_dvd_mul_left (hu2u.trans huDdvd)
  have hu1e1 : u.gcd m ∣ e1 := hc1e2.dvd_of_dvd_mul_right (hu1u.trans huEdvd)
  have hu2e2 : u.gcd n ∣ e2 := hc2e1.dvd_of_dvd_mul_left (hu2u.trans huEdvd)
  have humn : u ∣ m * n := huDdvd.trans (Nat.mul_dvd_mul hd1 hd2)
  have hsplit : u.gcd m * u.gcd n = u := gcd_mul_gcd_eq_of_dvd_mul hmn humn
  have hqd : (d1 * d2) / u = d1 / u.gcd m * (d2 / u.gcd n) := by
    conv_lhs => rw [← hsplit]
    exact (Nat.div_mul_div_comm hu1d1 hu2d2).symm
  have hqe : (e1 * e2) / u = e1 / u.gcd m * (e2 / u.gcd n) := by
    conv_lhs => rw [← hsplit]
    exact (Nat.div_mul_div_comm hu1e1 hu2e2).symm
  rw [hqd] at huDcop
  rw [hqe] at huEcop
  have hc1d : (u.gcd m).Coprime (d1 / u.gcd m) :=
    (huDcop.coprime_dvd_left hu1u).coprime_dvd_right (Nat.dvd_mul_right _ _)
  have hc2d : (u.gcd n).Coprime (d2 / u.gcd n) :=
    (huDcop.coprime_dvd_left hu2u).coprime_dvd_right (Nat.dvd_mul_left _ _)
  have hc1e : (u.gcd m).Coprime (e1 / u.gcd m) :=
    (huEcop.coprime_dvd_left hu1u).coprime_dvd_right (Nat.dvd_mul_right _ _)
  have hc2e : (u.gcd n).Coprime (e2 / u.gcd n) :=
    (huEcop.coprime_dvd_left hu2u).coprime_dvd_right (Nat.dvd_mul_left _ _)
  have hd10 : d1 ≠ 0 := ne_zero_of_dvd_ne_zero hd1 hm
  have hd20 : d2 ≠ 0 := ne_zero_of_dvd_ne_zero hd2 hn
  have he10 : e1 ≠ 0 := ne_zero_of_dvd_ne_zero he1 hm
  have he20 : e2 ≠ 0 := ne_zero_of_dvd_ne_zero he2 hn
  refine ⟨mem_inter.mpr ⟨?_, ?_⟩, mem_inter.mpr ⟨?_, ?_⟩, hsplit⟩
  · exact Nat.mem_unitaryDivisors.mpr ⟨hu1d1, hd10, hc1d⟩
  · exact Nat.mem_unitaryDivisors.mpr ⟨hu1e1, he10, hc1e⟩
  · exact Nat.mem_unitaryDivisors.mpr ⟨hu2d2, hd20, hc2d⟩
  · exact Nat.mem_unitaryDivisors.mpr ⟨hu2e2, he20, hc2e⟩

private theorem gcd_mem_biunitaryDivisors_of_mem_mul_left {m n d : ℕ} (hm : m ≠ 0)
    (hn : n ≠ 0) (hmn : m.Coprime n) (hd : d ∈ biunitaryDivisors (m * n)) :
    d.gcd m ∈ biunitaryDivisors m := by
  obtain ⟨hdvd, hmn0, hunit⟩ := mem_biunitaryDivisors.mp hd
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hdvd hmn0
  have hd1 : d.gcd m ∣ m := Nat.gcd_dvd_right d m
  have hd2 : d.gcd n ∣ n := Nat.gcd_dvd_right d n
  have hd10 : d.gcd m ≠ 0 := ne_zero_of_dvd_ne_zero hd1 hm
  have hd20 : d.gcd n ≠ 0 := ne_zero_of_dvd_ne_zero hd2 hn
  have he10 : m / d.gcd m ≠ 0 := div_ne_zero_of_dvd hd1 hm
  have he20 : n / d.gcd n ≠ 0 := div_ne_zero_of_dvd hd2 hn
  have hsplit : d.gcd m * d.gcd n = d := gcd_mul_gcd_eq_of_dvd_mul hmn hdvd
  have hqsplit : m / d.gcd m * (n / d.gcd n) = m * n / d := by
    rw [Nat.div_mul_div_comm hd1 hd2, hsplit]
  have hquot0 : m * n / d ≠ 0 := div_ne_zero_of_dvd hdvd hmn0
  refine mem_biunitaryDivisors.mpr ⟨hd1, hm, ?_⟩
  rw [gcdUnitary_eq_one_iff hd10 he10]
  intro u1 hu1
  have h1mem : (1 : ℕ) ∈ (d.gcd n).unitaryDivisors ∩ (n / d.gcd n).unitaryDivisors :=
    mem_inter.mpr ⟨by simp [hd20], by simp [he20]⟩
  have hprod := mul_mem_inter_unitaryDivisors
    ((hmn.coprime_dvd_left hd1).coprime_dvd_right hd2)
    ((hmn.coprime_dvd_left (Nat.div_dvd_of_dvd hd1)).coprime_dvd_right
      (Nat.div_dvd_of_dvd hd2))
    hu1 h1mem
  rw [hsplit, hqsplit, mul_one] at hprod
  exact (gcdUnitary_eq_one_iff hd0 hquot0).mp hunit _ hprod

private theorem gcd_mem_biunitaryDivisors_of_mem_mul_right {m n d : ℕ} (hm : m ≠ 0)
    (hn : n ≠ 0) (hmn : m.Coprime n) (hd : d ∈ biunitaryDivisors (m * n)) :
    d.gcd n ∈ biunitaryDivisors n := by
  rw [mul_comm m n] at hd
  exact gcd_mem_biunitaryDivisors_of_mem_mul_left hn hm hmn.symm hd

private theorem mul_mem_biunitaryDivisors_mul {m n d1 d2 : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hmn : m.Coprime n) (h1 : d1 ∈ biunitaryDivisors m) (h2 : d2 ∈ biunitaryDivisors n) :
    d1 * d2 ∈ biunitaryDivisors (m * n) := by
  obtain ⟨hd1, -, hunit1⟩ := mem_biunitaryDivisors.mp h1
  obtain ⟨hd2, -, hunit2⟩ := mem_biunitaryDivisors.mp h2
  have hdvd : d1 * d2 ∣ m * n := Nat.mul_dvd_mul hd1 hd2
  have hmn0 : m * n ≠ 0 := mul_ne_zero hm hn
  have hd0 : d1 * d2 ≠ 0 := ne_zero_of_dvd_ne_zero hdvd hmn0
  have hq : m * n / (d1 * d2) = m / d1 * (n / d2) :=
    (Nat.div_mul_div_comm hd1 hd2).symm
  have hquot0 : m * n / (d1 * d2) ≠ 0 := div_ne_zero_of_dvd hdvd hmn0
  have hd10 : d1 ≠ 0 := ne_zero_of_dvd_ne_zero hd1 hm
  have he10 : m / d1 ≠ 0 := div_ne_zero_of_dvd hd1 hm
  have hd20 : d2 ≠ 0 := ne_zero_of_dvd_ne_zero hd2 hn
  have he20 : n / d2 ≠ 0 := div_ne_zero_of_dvd hd2 hn
  refine mem_biunitaryDivisors.mpr ⟨hdvd, hmn0, ?_⟩
  rw [gcdUnitary_eq_one_iff hd0 hquot0, hq]
  intro u hu
  obtain ⟨hu1, hu2, hsplit⟩ := gcd_mem_inter_unitaryDivisors hmn hm hn hd1 hd2
    (Nat.div_dvd_of_dvd hd1) (Nat.div_dvd_of_dvd hd2) hu
  have e1 := (gcdUnitary_eq_one_iff hd10 he10).mp hunit1 _ hu1
  have e2 := (gcdUnitary_eq_one_iff hd20 he20).mp hunit2 _ hu2
  rw [e1, e2, mul_one] at hsplit
  exact hsplit.symm

private theorem sigmaBiunitary_mul_of_coprime {m n : ℕ} (hmn : m.Coprime n) :
    sigmaBiunitary (m * n) = sigmaBiunitary m * sigmaBiunitary n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp only [sigmaBiunitary]
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  symm
  refine Finset.sum_nbij' (fun x => x.1 * x.2) (fun d => (d.gcd m, d.gcd n)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hab
    rw [mem_product] at hab
    exact mul_mem_biunitaryDivisors_mul hm hn hmn hab.1 hab.2
  · intro d hd
    rw [mem_product]
    exact ⟨gcd_mem_biunitaryDivisors_of_mem_mul_left hm hn hmn hd,
      gcd_mem_biunitaryDivisors_of_mem_mul_right hm hn hmn hd⟩
  · rintro ⟨a, b⟩ hab
    rw [mem_product] at hab
    have ha : a ∣ m := dvd_of_mem_biunitaryDivisors hab.1
    have hb : b ∣ n := dvd_of_mem_biunitaryDivisors hab.2
    have hbm : b.Coprime m := hmn.symm.coprime_dvd_left hb
    have han : a.Coprime n := hmn.coprime_dvd_left ha
    show ((a * b).gcd m, (a * b).gcd n) = (a, b)
    simp only [Prod.mk.injEq]
    exact ⟨by rw [Nat.Coprime.gcd_mul_right_cancel a hbm, Nat.gcd_eq_left ha],
      by rw [mul_comm a b, Nat.Coprime.gcd_mul_right_cancel b han, Nat.gcd_eq_left hb]⟩
  · intro d hd
    exact gcd_mul_gcd_eq_of_dvd_mul hmn (dvd_of_mem_biunitaryDivisors hd)
  · rintro ⟨a, b⟩ _
    rfl

/-- **Powers of two dividing the biunitary divisor sum of an odd number.** For every odd natural
number $n$, $2^{\omega(n)}$ divides $\sigma^{**}(n)$, where $\omega(n)$ is the number of distinct
prime factors of $n$ and $\sigma^{**}$ is the biunitary divisor sum.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 2 (`jis-2025-25.4.5-lem-2`). -/
public theorem two_pow_card_primeFactors_dvd_sigmaBiunitary_of_odd (n : ℕ)
    (hn : Odd n) : 2 ^ n.primeFactors.card ∣ sigmaBiunitary n := by
  have hn0 : n ≠ 0 := fun h => Nat.not_odd_zero (h ▸ hn)
  have hmul : ∀ x y : ℕ, x.Coprime y →
      sigmaBiunitary (x * y) = sigmaBiunitary x * sigmaBiunitary y :=
    fun x y h => sigmaBiunitary_mul_of_coprime h
  have hfact : sigmaBiunitary n = n.factorization.prod fun p k => sigmaBiunitary (p ^ k) :=
    Nat.multiplicative_factorization sigmaBiunitary hmul sigmaBiunitary_one hn0
  rw [hfact]
  show 2 ^ n.primeFactors.card ∣ ∏ p ∈ n.primeFactors, sigmaBiunitary (p ^ n.factorization p)
  have h2 : (2 : ℕ) ^ n.primeFactors.card = ∏ _p ∈ n.primeFactors, 2 :=
    (Finset.prod_const 2).symm
  rw [h2]
  refine Finset.prod_dvd_prod_of_dvd _ _ fun p hp => ?_
  show 2 ∣ sigmaBiunitary (p ^ n.factorization p)
  obtain ⟨hpprime, hpdvd, -⟩ := Nat.mem_primeFactors.mp hp
  have hodd_p : Odd p := by
    obtain ⟨a, rfl⟩ := hpdvd
    exact Nat.Odd.of_mul_left hn
  have he : 1 ≤ n.factorization p := hpprime.factorization_pos_of_dvd hn0 hpdvd
  have hpos : 0 < p ^ n.factorization p := pow_pos hpprime.pos _
  rw [← even_iff_two_dvd, ← Nat.not_odd_iff_even]
  intro hodd
  obtain ⟨k, hk⟩ := (odd_sigmaBiunitary_iff _ hpos).mp hodd
  have hodd_pow : Odd (p ^ n.factorization p) := hodd_p.pow
  rw [hk] at hodd_pow
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [pow_zero] at hk
    have hlt : 1 < p ^ n.factorization p := Nat.one_lt_pow (by omega) hpprime.one_lt
    omega
  · exact hodd_pow.not_two_dvd_nat (dvd_pow_self 2 hk0.ne')

end MetaMathlibExt
