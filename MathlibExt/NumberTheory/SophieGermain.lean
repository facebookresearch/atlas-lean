/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

section

namespace MetaMathlibExt

private theorem zmodEqZero_iff_dvd (a n : ℕ) : (a : ZMod n) = 0 ↔ n ∣ a := by
  rw [← Nat.cast_zero (R := ZMod n), ZMod.natCast_eq_natCast_iff,
    Nat.modEq_zero_iff_dvd]

private theorem powResidue (q p : ℕ) (hq : Nat.Prime q) (hqq : q = 2 * p + 1)
    (hp0 : 0 < p) (a : ℕ) :
    (a : ZMod q) ^ p = 0 ∨ (a : ZMod q) ^ p = 1 ∨ (a : ZMod q) ^ p = -1 := by
  have : Fact (Nat.Prime q) := ⟨hq⟩
  by_cases ha : (a : ZMod q) = 0
  · left
    rw [ha]
    exact zero_pow (by omega : p ≠ 0)
  · have hflt : (a : ZMod q) ^ (q - 1) = 1 :=
      ZMod.pow_card_sub_one_eq_one ha
    have hq1 : q - 1 = 2 * p := by omega
    rw [hq1] at hflt
    have hsq : ((a : ZMod q) ^ p) ^ 2 = 1 := by
      rw [← pow_mul]
      have he : p * 2 = 2 * p := by ring
      rw [he]
      exact hflt
    rw [sq_eq_one_iff] at hsq
    exact Or.inr hsq

private theorem sgCore (q : ℕ) (A B C : ZMod q)
    (hA : A = 0 ∨ A ^ 2 = 1) (hB : B = 0 ∨ B ^ 2 = 1)
    (hC : C = 0 ∨ C ^ 2 = 1) (hsum : A + B = C) (hq7 : 7 ≤ q) :
    A = 0 ∨ B = 0 ∨ C = 0 := by
  rcases hA with rfl | hA2
  · exact Or.inl rfl
  rcases hB with rfl | hB2
  · exact Or.inr (Or.inl rfl)
  rcases hC with rfl | hC2
  · exact Or.inr (Or.inr rfl)
  exfalso
  have hC2' : C ^ 2 = (A + B) ^ 2 := by rw [← hsum]
  have hexpand : (A + B) ^ 2 = A ^ 2 + 2 * A * B + B ^ 2 := by ring
  have h2ab : 2 * A * B = -1 := by
    linear_combination hC2 - hA2 - hB2 - hC2' - hexpand
  have h4 : (2 * A * B) ^ 2 = 4 := by
    rw [mul_pow, mul_pow, hA2, hB2]
    ring
  have h41 : (4 : ZMod q) = 1 := by
    have hcongr : (2 * A * B) ^ 2 = (-1 : ZMod q) ^ 2 := by rw [h2ab]
    have hneg : (-1 : ZMod q) ^ 2 = 1 := Even.neg_one_pow ⟨1, rfl⟩
    linear_combination hcongr - h4 + hneg
  have h3 : ((3 : ℕ) : ZMod q) = 0 := by
    have hcast41 : ((4 : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by
      exact_mod_cast h41
    have h30 : ((3 : ℕ) : ZMod q) = ((4 : ℕ) : ZMod q) - ((1 : ℕ) : ZMod q) := by
      push_cast
      ring
    rw [h30, hcast41, sub_self]
  rw [zmodEqZero_iff_dvd] at h3
  have hle : q ≤ 3 := Nat.le_of_dvd (by norm_num) h3
  omega

private theorem sgDvd (x y z p q : ℕ) (hq : Nat.Prime q) (hqq : q = 2 * p + 1)
    (hp0 : 0 < p) (h : x ^ p + y ^ p = z ^ p) (hq7 : 7 ≤ q) :
    q ∣ x ∨ q ∣ y ∨ q ∣ z := by
  have : Fact (Nat.Prime q) := ⟨hq⟩
  have hrx := powResidue q p hq hqq hp0 x
  have hry := powResidue q p hq hqq hp0 y
  have hrz := powResidue q p hq hqq hp0 z
  have hcast : (x : ZMod q) ^ p + (y : ZMod q) ^ p = (z : ZMod q) ^ p := by
    have h2 : ((x ^ p + y ^ p : ℕ) : ZMod q) = ((z ^ p : ℕ) : ZMod q) :=
      congrArg (fun n : ℕ => (n : ZMod q)) h
    rwa [Nat.cast_add, Nat.cast_pow, Nat.cast_pow, Nat.cast_pow] at h2
  have e1 : (x : ZMod q) ^ p = 0 ∨ ((x : ZMod q) ^ p) ^ 2 = 1 := by
    rcases hrx with h0 | h1 | hm1
    · exact Or.inl h0
    · exact Or.inr (by rw [h1, one_pow])
    · exact Or.inr (by rw [hm1]; exact Even.neg_one_pow ⟨1, rfl⟩)
  have e2 : (y : ZMod q) ^ p = 0 ∨ ((y : ZMod q) ^ p) ^ 2 = 1 := by
    rcases hry with h0 | h1 | hm1
    · exact Or.inl h0
    · exact Or.inr (by rw [h1, one_pow])
    · exact Or.inr (by rw [hm1]; exact Even.neg_one_pow ⟨1, rfl⟩)
  have e3 : (z : ZMod q) ^ p = 0 ∨ ((z : ZMod q) ^ p) ^ 2 = 1 := by
    rcases hrz with h0 | h1 | hm1
    · exact Or.inl h0
    · exact Or.inr (by rw [h1, one_pow])
    · exact Or.inr (by rw [hm1]; exact Even.neg_one_pow ⟨1, rfl⟩)
  have hdisj := sgCore q _ _ _ e1 e2 e3 hcast hq7
  have hpne : p ≠ 0 := by omega
  rcases hdisj with hx0 | hy0 | hz0
  · left
    have hx00 : (x : ZMod q) = 0 := (pow_eq_zero_iff hpne).mp hx0
    exact (zmodEqZero_iff_dvd x q).mp hx00
  · right
    left
    have hy00 : (y : ZMod q) = 0 := (pow_eq_zero_iff hpne).mp hy0
    exact (zmodEqZero_iff_dvd y q).mp hy00
  · right
    right
    have hz00 : (z : ZMod q) = 0 := (pow_eq_zero_iff hpne).mp hz0
    exact (zmodEqZero_iff_dvd z q).mp hz00

private theorem addPowFactor (X Y : ℤ) (p : ℕ) (hp : Odd p) :
    (∑ i ∈ Finset.range p, X ^ i * (-Y) ^ (p - 1 - i)) * (X + Y)
      = X ^ p + Y ^ p := by
  have h := geom_sum₂_mul X (-Y) p
  rw [sub_neg_eq_add] at h
  rw [hp.neg_pow, sub_neg_eq_add] at h
  exact h

private theorem subPowFactor (Z Y : ℤ) (p : ℕ) :
    (∑ i ∈ Finset.range p, Z ^ i * Y ^ (p - 1 - i)) * (Z - Y)
      = Z ^ p - Y ^ p :=
  geom_sum₂_mul Z Y p

private theorem dvdAddPow (x y p : ℕ) (hp : Odd p) : (x + y) ∣ x ^ p + y ^ p := by
  have hform := addPowFactor (x : ℤ) (y : ℤ) p hp
  have hZdvd : ((x + y : ℕ) : ℤ) ∣ ((x ^ p + y ^ p : ℕ) : ℤ) := by
    have hcast : (x : ℤ) ^ p + (y : ℤ) ^ p = ((x ^ p + y ^ p : ℕ) : ℤ) := by
      rw [Nat.cast_add, Nat.cast_pow, Nat.cast_pow]
    have hxy : ((x + y : ℕ) : ℤ) = (x : ℤ) + (y : ℤ) := by
      rw [Nat.cast_add]
    rw [hxy]
    exact ⟨_, hcast.symm.trans (((mul_comm _ _).trans hform).symm)⟩
  exact Int.natCast_dvd_natCast.mp hZdvd

private theorem dvdSubPow (z y p : ℕ) (h : y ≤ z) : (z - y) ∣ z ^ p - y ^ p := by
  have hle : y ^ p ≤ z ^ p := pow_le_pow_left₀ (Nat.zero_le _) h p
  have hZdvd : ((z - y : ℕ) : ℤ) ∣ ((z ^ p - y ^ p : ℕ) : ℤ) := by
    have hform := subPowFactor (z : ℤ) (y : ℤ) p
    have hcast : (z : ℤ) ^ p - (y : ℤ) ^ p = ((z ^ p - y ^ p : ℕ) : ℤ) := by
      rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow]
    rw [Nat.cast_sub h]
    exact ⟨_, hcast.symm.trans (((mul_comm _ _).trans hform).symm)⟩
  exact Int.natCast_dvd_natCast.mp hZdvd

private theorem natPowOfCoprimeMul (a b c p : ℕ) (hcop : Nat.Coprime a b)
    (hprod : a * b = c ^ p) (hp : Odd p) : ∃ s, a = s ^ p := by
  have hI : IsCoprime ((a : ℕ) : ℤ) ((b : ℕ) : ℤ) :=
    Nat.Coprime.isCoprime hcop
  have hprodZ : ((a : ℕ) : ℤ) * ((b : ℕ) : ℤ) = ((c : ℕ) : ℤ) ^ p := by
    have h2 : ((((a * b : ℕ))) : ℤ) = (((c ^ p : ℕ)) : ℤ) :=
      congrArg (fun n : ℕ => (n : ℤ)) hprod
    rw [Nat.cast_mul, Nat.cast_pow] at h2
    exact h2
  obtain ⟨d, hd⟩ := (Int.eq_pow_of_mul_eq_pow_odd hI hp hprodZ).1
  have hd0 : 0 ≤ d := by
    by_contra hlt
    have hlt' : d < 0 := lt_of_not_ge hlt
    have h1 : (0 : ℤ) < (-d) ^ p := pow_pos (by omega) p
    have h2 : d ^ p = -((-d) ^ p) := by
      conv_lhs => rw [← neg_neg d]
      rw [hp.neg_pow]
    have h3 : (0 : ℤ) ≤ ((a : ℕ) : ℤ) := by positivity
    omega
  refine ⟨d.toNat, ?_⟩
  have hds : ((d.toNat : ℕ) : ℤ) = d := Int.toNat_of_nonneg hd0
  have hcast : ((a : ℕ) : ℤ) = ((d.toNat ^ p : ℕ) : ℤ) := by
    rw [Nat.cast_pow, hds]
    exact hd
  exact_mod_cast hcast

private theorem notDvdOfCoprimeDiv (q a b : ℕ) (hq7 : 7 ≤ q)
    (hcop : Nat.Coprime a b) (hqa : q ∣ a) : ¬ q ∣ b := by
  intro hqb
  have h1 : q ∣ 1 := by
    have hgd := Nat.dvd_gcd hqa hqb
    rwa [show Nat.gcd a b = 1 from hcop] at hgd
  have hq1 : q = 1 := Nat.dvd_one.mp h1
  omega

private theorem coprime_add_cofactor (x y M z p : ℕ) (hp : Odd p)
    (hpprime : Nat.Prime p) (hpz : ¬ p ∣ z)
    (hxy : Nat.Coprime x y)
    (hprod : (x + y) * M = z ^ p)
    (hMform : ((M : ℕ) : ℤ) =
      ∑ i ∈ Finset.range p, (x : ℤ) ^ i * (-(y : ℤ)) ^ (p - 1 - i)) :
    Nat.Coprime (x + y) M := by
  apply Nat.coprime_of_dvd
  intro k hkprime hkx hkM
  have hxy0 : (x : ZMod k) + (y : ZMod k) = 0 := by
    have hcast : ((x + y : ℕ) : ZMod k) = 0 := (zmodEqZero_iff_dvd _ _).mpr hkx
    rwa [Nat.cast_add] at hcast
  have hX : (x : ZMod k) = -(y : ZMod k) := by linear_combination hxy0
  have hM0 : (M : ZMod k) = 0 := (zmodEqZero_iff_dvd _ _).mpr hkM
  have hMcast : (M : ZMod k) =
      ∑ i ∈ Finset.range p, (x : ZMod k) ^ i * (-(y : ZMod k)) ^ (p - 1 - i) := by
    have h2 := congrArg (fun z : ℤ => (z : ZMod k)) hMform
    push_cast at h2
    exact h2
  have heven : Even (p - 1) := by
    obtain ⟨t, ht⟩ := hp
    exact ⟨t, by omega⟩
  have hterm : ∀ i ∈ Finset.range p,
      (x : ZMod k) ^ i * (-(y : ZMod k)) ^ (p - 1 - i)
        = (y : ZMod k) ^ (p - 1) := by
    intro i hi
    have hip : i + (p - 1 - i) = p - 1 := by
      have hmem := Finset.mem_range.mp hi
      omega
    rw [hX, ← pow_add, hip]
    exact heven.neg_pow _
  have hsum : ∑ i ∈ Finset.range p,
      (x : ZMod k) ^ i * (-(y : ZMod k)) ^ (p - 1 - i)
      = (p : ZMod k) * (y : ZMod k) ^ (p - 1) := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  have hzero : (p : ZMod k) * (y : ZMod k) ^ (p - 1) = 0 := by
    rw [← hsum, ← hMcast]
    exact hM0
  have hdvd : k ∣ p * y ^ (p - 1) := by
    have hcast0 : ((p * y ^ (p - 1) : ℕ) : ZMod k) = 0 := by
      push_cast
      exact hzero
    exact (zmodEqZero_iff_dvd _ _).mp hcast0
  rcases (hkprime.dvd_mul.mp hdvd) with hkp | hky
  · have hkeq : k = p := (Nat.prime_dvd_prime_iff_eq hkprime hpprime).mp hkp
    have hkx' : p ∣ x + y := by
      rw [← hkeq]
      exact hkx
    have hdz : p ∣ z ^ p := by
      rw [← hprod]
      exact hkx'.mul_right M
    exact hpz (hpprime.dvd_of_dvd_pow hdz)
  · have hky1 : k ∣ y := hkprime.dvd_of_dvd_pow hky
    have hkx1 : k ∣ x := by
      have hsub := Nat.dvd_sub hkx hky1
      rwa [Nat.add_sub_cancel] at hsub
    have h1 : k ∣ 1 := by
      have hgd := Nat.dvd_gcd hkx1 hky1
      rwa [show Nat.gcd x y = 1 from hxy] at hgd
    have hkeq1 : k = 1 := Nat.dvd_one.mp h1
    exact hkprime.ne_one hkeq1

private theorem coprime_sub_cofactor (z y L x p : ℕ) (hyz_le : y ≤ z)
    (hpprime : Nat.Prime p) (hpx : ¬ p ∣ x)
    (hyz : Nat.Coprime y z)
    (hprod : (z - y) * L = x ^ p)
    (hLform : ((L : ℕ) : ℤ) =
      ∑ i ∈ Finset.range p, (z : ℤ) ^ i * (y : ℤ) ^ (p - 1 - i)) :
    Nat.Coprime (z - y) L := by
  apply Nat.coprime_of_dvd
  intro k hkprime hkz hkL
  have hZY0 : (z : ZMod k) - (y : ZMod k) = 0 := by
    have hcast : ((z - y : ℕ) : ZMod k) = 0 := (zmodEqZero_iff_dvd _ _).mpr hkz
    rwa [Nat.cast_sub hyz_le] at hcast
  have hZY : (z : ZMod k) = (y : ZMod k) := by linear_combination hZY0
  have hL0 : (L : ZMod k) = 0 := (zmodEqZero_iff_dvd _ _).mpr hkL
  have hLcast : (L : ZMod k) =
      ∑ i ∈ Finset.range p, (z : ZMod k) ^ i * (y : ZMod k) ^ (p - 1 - i) := by
    have h2 := congrArg (fun z : ℤ => (z : ZMod k)) hLform
    push_cast at h2
    exact h2
  have hterm : ∀ i ∈ Finset.range p,
      (z : ZMod k) ^ i * (y : ZMod k) ^ (p - 1 - i)
        = (y : ZMod k) ^ (p - 1) := by
    intro i hi
    have hip : i + (p - 1 - i) = p - 1 := by
      have hmem := Finset.mem_range.mp hi
      omega
    rw [hZY, ← pow_add, hip]
  have hsum : ∑ i ∈ Finset.range p,
      (z : ZMod k) ^ i * (y : ZMod k) ^ (p - 1 - i)
      = (p : ZMod k) * (y : ZMod k) ^ (p - 1) := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  have hzero : (p : ZMod k) * (y : ZMod k) ^ (p - 1) = 0 := by
    rw [← hsum, ← hLcast]
    exact hL0
  have hdvd : k ∣ p * y ^ (p - 1) := by
    have hcast0 : ((p * y ^ (p - 1) : ℕ) : ZMod k) = 0 := by
      push_cast
      exact hzero
    exact (zmodEqZero_iff_dvd _ _).mp hcast0
  rcases (hkprime.dvd_mul.mp hdvd) with hkp | hky
  · have hkeq : k = p := (Nat.prime_dvd_prime_iff_eq hkprime hpprime).mp hkp
    have hkz' : p ∣ z - y := by
      rw [← hkeq]
      exact hkz
    have hdx : p ∣ x ^ p := by
      rw [← hprod]
      exact hkz'.mul_right L
    exact hpx (hpprime.dvd_of_dvd_pow hdx)
  · have hky1 : k ∣ y := hkprime.dvd_of_dvd_pow hky
    have hkz1 : k ∣ z := by
      have hadd := Nat.dvd_add hkz hky1
      rwa [Nat.sub_add_cancel hyz_le] at hadd
    have h1 : k ∣ 1 := by
      have hgd := Nat.dvd_gcd hky1 hkz1
      rwa [show Nat.gcd y z = 1 from hyz] at hgd
    have hkeq1 : k = 1 := Nat.dvd_one.mp h1
    exact hkprime.ne_one hkeq1

private theorem sumCofactorForm (x y z M p : ℕ) (hp : Odd p)
    (hprod : (x + y) * M = z ^ p) (hsum : x ^ p + y ^ p = z ^ p)
    (hxy0 : 0 < x + y) :
    ((M : ℕ) : ℤ) =
      ∑ i ∈ Finset.range p, (x : ℤ) ^ i * (-(y : ℤ)) ^ (p - 1 - i) := by
  have hcastprod : (((x + y : ℕ)) : ℤ) * ((M : ℕ) : ℤ) = (z : ℤ) ^ p := by
    have h2 : ((((x + y) * M : ℕ)) : ℤ) = (((z ^ p : ℕ)) : ℤ) :=
      congrArg (fun n : ℕ => (n : ℤ)) hprod
    rw [Nat.cast_mul, Nat.cast_pow] at h2
    exact h2
  have hne : (((x + y : ℕ)) : ℤ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hxy0)
  have hform := addPowFactor (x : ℤ) (y : ℤ) p hp
  have hXY : (((x + y : ℕ)) : ℤ) = (x : ℤ) + (y : ℤ) := by
    rw [Nat.cast_add]
  have hXpYp : (x : ℤ) ^ p + (y : ℤ) ^ p = (z : ℤ) ^ p := by
    have h2 : (((x ^ p + y ^ p : ℕ)) : ℤ) = (((z ^ p : ℕ)) : ℤ) :=
      congrArg (fun n : ℕ => (n : ℤ)) hsum
    rw [Nat.cast_add, Nat.cast_pow, Nat.cast_pow, Nat.cast_pow] at h2
    exact h2
  apply mul_left_cancel₀ hne
  rw [hcastprod, hXY]
  rw [hXpYp] at hform
  exact ((mul_comm _ _).trans hform).symm

private theorem subCofactorForm (z y x L p : ℕ) (hyz : y ≤ z)
    (hprod : (z - y) * L = x ^ p) (hdiff : x ^ p = z ^ p - y ^ p)
    (hzy0 : y < z) :
    ((L : ℕ) : ℤ) =
      ∑ i ∈ Finset.range p, (z : ℤ) ^ i * (y : ℤ) ^ (p - 1 - i) := by
  have hle : y ^ p ≤ z ^ p := pow_le_pow_left₀ (Nat.zero_le _) hyz p
  have hcastprod : (((z - y : ℕ)) : ℤ) * ((L : ℕ) : ℤ) = (x : ℤ) ^ p := by
    have h2 : ((((z - y) * L : ℕ)) : ℤ) = (((x ^ p : ℕ)) : ℤ) :=
      congrArg (fun n : ℕ => (n : ℤ)) hprod
    rw [Nat.cast_mul, Nat.cast_pow] at h2
    exact h2
  have hXeq : (x : ℤ) ^ p = (z : ℤ) ^ p - (y : ℤ) ^ p := by
    have h2 : (((x ^ p : ℕ)) : ℤ) = (((z ^ p - y ^ p : ℕ)) : ℤ) :=
      congrArg (fun n : ℕ => (n : ℤ)) hdiff
    rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow, Nat.cast_pow] at h2
    exact h2
  have hZY : (((z - y : ℕ)) : ℤ) = (z : ℤ) - (y : ℤ) := Nat.cast_sub hyz
  have hne : (((z - y : ℕ)) : ℤ) ≠ 0 := by
    have hpos : 0 < z - y := by omega
    exact_mod_cast (ne_of_gt hpos)
  have hform := subPowFactor (z : ℤ) (y : ℤ) p
  apply mul_left_cancel₀ hne
  rw [hcastprod, hZY, hXeq]
  exact ((mul_comm _ _).trans hform).symm

private theorem case_q_dvd_x (p x y z : ℕ)
    (hp_odd : Odd p) (hpprime : Nat.Prime p) (hqprime : Nat.Prime (2 * p + 1))
    (hx0 : 0 < x) (hy0 : 0 < y) (_hz0 : 0 < z)
    (hxy : Nat.Coprime x y) (hyz : Nat.Coprime y z) (hxz : Nat.Coprime x z)
    (h : x ^ p + y ^ p = z ^ p)
    (hpx : ¬ p ∣ x) (hpy : ¬ p ∣ y) (hpz : ¬ p ∣ z)
    (hqx : (2 * p + 1) ∣ x) : False := by
  have : Fact (Nat.Prime (2 * p + 1)) := ⟨hqprime⟩
  have hp3 : 3 ≤ p := by
    have h2 := hpprime.two_le
    have hne2 : p ≠ 2 := by
      intro hcon2
      rw [hcon2] at hp_odd
      have hodd := Nat.odd_iff.mp hp_odd
      norm_num at hodd
    omega
  have hpne : p ≠ 0 := by omega
  have hp0 : 0 < p := by omega
  have hq7 : 7 ≤ 2 * p + 1 := by omega
  have hq1 : (2 * p + 1) - 1 = 2 * p := by omega
  have heven : Even (p - 1) := by
    obtain ⟨t, ht⟩ := hp_odd
    exact ⟨t, by omega⟩
  have hxz_lt : x < z := by
    by_contra hcon
    have hcon' : z ≤ x := not_lt.mp hcon
    have hle : z ^ p ≤ x ^ p := pow_le_pow_left₀ (Nat.zero_le _) hcon' p
    have hx1 : 1 ≤ x ^ p := by
      have hpos := pow_pos hx0 p
      omega
    have hy1 : 1 ≤ y ^ p := by
      have hpos := pow_pos hy0 p
      omega
    omega
  have hyz_lt : y < z := by
    by_contra hcon
    have hcon' : z ≤ y := not_lt.mp hcon
    have hle : z ^ p ≤ y ^ p := pow_le_pow_left₀ (Nat.zero_le _) hcon' p
    have hx1 : 1 ≤ x ^ p := by
      have hpos := pow_pos hx0 p
      omega
    have hy1 : 1 ≤ y ^ p := by
      have hpos := pow_pos hy0 p
      omega
    omega
  have hdvdM : (x + y) ∣ z ^ p := by
    rw [← h]
    exact dvdAddPow x y p hp_odd
  have hdiffN : y ^ p = z ^ p - x ^ p := by omega
  have hdvdN : (z - x) ∣ y ^ p := by
    have h1 := dvdSubPow z x p (le_of_lt hxz_lt)
    rwa [hdiffN]
  have hdiffK : x ^ p = z ^ p - y ^ p := by omega
  have hdvdK : (z - y) ∣ x ^ p := by
    have h1 := dvdSubPow z y p (le_of_lt hyz_lt)
    rwa [hdiffK]
  have hprodM : (x + y) * (z ^ p / (x + y)) = z ^ p := by
    rw [mul_comm]
    exact Nat.div_mul_cancel hdvdM
  have hprodN : (z - x) * (y ^ p / (z - x)) = y ^ p := by
    rw [mul_comm]
    exact Nat.div_mul_cancel hdvdN
  have hprodK : (z - y) * (x ^ p / (z - y)) = x ^ p := by
    rw [mul_comm]
    exact Nat.div_mul_cancel hdvdK
  have hprodK' : (x ^ p / (z - y)) * (z - y) = x ^ p :=
    Nat.div_mul_cancel hdvdK
  have hMform := sumCofactorForm x y z (z ^ p / (x + y)) p hp_odd hprodM h
    (show 0 < x + y by omega)
  have hNform := subCofactorForm z x y (y ^ p / (z - x)) p
    (le_of_lt hxz_lt) hprodN hdiffN hxz_lt
  have hKform := subCofactorForm z y x (x ^ p / (z - y)) p
    (le_of_lt hyz_lt) hprodK hdiffK hyz_lt
  have hcopM := coprime_add_cofactor x y (z ^ p / (x + y)) z p hp_odd hpprime
    hpz hxy hprodM hMform
  have hcopN := coprime_sub_cofactor z x (y ^ p / (z - x)) y p
    (le_of_lt hxz_lt) hpprime hpy hxz hprodN hNform
  have hcopK := coprime_sub_cofactor z y (x ^ p / (z - y)) x p
    (le_of_lt hyz_lt) hpprime hpx hyz hprodK hKform
  obtain ⟨s, hs⟩ := natPowOfCoprimeMul (x + y) (z ^ p / (x + y)) z p
    hcopM hprodM hp_odd
  obtain ⟨u, hu⟩ := natPowOfCoprimeMul (z - x) (y ^ p / (z - x)) y p
    hcopN hprodN hp_odd
  obtain ⟨t, ht⟩ := natPowOfCoprimeMul (z - y) (x ^ p / (z - y)) x p
    hcopK hprodK hp_odd
  obtain ⟨l, hl⟩ := natPowOfCoprimeMul (x ^ p / (z - y)) (z - y) x p
    hcopK.symm hprodK' hp_odd
  have hcast : (x : ZMod (2 * p + 1)) ^ p + (y : ZMod (2 * p + 1)) ^ p
      = (z : ZMod (2 * p + 1)) ^ p := by
    have h2 : (((x ^ p + y ^ p : ℕ)) : ZMod (2 * p + 1))
        = (((z ^ p : ℕ)) : ZMod (2 * p + 1)) :=
      congrArg (fun n : ℕ => (n : ZMod (2 * p + 1))) h
    rwa [Nat.cast_add, Nat.cast_pow, Nat.cast_pow, Nat.cast_pow] at h2
  have hqy_n : ¬ (2 * p + 1) ∣ y :=
    notDvdOfCoprimeDiv (2 * p + 1) x y hq7 hxy hqx
  have hqz_n : ¬ (2 * p + 1) ∣ z :=
    notDvdOfCoprimeDiv (2 * p + 1) x z hq7 hxz hqx
  have hqs_n : ¬ (2 * p + 1) ∣ s := by
    intro hqs
    have h1 : (2 * p + 1) ∣ x + y := by
      have hsp : (2 * p + 1) ∣ s ^ p := hqs.trans (dvd_pow_self s hpne)
      rwa [← hs] at hsp
    have h2 : (2 * p + 1) ∣ y := by
      have hsub := Nat.dvd_sub h1 hqx
      rwa [Nat.add_sub_cancel_left] at hsub
    exact hqy_n h2
  have hqu_n : ¬ (2 * p + 1) ∣ u := by
    intro hqu
    have h1 : (2 * p + 1) ∣ z - x := by
      have hup : (2 * p + 1) ∣ u ^ p := hqu.trans (dvd_pow_self u hpne)
      rwa [← hu] at hup
    have h2 : (2 * p + 1) ∣ z := by
      have hadd := Nat.dvd_add h1 hqx
      rwa [Nat.sub_add_cancel (le_of_lt hxz_lt)] at hadd
    exact hqz_n h2
  have hx0q : (x : ZMod (2 * p + 1)) = 0 :=
    (zmodEqZero_iff_dvd _ _).mpr hqx
  have hsx : (s : ZMod (2 * p + 1)) ^ p = (y : ZMod (2 * p + 1)) := by
    have h2 := congrArg (fun n : ℕ => (n : ZMod (2 * p + 1))) hs
    rw [Nat.cast_add, Nat.cast_pow] at h2
    rw [hx0q, zero_add] at h2
    exact h2.symm
  have hY2 : (y : ZMod (2 * p + 1)) ^ 2 = 1 := by
    have hsne : (s : ZMod (2 * p + 1)) ≠ 0 :=
      fun h0 => hqs_n ((zmodEqZero_iff_dvd _ _).mp h0)
    have hflt : (s : ZMod (2 * p + 1)) ^ ((2 * p + 1) - 1) = 1 :=
      ZMod.pow_card_sub_one_eq_one hsne
    rw [hq1] at hflt
    have hsq : ((s : ZMod (2 * p + 1)) ^ p) ^ 2 = 1 := by
      rw [← pow_mul, show p * 2 = 2 * p by ring]
      exact hflt
    rwa [hsx] at hsq
  have hYpm : (y : ZMod (2 * p + 1)) = 1 ∨ (y : ZMod (2 * p + 1)) = -1 :=
    sq_eq_one_iff.mp hY2
  have huz : (u : ZMod (2 * p + 1)) ^ p = (z : ZMod (2 * p + 1)) := by
    have h2 := congrArg (fun n : ℕ => (n : ZMod (2 * p + 1))) hu
    rw [Nat.cast_sub (le_of_lt hxz_lt), Nat.cast_pow, hx0q, sub_zero] at h2
    exact h2.symm
  have hZ2 : (z : ZMod (2 * p + 1)) ^ 2 = 1 := by
    have hune : (u : ZMod (2 * p + 1)) ≠ 0 :=
      fun h0 => hqu_n ((zmodEqZero_iff_dvd _ _).mp h0)
    have hflt : (u : ZMod (2 * p + 1)) ^ ((2 * p + 1) - 1) = 1 :=
      ZMod.pow_card_sub_one_eq_one hune
    rw [hq1] at hflt
    have hsq : ((u : ZMod (2 * p + 1)) ^ p) ^ 2 = 1 := by
      rw [← pow_mul, show p * 2 = 2 * p by ring]
      exact hflt
    rwa [huz] at hsq
  have hZpm : (z : ZMod (2 * p + 1)) = 1 ∨ (z : ZMod (2 * p + 1)) = -1 :=
    sq_eq_one_iff.mp hZ2
  have htt : (t : ZMod (2 * p + 1)) ^ p
      = (z : ZMod (2 * p + 1)) - (y : ZMod (2 * p + 1)) := by
    have h2 := congrArg (fun n : ℕ => (n : ZMod (2 * p + 1))) ht
    rw [Nat.cast_pow] at h2
    have hZYcast : ((z - y : ℕ) : ZMod (2 * p + 1))
        = (z : ZMod (2 * p + 1)) - (y : ZMod (2 * p + 1)) :=
      Nat.cast_sub (le_of_lt hyz_lt)
    rw [hZYcast] at h2
    exact h2.symm
  have hZYeq : (z : ZMod (2 * p + 1)) = (y : ZMod (2 * p + 1)) := by
    by_cases hqt : (2 * p + 1) ∣ t
    · have ht0 : (t : ZMod (2 * p + 1)) = 0 :=
        (zmodEqZero_iff_dvd _ _).mpr hqt
      have htp0 : (t : ZMod (2 * p + 1)) ^ p = 0 := by
        rw [ht0]
        exact zero_pow hpne
      rw [htp0] at htt
      exact sub_eq_zero.mp htt.symm
    · have htne : (t : ZMod (2 * p + 1)) ≠ 0 :=
        fun h0 => hqt ((zmodEqZero_iff_dvd _ _).mp h0)
      have hflt : (t : ZMod (2 * p + 1)) ^ ((2 * p + 1) - 1) = 1 :=
        ZMod.pow_card_sub_one_eq_one htne
      rw [hq1] at hflt
      have htsq : ((t : ZMod (2 * p + 1)) ^ p) ^ 2 = 1 := by
        rw [← pow_mul, show p * 2 = 2 * p by ring]
        exact hflt
      rw [htt] at htsq
      have hexpand : ((z : ZMod (2 * p + 1)) - (y : ZMod (2 * p + 1))) ^ 2
          = 2 - 2 * (z : ZMod (2 * p + 1)) * (y : ZMod (2 * p + 1)) := by
        linear_combination hZ2 + hY2
      have h2ZY : 2 * (z : ZMod (2 * p + 1)) * (y : ZMod (2 * p + 1)) = 1 := by
        linear_combination hexpand - htsq
      have e1 : (2 * (z : ZMod (2 * p + 1)) * (y : ZMod (2 * p + 1))) ^ 2
          = 4 := by
        rw [mul_pow, mul_pow, hZ2, hY2]
        ring
      have h4 : (4 : ZMod (2 * p + 1)) = 1 := by
        have hcongr : (2 * (z : ZMod (2 * p + 1)) * (y : ZMod (2 * p + 1))) ^ 2
            = (1 : ZMod (2 * p + 1)) ^ 2 := by rw [h2ZY]
        have h1sq : (1 : ZMod (2 * p + 1)) ^ 2 = 1 := one_pow 2
        linear_combination hcongr - e1 + h1sq
      have h3 : (3 : ZMod (2 * p + 1)) = 0 := by linear_combination h4
      have h3cast : ((3 : ℕ) : ZMod (2 * p + 1)) = 0 := by
        exact_mod_cast h3
      have hdvd3 : (2 * p + 1) ∣ 3 := (zmodEqZero_iff_dvd _ _).mp h3cast
      have hle3 : 2 * p + 1 ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd3
      exfalso
      omega
  have hKq : ((x ^ p / (z - y) : ℕ) : ZMod (2 * p + 1))
      = ∑ i ∈ Finset.range p, (z : ZMod (2 * p + 1)) ^ i
        * (y : ZMod (2 * p + 1)) ^ (p - 1 - i) := by
    have h2 := congrArg (fun z : ℤ => (z : ZMod (2 * p + 1))) hKform
    push_cast at h2
    exact h2
  have hKval : ((x ^ p / (z - y) : ℕ) : ZMod (2 * p + 1))
      = ((p : ℕ) : ZMod (2 * p + 1)) := by
    rw [hKq]
    have hterm : ∀ i ∈ Finset.range p,
        (z : ZMod (2 * p + 1)) ^ i * (y : ZMod (2 * p + 1)) ^ (p - 1 - i)
          = (y : ZMod (2 * p + 1)) ^ (p - 1) := by
      intro i hi
      have hip : i + (p - 1 - i) = p - 1 := by
        have hmem := Finset.mem_range.mp hi
        omega
      rw [hZYeq, ← pow_add, hip]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    have hYp1 : (y : ZMod (2 * p + 1)) ^ (p - 1) = 1 := by
      rcases hYpm with h1 | h1
      · rw [h1, one_pow]
      · rw [h1]
        exact Even.neg_one_pow heven
    rw [hYp1, mul_one]
  have hlp : ((l : ℕ) : ZMod (2 * p + 1)) ^ p
      = ((x ^ p / (z - y) : ℕ) : ZMod (2 * p + 1)) := by
    have h2 := congrArg (fun n : ℕ => (n : ZMod (2 * p + 1))) hl
    rw [Nat.cast_pow] at h2
    exact h2.symm
  have hql : ¬ (2 * p + 1) ∣ l := by
    intro hql
    have hm10 : ((l : ℕ) : ZMod (2 * p + 1)) ^ p = 0 := by
      have hl0 := (zmodEqZero_iff_dvd _ _).mpr hql
      rw [hl0]
      exact zero_pow hpne
    have hK0 : ((x ^ p / (z - y) : ℕ) : ZMod (2 * p + 1)) = 0 := by
      rw [← hlp]
      exact hm10
    rw [hKval] at hK0
    have hpdvd : (2 * p + 1) ∣ p := (zmodEqZero_iff_dvd _ _).mp hK0
    have hle : 2 * p + 1 ≤ p := Nat.le_of_dvd hp0 hpdvd
    omega
  have hfin : ((p : ℕ) : ZMod (2 * p + 1)) = 1
      ∨ ((p : ℕ) : ZMod (2 * p + 1)) = -1 := by
    have hlres := powResidue (2 * p + 1) p hqprime rfl hp0 l
    rcases hlres with h0 | h1 | hm1
    · exfalso
      have hl0 : ((l : ℕ) : ZMod (2 * p + 1)) = 0 :=
        (pow_eq_zero_iff hpne).mp h0
      exact hql ((zmodEqZero_iff_dvd _ _).mp hl0)
    · left
      rw [← hKval, ← hlp]
      exact h1
    · right
      rw [← hKval, ← hlp]
      exact hm1
  rcases hfin with h1 | hm1
  · have hcastp : ((p - 1 : ℕ) : ZMod (2 * p + 1)) = 0 := by
      rw [Nat.cast_sub (by omega : 1 ≤ p), h1, Nat.cast_one, sub_self]
    have hdvd : (2 * p + 1) ∣ p - 1 := (zmodEqZero_iff_dvd _ _).mp hcastp
    have hle : 2 * p + 1 ≤ p - 1 := Nat.le_of_dvd (by omega) hdvd
    omega
  · have hcastp : ((p + 1 : ℕ) : ZMod (2 * p + 1)) = 0 := by
      have e : ((p + 1 : ℕ) : ZMod (2 * p + 1))
          = ((p : ℕ) : ZMod (2 * p + 1)) + 1 := by
        rw [Nat.cast_add, Nat.cast_one]
      rw [e, hm1, neg_add_cancel]
    have hdvd : (2 * p + 1) ∣ p + 1 := (zmodEqZero_iff_dvd _ _).mp hcastp
    have hle : 2 * p + 1 ≤ p + 1 := Nat.le_of_dvd (by positivity) hdvd
    omega

private theorem case_q_dvd_z (p x y z : ℕ)
    (hp_odd : Odd p) (hpprime : Nat.Prime p) (hqprime : Nat.Prime (2 * p + 1))
    (hx0 : 0 < x) (hy0 : 0 < y) (_hz0 : 0 < z)
    (hxy : Nat.Coprime x y) (hyz : Nat.Coprime y z) (hxz : Nat.Coprime x z)
    (h : x ^ p + y ^ p = z ^ p)
    (hpx : ¬ p ∣ x) (hpy : ¬ p ∣ y) (hpz : ¬ p ∣ z)
    (hqz : (2 * p + 1) ∣ z) : False := by
  have : Fact (Nat.Prime (2 * p + 1)) := ⟨hqprime⟩
  have hp3 : 3 ≤ p := by
    have h2 := hpprime.two_le
    have hne2 : p ≠ 2 := by
      intro hcon2
      rw [hcon2] at hp_odd
      have hodd := Nat.odd_iff.mp hp_odd
      norm_num at hodd
    omega
  have hpne : p ≠ 0 := by omega
  have hp0 : 0 < p := by omega
  have hq7 : 7 ≤ 2 * p + 1 := by omega
  have hq1 : (2 * p + 1) - 1 = 2 * p := by omega
  have heven : Even (p - 1) := by
    obtain ⟨t, ht⟩ := hp_odd
    exact ⟨t, by omega⟩
  have hxz_lt : x < z := by
    by_contra hcon
    have hcon' : z ≤ x := not_lt.mp hcon
    have hle : z ^ p ≤ x ^ p := pow_le_pow_left₀ (Nat.zero_le _) hcon' p
    have hx1 : 1 ≤ x ^ p := by
      have hpos := pow_pos hx0 p
      omega
    have hy1 : 1 ≤ y ^ p := by
      have hpos := pow_pos hy0 p
      omega
    omega
  have hyz_lt : y < z := by
    by_contra hcon
    have hcon' : z ≤ y := not_lt.mp hcon
    have hle : z ^ p ≤ y ^ p := pow_le_pow_left₀ (Nat.zero_le _) hcon' p
    have hx1 : 1 ≤ x ^ p := by
      have hpos := pow_pos hx0 p
      omega
    have hy1 : 1 ≤ y ^ p := by
      have hpos := pow_pos hy0 p
      omega
    omega
  have hdvdM : (x + y) ∣ z ^ p := by
    rw [← h]
    exact dvdAddPow x y p hp_odd
  have hdiffN : y ^ p = z ^ p - x ^ p := by omega
  have hdvdN : (z - x) ∣ y ^ p := by
    have h1 := dvdSubPow z x p (le_of_lt hxz_lt)
    rwa [hdiffN]
  have hdiffK : x ^ p = z ^ p - y ^ p := by omega
  have hdvdK : (z - y) ∣ x ^ p := by
    have h1 := dvdSubPow z y p (le_of_lt hyz_lt)
    rwa [hdiffK]
  have hprodM : (x + y) * (z ^ p / (x + y)) = z ^ p := by
    rw [mul_comm]
    exact Nat.div_mul_cancel hdvdM
  have hprodM' : (z ^ p / (x + y)) * (x + y) = z ^ p :=
    Nat.div_mul_cancel hdvdM
  have hprodN : (z - x) * (y ^ p / (z - x)) = y ^ p := by
    rw [mul_comm]
    exact Nat.div_mul_cancel hdvdN
  have hprodK : (z - y) * (x ^ p / (z - y)) = x ^ p := by
    rw [mul_comm]
    exact Nat.div_mul_cancel hdvdK
  have hMform := sumCofactorForm x y z (z ^ p / (x + y)) p hp_odd hprodM h
    (show 0 < x + y by omega)
  have hNform := subCofactorForm z x y (y ^ p / (z - x)) p
    (le_of_lt hxz_lt) hprodN hdiffN hxz_lt
  have hKform := subCofactorForm z y x (x ^ p / (z - y)) p
    (le_of_lt hyz_lt) hprodK hdiffK hyz_lt
  have hcopM := coprime_add_cofactor x y (z ^ p / (x + y)) z p hp_odd hpprime
    hpz hxy hprodM hMform
  have hcopN := coprime_sub_cofactor z x (y ^ p / (z - x)) y p
    (le_of_lt hxz_lt) hpprime hpy hxz hprodN hNform
  have hcopK := coprime_sub_cofactor z y (x ^ p / (z - y)) x p
    (le_of_lt hyz_lt) hpprime hpx hyz hprodK hKform
  obtain ⟨u, hu⟩ := natPowOfCoprimeMul (z - x) (y ^ p / (z - x)) y p
    hcopN hprodN hp_odd
  obtain ⟨t, ht⟩ := natPowOfCoprimeMul (z - y) (x ^ p / (z - y)) x p
    hcopK hprodK hp_odd
  obtain ⟨m1, hm1⟩ := natPowOfCoprimeMul (z ^ p / (x + y)) (x + y) z p
    hcopM.symm hprodM' hp_odd
  have hcast : (x : ZMod (2 * p + 1)) ^ p + (y : ZMod (2 * p + 1)) ^ p
      = (z : ZMod (2 * p + 1)) ^ p := by
    have h2 : (((x ^ p + y ^ p : ℕ)) : ZMod (2 * p + 1))
        = (((z ^ p : ℕ)) : ZMod (2 * p + 1)) :=
      congrArg (fun n : ℕ => (n : ZMod (2 * p + 1))) h
    rwa [Nat.cast_add, Nat.cast_pow, Nat.cast_pow, Nat.cast_pow] at h2
  have hqx_n : ¬ (2 * p + 1) ∣ x :=
    notDvdOfCoprimeDiv (2 * p + 1) z x hq7 hxz.symm hqz
  have hqy_n : ¬ (2 * p + 1) ∣ y :=
    notDvdOfCoprimeDiv (2 * p + 1) z y hq7 hyz.symm hqz
  have hqu_n : ¬ (2 * p + 1) ∣ u := by
    intro hqu
    have h1 : (2 * p + 1) ∣ z - x := by
      have hup : (2 * p + 1) ∣ u ^ p := hqu.trans (dvd_pow_self u hpne)
      rwa [← hu] at hup
    have h2 : (2 * p + 1) ∣ x := by
      have hsub := Nat.dvd_sub hqz h1
      rwa [Nat.sub_sub_self (le_of_lt hxz_lt)] at hsub
    exact hqx_n h2
  have hqt_n : ¬ (2 * p + 1) ∣ t := by
    intro hqt
    have h1 : (2 * p + 1) ∣ z - y := by
      have htp : (2 * p + 1) ∣ t ^ p := hqt.trans (dvd_pow_self t hpne)
      rwa [← ht] at htp
    have h2 : (2 * p + 1) ∣ y := by
      have hsub := Nat.dvd_sub hqz h1
      rwa [Nat.sub_sub_self (le_of_lt hyz_lt)] at hsub
    exact hqy_n h2
  have hZ0 : (z : ZMod (2 * p + 1)) = 0 :=
    (zmodEqZero_iff_dvd _ _).mpr hqz
  have huX : (u : ZMod (2 * p + 1)) ^ p = -(x : ZMod (2 * p + 1)) := by
    have h2 := congrArg (fun n : ℕ => (n : ZMod (2 * p + 1))) hu
    rw [Nat.cast_sub (le_of_lt hxz_lt), Nat.cast_pow] at h2
    rw [hZ0, zero_sub] at h2
    exact h2.symm
  have hX2 : (x : ZMod (2 * p + 1)) ^ 2 = 1 := by
    have hune : (u : ZMod (2 * p + 1)) ≠ 0 :=
      fun h0 => hqu_n ((zmodEqZero_iff_dvd _ _).mp h0)
    have hflt : (u : ZMod (2 * p + 1)) ^ ((2 * p + 1) - 1) = 1 :=
      ZMod.pow_card_sub_one_eq_one hune
    rw [hq1] at hflt
    have hsq : ((u : ZMod (2 * p + 1)) ^ p) ^ 2 = 1 := by
      rw [← pow_mul, show p * 2 = 2 * p by ring]
      exact hflt
    have e : ((u : ZMod (2 * p + 1)) ^ p) ^ 2
        = (x : ZMod (2 * p + 1)) ^ 2 := by
      rw [huX]
      exact Even.neg_pow ⟨1, rfl⟩ _
    rwa [e] at hsq
  have hXpm : (x : ZMod (2 * p + 1)) = 1 ∨ (x : ZMod (2 * p + 1)) = -1 :=
    sq_eq_one_iff.mp hX2
  have hXp : (x : ZMod (2 * p + 1)) ^ p = (x : ZMod (2 * p + 1)) := by
    rcases hXpm with h1 | h1
    · rw [h1, one_pow]
    · rw [h1]
      exact hp_odd.neg_one_pow
  have htY : (t : ZMod (2 * p + 1)) ^ p = -(y : ZMod (2 * p + 1)) := by
    have h2 := congrArg (fun n : ℕ => (n : ZMod (2 * p + 1))) ht
    rw [Nat.cast_sub (le_of_lt hyz_lt), Nat.cast_pow] at h2
    rw [hZ0, zero_sub] at h2
    exact h2.symm
  have hY2 : (y : ZMod (2 * p + 1)) ^ 2 = 1 := by
    have htne : (t : ZMod (2 * p + 1)) ≠ 0 :=
      fun h0 => hqt_n ((zmodEqZero_iff_dvd _ _).mp h0)
    have hflt : (t : ZMod (2 * p + 1)) ^ ((2 * p + 1) - 1) = 1 :=
      ZMod.pow_card_sub_one_eq_one htne
    rw [hq1] at hflt
    have hsq : ((t : ZMod (2 * p + 1)) ^ p) ^ 2 = 1 := by
      rw [← pow_mul, show p * 2 = 2 * p by ring]
      exact hflt
    have e : ((t : ZMod (2 * p + 1)) ^ p) ^ 2
        = (y : ZMod (2 * p + 1)) ^ 2 := by
      rw [htY]
      exact Even.neg_pow ⟨1, rfl⟩ _
    rwa [e] at hsq
  have hYpm : (y : ZMod (2 * p + 1)) = 1 ∨ (y : ZMod (2 * p + 1)) = -1 :=
    sq_eq_one_iff.mp hY2
  have hYp : (y : ZMod (2 * p + 1)) ^ p = (y : ZMod (2 * p + 1)) := by
    rcases hYpm with h1 | h1
    · rw [h1, one_pow]
    · rw [h1]
      exact hp_odd.neg_one_pow
  have hZp0 : (z : ZMod (2 * p + 1)) ^ p = 0 := by
    rw [hZ0]
    exact zero_pow hpne
  rw [hXp, hYp, hZp0] at hcast
  have hYX : (y : ZMod (2 * p + 1)) = -(x : ZMod (2 * p + 1)) := by
    linear_combination hcast
  have hM1q : ((z ^ p / (x + y) : ℕ) : ZMod (2 * p + 1))
      = ∑ i ∈ Finset.range p, (x : ZMod (2 * p + 1)) ^ i
        * (-(y : ZMod (2 * p + 1))) ^ (p - 1 - i) := by
    have h2 := congrArg (fun z : ℤ => (z : ZMod (2 * p + 1))) hMform
    push_cast at h2
    exact h2
  have hMval : ((z ^ p / (x + y) : ℕ) : ZMod (2 * p + 1))
      = ((p : ℕ) : ZMod (2 * p + 1)) := by
    rw [hM1q]
    have hterm : ∀ i ∈ Finset.range p,
        (x : ZMod (2 * p + 1)) ^ i * (-(y : ZMod (2 * p + 1))) ^ (p - 1 - i)
          = (x : ZMod (2 * p + 1)) ^ (p - 1) := by
      intro i hi
      have hip : i + (p - 1 - i) = p - 1 := by
        have hmem := Finset.mem_range.mp hi
        omega
      have hneg : (-(y : ZMod (2 * p + 1))) = (x : ZMod (2 * p + 1)) := by
        rw [hYX, neg_neg]
      rw [hneg, ← pow_add, hip]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    have hXp1 : (x : ZMod (2 * p + 1)) ^ (p - 1) = 1 := by
      rcases hXpm with h1 | h1
      · rw [h1, one_pow]
      · rw [h1]
        exact Even.neg_one_pow heven
    rw [hXp1, mul_one]
  have hcastm : ((z ^ p / (x + y) : ℕ) : ZMod (2 * p + 1))
      = ((m1 : ℕ) : ZMod (2 * p + 1)) ^ p := by
    have h2 := congrArg (fun n : ℕ => (n : ZMod (2 * p + 1))) hm1
    rwa [Nat.cast_pow] at h2
  have hpne0 : ((p : ℕ) : ZMod (2 * p + 1)) ≠ 0 := by
    intro h0
    have hdvd := (zmodEqZero_iff_dvd _ _).mp h0
    have hle := Nat.le_of_dvd hp0 hdvd
    omega
  have hqm1 : ¬ (2 * p + 1) ∣ m1 := by
    intro hqm
    have hm10 : ((m1 : ℕ) : ZMod (2 * p + 1)) ^ p = 0 := by
      have hm10' := (zmodEqZero_iff_dvd _ _).mpr hqm
      rw [hm10']
      exact zero_pow hpne
    have hM0 : ((z ^ p / (x + y) : ℕ) : ZMod (2 * p + 1)) = 0 := by
      rw [hcastm]
      exact hm10
    rw [hMval] at hM0
    exact hpne0 hM0
  have hfin : ((p : ℕ) : ZMod (2 * p + 1)) = 1
      ∨ ((p : ℕ) : ZMod (2 * p + 1)) = -1 := by
    have hmres := powResidue (2 * p + 1) p hqprime rfl hp0 m1
    rcases hmres with h0 | h1 | hm1'
    · exfalso
      have hm10 : ((m1 : ℕ) : ZMod (2 * p + 1)) = 0 :=
        (pow_eq_zero_iff hpne).mp h0
      exact hqm1 ((zmodEqZero_iff_dvd _ _).mp hm10)
    · left
      rw [← hMval, hcastm]
      exact h1
    · right
      rw [← hMval, hcastm]
      exact hm1'
  rcases hfin with h1 | hm1'
  · have hcastp : ((p - 1 : ℕ) : ZMod (2 * p + 1)) = 0 := by
      rw [Nat.cast_sub (by omega : 1 ≤ p), h1, Nat.cast_one, sub_self]
    have hdvd : (2 * p + 1) ∣ p - 1 := (zmodEqZero_iff_dvd _ _).mp hcastp
    have hle : 2 * p + 1 ≤ p - 1 := Nat.le_of_dvd (by omega) hdvd
    omega
  · have hcastp : ((p + 1 : ℕ) : ZMod (2 * p + 1)) = 0 := by
      have e : ((p + 1 : ℕ) : ZMod (2 * p + 1))
          = ((p : ℕ) : ZMod (2 * p + 1)) + 1 := by
        rw [Nat.cast_add, Nat.cast_one]
      rw [e, hm1', neg_add_cancel]
    have hdvd : (2 * p + 1) ∣ p + 1 := (zmodEqZero_iff_dvd _ _).mp hcastp
    have hle : 2 * p + 1 ≤ p + 1 := Nat.le_of_dvd (by positivity) hdvd
    omega

/-- **Sophie Germain's theorem.** Let $p$ be an odd prime such that $2p + 1$ is also prime. If
$x$, $y$, $z$ are pairwise coprime positive integers with $x^p + y^p = z^p$, then $p$ divides
$xyz$.

Source: https://en.wikipedia.org/wiki/Sophie_Germain%27s_theorem, statement `sophie-s1`.
Proves `Wanted` entry `sophieGermain`.
-/
theorem sophieGermain (p x y z : ℕ) :
    Odd p → Nat.Prime p → Nat.Prime (2 * p + 1) →
    0 < x → 0 < y → 0 < z →
    Nat.Coprime x y → Nat.Coprime y z → Nat.Coprime x z →
    x ^ p + y ^ p = z ^ p → p ∣ x * y * z := by
  intro hp_odd hpprime hqprime hx0 hy0 hz0 hxy hyz hxz h
  by_contra hcon
  have hpx : ¬ p ∣ x := fun hd => hcon (by
    have e1 := hd.mul_right (y * z)
    have e2 : x * (y * z) = x * y * z := by ring
    rwa [e2] at e1)
  have hpy : ¬ p ∣ y := fun hd =>
    hcon ((hd.trans (dvd_mul_left y x)).mul_right z)
  have hpz : ¬ p ∣ z := fun hd => hcon (hd.mul_left (x * y))
  have hq7 : 7 ≤ 2 * p + 1 := by
    have h2 := hpprime.two_le
    have hne2 : p ≠ 2 := by
      intro hcon2
      rw [hcon2] at hp_odd
      have hodd := Nat.odd_iff.mp hp_odd
      norm_num at hodd
    omega
  have hqxyz := sgDvd x y z p (2 * p + 1) hqprime rfl hpprime.pos h hq7
  rcases hqxyz with hqx | hqy | hqz
  · exact case_q_dvd_x p x y z hp_odd hpprime hqprime hx0 hy0 hz0 hxy hyz hxz
      h hpx hpy hpz hqx
  · exact case_q_dvd_x p y x z hp_odd hpprime hqprime hy0 hx0 hz0 hxy.symm
      hxz hyz ((add_comm _ _).trans h) hpy hpx hpz hqy
  · exact case_q_dvd_z p x y z hp_odd hpprime hqprime hx0 hy0 hz0 hxy hyz hxz
      h hpx hpy hpz hqz

end MetaMathlibExt

end
