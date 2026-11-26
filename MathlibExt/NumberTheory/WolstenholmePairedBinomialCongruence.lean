/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.Binomial
public import MathlibExt.NumberTheory.HigherOrderHarmonic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Paired binomial products modulo the seventh power of a prime

The two shifted binomial coefficients pair into quadratic factors. Newton's identities
then express the first coefficients in terms of harmonic numbers.
-/

namespace MetaMathlibExt

open Finset

private lemma choose_sub_one_eq_prod (z : ℤ) (n : ℕ) :
    ((Ring.choose (z - 1) n : ℤ) : ℚ) =
      (∏ j ∈ Icc 1 n, ((z : ℚ) - j)) / n.factorial := by
  change (Int.castRingHom ℚ) (Ring.choose (z - 1) n) = _
  rw [Ring.map_choose, Ring.choose_eq_smul, smul_eq_mul, mul_comm, ← div_eq_mul_inv]
  change (descPochhammer ℤ n).smeval ((↑(z - 1) : ℚ)) / _ = _
  push_cast
  congr 1
  rw [← Polynomial.eval₂_smulOneHom_eq_smeval, Polynomial.eval₂_eq_eval_map,
    descPochhammer_map, descPochhammer_eval_eq_prod_range,
    ← Ico_add_one_right_eq_Icc, prod_Ico_eq_prod_range, Nat.add_sub_cancel]
  exact prod_congr rfl fun j _ => by push_cast; ring

private lemma paired_choose_eq_prod (p : ℕ) (α : ℤ) (hp : p.Prime) (hp11 : 11 ≤ p) :
    ((Ring.choose (α * p - 1) (p - 1) : ℤ) : ℚ) *
      ((Ring.choose ((α + 1) * p - 1) (p - 1) : ℤ) : ℚ) =
        ∏ j ∈ Icc 1 (p - 1), (1 - ((α : ℚ) * p) ^ 2 * ((j : ℚ) ^ 2)⁻¹) := by
  have hpodd := hp.odd_of_ne_two (by omega : p ≠ 2)
  have heven : Even (p - 1) := by obtain ⟨k, hk⟩ := hpodd; exact ⟨k, by omega⟩
  have hp' : p - 1 + 1 = p := by omega
  have hreflect (f : ℕ → ℚ) :
      (∏ j ∈ Icc 1 (p - 1), f (p - j)) = ∏ j ∈ Icc 1 (p - 1), f j := by
    simp only [← Ico_add_one_right_eq_Icc, hp']
    rw [prod_Ico_reflect f 1 (Nat.le_succ p), Nat.add_sub_cancel,
      show p + 1 - p = 1 by omega]
  have hfact : (∏ j ∈ Icc 1 (p - 1), (j : ℚ)) = ((p - 1).factorial : ℚ) := by
    rw [← Ico_add_one_right_eq_Icc, ← Nat.cast_prod, prod_Ico_id_eq_factorial]
  rw [choose_sub_one_eq_prod, choose_sub_one_eq_prod]
  push_cast
  rw [← hreflect (fun j => ((α : ℚ) + 1) * p - j), div_mul_div_comm, ← prod_mul_distrib,
    ← hfact, ← prod_mul_distrib, ← prod_div_distrib]
  calc
    _ = ∏ j ∈ Icc 1 (p - 1), (-1) * (1 - ((α : ℚ) * p) ^ 2 * ((j : ℚ) ^ 2)⁻¹) := by
      apply prod_congr rfl
      intro j hj
      have hj' := mem_Icc.mp hj
      rw [Nat.cast_sub (by omega : j ≤ p)]
      have hj0 : (j : ℚ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
      field_simp
      ring
    _ = _ := by
      rw [prod_mul_distrib, prod_const, Nat.card_Icc]
      have hn : p - 1 + 1 - 1 = p - 1 := by omega
      rw [hn, heven.neg_one_pow, one_mul]

private lemma prod_one_add_mul_eq_sum_esymm {ι R : Type*} [Fintype ι] [CommRing R]
    (f : ι → R) (x : R) :
    (∏ i, (1 + x * f i)) =
      ∑ k ∈ range (Fintype.card ι + 1), x ^ k * (univ.val.map f).esymm k := by
  classical
  rw [prod_one_add, powerset_card_biUnion,
    sum_biUnion ((pairwise_disjoint_powersetCard _).set_pairwise _), card_univ]
  refine sum_congr rfl fun k _ => ?_
  rw [esymm_map_val, mul_sum]
  refine sum_congr rfl fun t ht => ?_
  rw [prod_mul_distrib, prod_const, (mem_powersetCard.mp ht).2]

private lemma two_mul_esymm {ι R : Type*} [Fintype ι] [CommRing R] (f : ι → R) :
    2 * (univ.val.map f).esymm 2 = (∑ i, f i) ^ 2 - ∑ i, f i ^ 2 := by
  classical
  have h := congrArg (MvPolynomial.aeval f : MvPolynomial ι R →ₐ[R] R)
    (MvPolynomial.mul_esymm_eq_sum ι R 2)
  have h₂ : ((antidiagonal 2).filter fun a => a.1 < 2) = {(0, 2), (1, 1)} := by decide
  simp only [h₂, sum_pair (by decide : (0, 2) ≠ (1, 1)), map_add, map_mul, map_natCast, map_pow,
    map_neg, map_one, MvPolynomial.esymm_zero, MvPolynomial.esymm_one, MvPolynomial.psum,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, map_sum, MvPolynomial.aeval_X,
    pow_one, pow_zero] at h
  linear_combination h

private lemma three_mul_esymm {ι R : Type*} [Fintype ι] [CommRing R] (f : ι → R) :
    3 * (univ.val.map f).esymm 3 =
      (∑ i, f i ^ 3) - (∑ i, f i) * (∑ i, f i ^ 2) +
        (univ.val.map f).esymm 2 * (∑ i, f i) := by
  classical
  have h := congrArg (MvPolynomial.aeval f : MvPolynomial ι R →ₐ[R] R)
    (MvPolynomial.mul_esymm_eq_sum ι R 3)
  have h₃ : ((antidiagonal 3).filter fun a => a.1 < 3) = {(0, 3), (1, 2), (2, 1)} := by decide
  simp only [h₃, sum_insert (by decide : (0, 3) ∉ ({(1, 2), (2, 1)} : Finset (ℕ × ℕ))),
    sum_pair (by decide : (1, 2) ≠ (2, 1)), map_add, map_mul, map_natCast,
    map_pow, map_neg, map_one,
    MvPolynomial.esymm_zero, MvPolynomial.esymm_one, MvPolynomial.psum,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, map_sum, MvPolynomial.aeval_X,
    pow_one, pow_zero] at h
  linear_combination h

private lemma natCast_mul_inv {p n : ℕ} [Fact p.Prime] (hn : 0 < n) (hlt : n < p) :
    (n : ℤ_[p]) * (n : ℤ_[p]).inv = 1 :=
  PadicInt.mul_inv (PadicInt.norm_natCast_eq_one_iff.mpr
    (Nat.coprime_of_lt_prime hn.ne' hlt Fact.out))

private lemma coe_inv_natCast {p n : ℕ} [Fact p.Prime] (hn : 0 < n) (hlt : n < p) :
    ((n : ℤ_[p]).inv : ℚ_[p]) = (n : ℚ_[p])⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  exact congrArg (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]) (natCast_mul_inv hn hlt)

private lemma p_dvd_of_toZMod_eq_zero {p : ℕ} [Fact p.Prime] {x : ℤ_[p]}
    (h : PadicInt.toZMod x = 0) : (p : ℤ_[p]) ∣ x := by
  rwa [← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod,
    RingHom.mem_ker]

private lemma sum_inv_pow_zmod_eq_zero {p k : ℕ} [hp : Fact p.Prime]
    (hk : k ≠ 0) (hlt : k < p - 1) :
    ∑ j ∈ Icc 1 (p - 1), ((j : ZMod p) ^ k)⁻¹ = 0 := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have hi : range p = insert 0 (Icc 1 (p - 1)) := by
    ext j
    simp only [mem_range, mem_insert, mem_Icc]
    have := hp.out.pos
    omega
  have hsum : (∑ j ∈ range p, ((j : ZMod p) ^ k)⁻¹) = ∑ x : ZMod p, (x ^ k)⁻¹ := by
    refine sum_bij' (fun j _ => (j : ZMod p)) (fun x _ => x.val) ?_ ?_ ?_ ?_ ?_
    · simp
    · exact fun x _ => mem_range.mpr (ZMod.val_lt x)
    · exact fun j hj => ZMod.val_natCast_of_lt (mem_range.mp hj)
    · exact fun x _ => by rw [ZMod.natCast_val, ZMod.cast_id]
    · intros; rfl
  rw [hi, sum_insert (by simp), Nat.cast_zero, zero_pow hk, inv_zero, zero_add] at hsum
  rw [hsum]
  calc
    (∑ x : ZMod p, (x ^ k)⁻¹) = ∑ x : ZMod p, x ^ k := by
      simpa only [Equiv.inv_apply, inv_pow, Function.comp_apply] using
        Equiv.sum_comp (Equiv.inv (ZMod p)) (· ^ k)
    _ = 0 := FiniteField.sum_pow_lt_card_sub_one (ZMod p) k (by simpa only [ZMod.card] using hlt)

private abbrev HarmonicIndex (p : ℕ) := ↥(Icc 1 (p - 1))

private noncomputable def invSquare {p : ℕ} [Fact p.Prime] (j : HarmonicIndex p) : ℤ_[p] :=
  (j.val : ℤ_[p]).inv ^ 2

private noncomputable def invSquareSum (p : ℕ) [Fact p.Prime] (r : ℕ) : ℤ_[p] :=
  ∑ j : HarmonicIndex p, invSquare j ^ r

private lemma coe_invSquare {p : ℕ} [Fact p.Prime] (j : HarmonicIndex p) :
    (invSquare j : ℚ_[p]) = ((j.val : ℚ_[p]) ^ 2)⁻¹ := by
  have hj := mem_Icc.mp j.property
  rw [invSquare, PadicInt.coe_pow, coe_inv_natCast (by omega : 0 < j.val) (by omega : j.val < p),
    inv_pow]

private lemma coe_invSquareSum (p : ℕ) [Fact p.Prime] (r : ℕ) :
    (invSquareSum p r : ℚ_[p]) = (higherHarmonic (p - 1) (2 * r) : ℚ_[p]) := by
  rw [invSquareSum, higherHarmonic, PadicInt.coe_sum, Rat.cast_sum]
  simp only [PadicInt.coe_pow, coe_invSquare, ← inv_pow, ← pow_mul, one_div,
    Rat.cast_inv, Rat.cast_pow, Rat.cast_natCast]
  exact sum_coe_sort _ (fun j : ℕ => (j : ℚ_[p])⁻¹ ^ (2 * r))

private lemma toZMod_invSquareSum (p : ℕ) [Fact p.Prime] (r : ℕ) (hr : r ≠ 0)
    (hlt : 2 * r < p - 1) : PadicInt.toZMod (invSquareSum p r) = 0 := by
  have hterm (j : HarmonicIndex p) :
      PadicInt.toZMod (j.val : ℤ_[p]).inv = (j.val : ZMod p)⁻¹ := by
    have hj := mem_Icc.mp j.property
    have h := congrArg (PadicInt.toZMod : ℤ_[p] →+* ZMod p)
      (natCast_mul_inv (by omega : 0 < j.val) (by omega : j.val < p))
    exact eq_inv_of_mul_eq_one_right (by simpa only [map_mul, map_natCast, map_one] using h)
  rw [invSquareSum, map_sum]
  simp only [invSquare, map_pow, hterm, ← pow_mul]
  rw [sum_coe_sort _ (fun j : ℕ => (j : ZMod p)⁻¹ ^ (2 * r))]
  simpa only [← inv_pow] using sum_inv_pow_zmod_eq_zero (by omega) hlt

private lemma rat_congr_of_dvd {p : ℕ} [Fact p.Prime] {q : ℚ} {x : ℤ_[p]} {n : ℕ}
    (hcast : (x : ℚ_[p]) = (q : ℚ_[p])) (hdvd : (p : ℤ_[p]) ^ n ∣ x) :
    q = 0 ∨ (n : ℤ) ≤ padicValRat p q := by
  by_cases hq : q = 0
  · exact Or.inl hq
  have hx : x ≠ 0 := by
    intro h
    apply hq
    apply Rat.cast_injective (α := ℚ_[p])
    simpa only [h, PadicInt.coe_zero, Rat.cast_zero] using hcast.symm
  have hv := (PadicInt.mem_span_pow_iff_le_valuation x hx n).mp
    (Ideal.mem_span_singleton.mpr hdvd)
  right
  rw [← Padic.valuation_ratCast, ← hcast, PadicInt.valuation_coe]
  exact_mod_cast hv

private lemma paired_prod_expansion (p : ℕ) [Fact p.Prime] (hp11 : 11 ≤ p) (a : ℤ_[p]) :
    (p : ℤ_[p]) ^ 7 ∣
      (∏ j : HarmonicIndex p, (1 - (a * p) ^ 2 * invSquare j)) -
        (1 - (a * p) ^ 2 * invSquareSum p 1 +
          (a * p) ^ 4 * (2 : ℤ_[p]).inv * (invSquareSum p 1 ^ 2 - invSquareSum p 2)) := by
  classical
  let f : HarmonicIndex p → ℤ_[p] := invSquare
  let E (k : ℕ) := (univ.val.map f).esymm k
  let x : ℤ_[p] := -(a * p) ^ 2
  have hx : x = (p : ℤ_[p]) ^ 2 * (-a ^ 2) := by dsimp [x]; ring
  have h₁ : E 1 = invSquareSum p 1 := by
    have h := congrArg (MvPolynomial.aeval f : MvPolynomial (HarmonicIndex p) ℤ_[p] →ₐ[ℤ_[p]] ℤ_[p])
      (MvPolynomial.esymm_one (HarmonicIndex p) ℤ_[p])
    simpa only [MvPolynomial.aeval_esymm_eq_multiset_esymm, map_sum, MvPolynomial.aeval_X,
      invSquareSum, pow_one] using h
  have h₂ : E 2 = (2 : ℤ_[p]).inv * (invSquareSum p 1 ^ 2 - invSquareSum p 2) := by
    have he := two_mul_esymm f
    have hh : (2 : ℤ_[p]) * (2 : ℤ_[p]).inv = 1 :=
      natCast_mul_inv (n := 2) (by decide) (by omega)
    change 2 * E 2 = _ at he
    simp only [invSquareSum, pow_one]
    rw [← he, ← mul_assoc, mul_comm (2 : ℤ_[p]).inv, hh, one_mul]
  have h₃ : (p : ℤ_[p]) ∣ E 3 := by
    apply p_dvd_of_toZMod_eq_zero
    have hzero (r : ℕ) (hr1 : 1 ≤ r) (hr3 : r ≤ 3) :
        PadicInt.toZMod (invSquareSum p r) = 0 :=
      toZMod_invSquareSum p r (by omega) (by omega)
    have h1 : PadicInt.toZMod (∑ i, f i) = 0 := by
      simpa only [invSquareSum, pow_one] using hzero 1 (by decide) (by decide)
    have h2 : PadicInt.toZMod (∑ i, f i ^ 2) = 0 := hzero 2 (by decide) (by decide)
    have h3 : PadicInt.toZMod (∑ i, f i ^ 3) = 0 := hzero 3 (by decide) (by decide)
    have he : (3 : ZMod p) * PadicInt.toZMod (E 3) = 0 := by
      simpa only [map_mul, map_add, map_sub, map_ofNat, h1, h2, h3, mul_zero, sub_zero,
        add_zero] using congrArg (PadicInt.toZMod : ℤ_[p] →+* ZMod p) (three_mul_esymm f)
    have hn : (3 : ZMod p) ≠ 0 := by
      have hn' : (↑(3 : ℕ) : ZMod p) ≠ 0 := fun h =>
        Nat.not_dvd_of_pos_of_lt (by decide : 0 < 3) (by omega : 3 < p)
          ((ZMod.natCast_eq_zero_iff 3 p).mp h)
      exact hn'
    exact (mul_eq_zero.mp he).resolve_left hn
  have hc : 4 ≤ Fintype.card (HarmonicIndex p) + 1 := by
    rw [Fintype.card_coe, Nat.card_Icc]
    omega
  have hprod : (∏ j : HarmonicIndex p, (1 - (a * p) ^ 2 * invSquare j)) =
      (∑ k ∈ range 4, x ^ k * E k) +
        ∑ i ∈ range (Fintype.card (HarmonicIndex p) + 1 - 4), x ^ (4 + i) * E (4 + i) := by
    simp only [sub_eq_add_neg, ← neg_mul]
    rw [prod_one_add_mul_eq_sum_esymm]
    have hs := sum_range_add (fun k => x ^ k * E k) 4
      (Fintype.card (HarmonicIndex p) + 1 - 4)
    rwa [Nat.add_sub_of_le hc] at hs
  have hlow : (∑ k ∈ range 4, x ^ k * E k) = 1 + x * E 1 + x ^ 2 * E 2 + x ^ 3 * E 3 := by
    simp [sum_range_succ, E]
  have htail : (p : ℤ_[p]) ^ 7 ∣
      ∑ i ∈ range (Fintype.card (HarmonicIndex p) + 1 - 4), x ^ (4 + i) * E (4 + i) := by
    apply dvd_sum
    intro i _
    apply dvd_mul_of_dvd_left
    rw [hx, mul_pow, ← pow_mul]
    exact dvd_mul_of_dvd_left (pow_dvd_pow _ (by omega)) _
  have hcubic : (p : ℤ_[p]) ^ 7 ∣ x ^ 3 * E 3 := by
    obtain ⟨t, ht⟩ := h₃
    exact ⟨(-a ^ 2) ^ 3 * t, by rw [hx, ht]; ring⟩
  have hremainder := dvd_add hcubic htail
  convert hremainder using 1
  rw [hprod, hlow, h₁, h₂]
  dsimp [x]
  ring

private lemma coe_paired_prod (p : ℕ) [hp : Fact p.Prime] (hp11 : 11 ≤ p) (α : ℤ) :
    ((∏ j : HarmonicIndex p, (1 - ((α : ℤ_[p]) * p) ^ 2 * invSquare j) : ℤ_[p]) : ℚ_[p]) =
      (↑(((Ring.choose (α * p - 1) (p - 1) : ℤ) : ℚ) *
        ((Ring.choose ((α + 1) * p - 1) (p - 1) : ℤ) : ℚ)) : ℚ_[p]) := by
  rw [paired_choose_eq_prod p α hp.out hp11, Rat.cast_prod]
  change PadicInt.Coe.ringHom (∏ j : HarmonicIndex p,
    (1 - ((α : ℤ_[p]) * (p : ℤ_[p])) ^ 2 * invSquare j)) = _
  rw [map_prod]
  change (∏ j : HarmonicIndex p,
    ((1 - ((α : ℤ_[p]) * p) ^ 2 * invSquare j : ℤ_[p]) : ℚ_[p])) = _
  simp only [PadicInt.coe_sub, PadicInt.coe_one, PadicInt.coe_pow, PadicInt.coe_mul,
    PadicInt.coe_intCast, PadicInt.coe_natCast, coe_invSquare, Rat.cast_sub, Rat.cast_one,
    Rat.cast_mul, Rat.cast_pow, Rat.cast_intCast, Rat.cast_natCast, Rat.cast_inv]
  exact prod_coe_sort _ (fun j : ℕ => (1 - ((α : ℚ_[p]) * p) ^ 2 * ((j : ℚ_[p]) ^ 2)⁻¹))

private lemma inverse_expansion (p : ℕ) [Fact p.Prime] (hp11 : 11 ≤ p) (B : ℤ_[p])
    (hB : (p : ℤ_[p]) ^ 7 ∣ B - (1 - (p : ℤ_[p]) ^ 2 * invSquareSum p 1 +
      (p : ℤ_[p]) ^ 4 * (2 : ℤ_[p]).inv * (invSquareSum p 1 ^ 2 - invSquareSum p 2))) :
    B * B.inv = 1 ∧ (p : ℤ_[p]) ^ 7 ∣ B.inv - (1 + (p : ℤ_[p]) ^ 2 * invSquareSum p 1 +
      (p : ℤ_[p]) ^ 4 * (2 : ℤ_[p]).inv * (invSquareSum p 1 ^ 2 + invSquareSum p 2)) := by
  let P : ℤ_[p] := p
  let H := invSquareSum p 1
  let J := invSquareSum p 2
  let half := (2 : ℤ_[p]).inv
  let U := P ^ 2 * H
  let V := half * (H ^ 2 - J)
  let W := half * (H ^ 2 + J)
  let D := 1 + U + P ^ 4 * W
  have hh : 2 * half = 1 := natCast_mul_inv (n := 2) (by decide) (by omega)
  have hVW : V + W = H ^ 2 := by
    dsimp [V, W]
    linear_combination H ^ 2 * hh
  have hUsq : U ^ 2 = P ^ 4 * (V + W) := by rw [hVW]; dsimp [U]; ring
  obtain ⟨t, ht⟩ : P ∣ H := p_dvd_of_toZMod_eq_zero
    (toZMod_invSquareSum p 1 (by decide) (by omega))
  have hU : U = P ^ 3 * t := by dsimp only [U]; rw [ht]; ring
  obtain ⟨r, hr⟩ := hB
  have hB' : B = P ^ 7 * r + (1 - U + P ^ 4 * V) := by
    dsimp only [P, U, V, H, J, half]
    rw [sub_eq_iff_eq_add] at hr
    simpa only [mul_assoc] using hr
  have hunit : IsUnit B := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, hB']
    simp [P, U]
  have hmul := PadicInt.mul_inv (PadicInt.isUnit_iff.mp hunit)
  have hprod : P ^ 7 ∣ B * D - 1 := by
    -- The quadratic terms cancel. The cross terms have valuations at least 7 and 8.
    refine ⟨r * D + t * (V - W) + P * V * W, ?_⟩
    dsimp only [D]
    rw [hB']
    linear_combination -hUsq + P ^ 4 * (V - W) * hU
  obtain ⟨e, he⟩ := hprod
  have hdvd : P ^ 7 ∣ B.inv - D := by
    refine ⟨-B.inv * e, ?_⟩
    linear_combination -B.inv * he + D * hmul
  exact ⟨hmul, by simpa only [D, U, W, H, J, P, half, mul_assoc] using hdvd⟩

/-- **Congruences modulo $p^7$ for $\binom{\alpha p - 1}{p - 1} \binom{(\alpha + 1)p - 1}{p - 1}$
and $\binom{2p - 1}{p - 1}^{-1}$.** Let $p \ge 11$ be a prime and let $\alpha$ be an integer. For
an integer $x$ and a natural number $r$ write $\binom{x}{r} = x(x-1)\cdots(x-r+1)/r!$, let
$H_{p-1}^{(r)} = \sum_{j=1}^{p-1} 1/j^r$ be the harmonic number of order $r$, and let $v_p$ be the
$p$-adic valuation on $\mathbb{Q}$. Put
$$
X = \binom{\alpha p - 1}{p - 1} \binom{(\alpha + 1)p - 1}{p - 1} - 1 +
(\alpha p)^2 H_{p-1}^{(2)} - \frac{(\alpha p)^4}{2} \Big(\big(H_{p-1}^{(2)}\big)^2 -
H_{p-1}^{(4)}\Big)
$$
and
$$
Y = \binom{2p - 1}{p - 1}^{-1} - 1 - p^2 H_{p-1}^{(2)} -
\frac{p^4}{2} \Big(\big(H_{p-1}^{(2)}\big)^2 + H_{p-1}^{(4)}\Big).
$$
Then either $X = 0$ or $v_p(X) \ge 7$, and either $Y = 0$ or $v_p(Y) \ge 7$.

The paper allows $\alpha \in \mathbb{Z}_p$; only integers $\alpha$ are covered here.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Theorem 13
(`integers-2026-A32-thm-13`). -/
public theorem ringChoose_mul_prime_sub_one_mul_congr (p : ℕ) (α : ℤ) (hp : p.Prime)
    (hp11 : 11 ≤ p) :
    let H2 : ℚ := higherHarmonic (p - 1) 2
    let H4 : ℚ := higherHarmonic (p - 1) 4
    let A : ℚ := α * p
    let L : ℚ := ((Ring.choose (α * p - 1) (p - 1) : ℤ) : ℚ) *
      ((Ring.choose ((α + 1) * p - 1) (p - 1) : ℤ) : ℚ)
    let R : ℚ := ((2 * p - 1).choose (p - 1) : ℚ)⁻¹
    (L - (1 - A ^ 2 * H2 + A ^ 4 / 2 * (H2 ^ 2 - H4)) = 0 ∨
        7 ≤ padicValRat p (L - (1 - A ^ 2 * H2 + A ^ 4 / 2 * (H2 ^ 2 - H4)))) ∧
      (R - (1 + (p : ℚ) ^ 2 * H2 + (p : ℚ) ^ 4 / 2 * (H2 ^ 2 + H4)) = 0 ∨
        7 ≤ padicValRat p (R - (1 + (p : ℚ) ^ 2 * H2 + (p : ℚ) ^ 4 / 2 * (H2 ^ 2 + H4)))) := by
  dsimp only
  have : Fact p.Prime := ⟨hp⟩
  have hhalf : ((2 : ℤ_[p]).inv : ℚ_[p]) = (2 : ℚ_[p])⁻¹ :=
    coe_inv_natCast (n := 2) (by decide) (by omega)
  have h₂ : (invSquareSum p 1 : ℚ_[p]) = (higherHarmonic (p - 1) 2 : ℚ_[p]) :=
    coe_invSquareSum p 1
  have h₄ : (invSquareSum p 2 : ℚ_[p]) = (higherHarmonic (p - 1) 4 : ℚ_[p]) :=
    coe_invSquareSum p 2
  constructor
  · refine rat_congr_of_dvd (n := 7) ?_ (paired_prod_expansion p hp11 (α : ℤ_[p]))
    rw [PadicInt.coe_sub, coe_paired_prod p hp11 α]
    simp only [PadicInt.coe_one, PadicInt.coe_add, PadicInt.coe_sub, PadicInt.coe_mul,
      PadicInt.coe_pow, PadicInt.coe_intCast, PadicInt.coe_natCast, h₂, h₄, hhalf,
      div_eq_mul_inv, Rat.cast_sub, Rat.cast_add, Rat.cast_one, Rat.cast_mul, Rat.cast_pow,
      Rat.cast_inv, Rat.cast_ofNat, Rat.cast_intCast, Rat.cast_natCast]
  · let B : ℤ_[p] := ((2 * p - 1).choose (p - 1) : ℕ)
    have hB : (∏ j : HarmonicIndex p, (1 - (p : ℤ_[p]) ^ 2 * invSquare j)) = B := by
      apply PadicInt.ext
      have h := coe_paired_prod p hp11 1
      have hleft : (1 : ℤ) * p - 1 = ((p - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_one, one_mul]
      have hright : ((1 + 1 : ℤ) * p - 1) = ((2 * p - 1 : ℕ) : ℤ) := by
        have hp' : 1 ≤ 2 * p := by omega
        push_cast [Nat.cast_sub hp']
        ring
      rw [hleft, hright] at h
      simpa only [Int.cast_one, one_mul, Ring.choose_natCast, Int.cast_natCast,
        Nat.choose_self, Nat.cast_one, Rat.cast_natCast, Rat.cast_mul, PadicInt.coe_natCast, B]
        using h
    have hBexp := paired_prod_expansion p hp11 1
    simp only [one_mul, hB] at hBexp
    obtain ⟨hBmul, hdvd⟩ := inverse_expansion p hp11 B hBexp
    have hBinv : (B.inv : ℚ_[p]) = (B : ℚ_[p])⁻¹ :=
      eq_inv_of_mul_eq_one_right (congrArg (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]) hBmul)
    refine rat_congr_of_dvd (n := 7) ?_ hdvd
    simp only [PadicInt.coe_sub, PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_one,
      PadicInt.coe_pow, PadicInt.coe_natCast, h₂, h₄, hhalf, hBinv, div_eq_mul_inv,
      Rat.cast_sub, Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_one, Rat.cast_ofNat,
      Rat.cast_inv, Rat.cast_natCast, B]

end MetaMathlibExt
