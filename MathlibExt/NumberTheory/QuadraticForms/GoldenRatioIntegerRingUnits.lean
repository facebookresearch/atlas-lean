/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Computability.Reduce
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace MetaMathlibExt

/-! # Unit group of the quadratic integer ring Z[α] -/

private lemma sqrt5_sq : (Real.sqrt 5 : ℝ) ^ 2 = 5 :=
  Real.sq_sqrt (by norm_num)

private lemma alpha_sq : ((1 + Real.sqrt 5) / 2 : ℝ) ^ 2 = ((1 + Real.sqrt 5) / 2 : ℝ) + 1 := by
  have hs := sqrt5_sq
  nlinarith [hs]

private lemma alpha_gt_one : (1 : ℝ) < (1 + Real.sqrt 5) / 2 := by
  have h : (2 : ℝ) < Real.sqrt 5 := by
    have hs : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hnn : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    nlinarith [hs, hnn]
  linarith

private lemma alpha_lt_two : ((1 + Real.sqrt 5) / 2 : ℝ) < 2 := by
  have h : Real.sqrt 5 < (3 : ℝ) := by
    have hs : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hnn : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    nlinarith [hs, hnn]
  linarith

private lemma alpha_pos : (0 : ℝ) < (1 + Real.sqrt 5) / 2 := by
  linarith [alpha_gt_one]

private lemma alpha_ne_zero : ((1 + Real.sqrt 5) / 2 : ℝ) ≠ 0 :=
  ne_of_gt alpha_pos

private lemma alpha_mul_sub_one : ((1 + Real.sqrt 5) / 2 : ℝ) * (((1 + Real.sqrt 5) / 2 : ℝ) - 1) = 1 := by
  have hsq := alpha_sq
  nlinarith [hsq]

private lemma alpha_inv_eq : ((1 + Real.sqrt 5) / 2 : ℝ)⁻¹ = ((1 + Real.sqrt 5) / 2 : ℝ) - 1 :=
  (eq_inv_of_mul_eq_one_right alpha_mul_sub_one).symm

private lemma one_div_alpha : (1 : ℝ) / ((1 + Real.sqrt 5) / 2) = ((1 + Real.sqrt 5) / 2) - 1 := by
  rw [one_div, alpha_inv_eq]

private lemma irrational_alpha : Irrational ((1 + Real.sqrt 5) / 2 : ℝ) := by
  have h5 : Nat.Prime 5 := by norm_num
  have h := Nat.Prime.irrational_sqrt h5
  have h5' : Irrational (Real.sqrt 5) := by simpa using h
  rw [irrational_iff_ne_rational] at h5' ⊢
  intro a b hb hab
  have hbR : ((b : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hb
  have hsqrt : (Real.sqrt 5 : ℝ) = (((2 * a - b : ℤ)) : ℝ) / (((b : ℤ)) : ℝ) := by
    have h2 : (((2 * a - b : ℤ)) : ℝ) = 2 * (a : ℝ) - (b : ℝ) := by push_cast; ring
    rw [h2, eq_div_iff hbR]
    rw [eq_div_iff hbR] at hab
    linarith [hab]
  exact h5' _ _ hb hsqrt

private lemma uniq_rep (a b a' b' : ℤ)
    (h : (a : ℝ) + (b : ℝ) * ((1 + Real.sqrt 5) / 2 : ℝ)
       = (a' : ℝ) + (b' : ℝ) * ((1 + Real.sqrt 5) / 2 : ℝ)) :
    a = a' ∧ b = b' := by
  have hα := irrational_alpha
  rw [irrational_iff_ne_rational] at hα
  by_cases hb : b = b'
  · subst hb
    have ha : (a : ℝ) = (a' : ℝ) := by linarith [h]
    have : a = a' := by exact_mod_cast ha
    exact ⟨this, rfl⟩
  · exfalso
    have hbb : b - b' ≠ 0 := sub_ne_zero.mpr hb
    have hbbR : (((b - b' : ℤ)) : ℝ) ≠ 0 := by exact_mod_cast hbb
    have heq : ((1 + Real.sqrt 5) / 2 : ℝ) = ((a' - a : ℤ) : ℝ) / (((b - b' : ℤ)) : ℝ) := by
      have h3 : (((b - b' : ℤ)) : ℝ) * ((1 + Real.sqrt 5) / 2) = (((a' - a : ℤ)) : ℝ) := by
        push_cast
        linarith [h]
      rw [eq_div_iff hbbR]
      linarith [h3]
    exact hα (a' - a) (b - b') hbb heq

private lemma mul_rep (a1 b1 a2 b2 : ℤ) :
    ((a1 : ℝ) + (b1 : ℝ) * ((1 + Real.sqrt 5) / 2)) * ((a2 : ℝ) + (b2 : ℝ) * ((1 + Real.sqrt 5) / 2))
      = (((a1 * a2 + b1 * b2 : ℤ)) : ℝ) + (((a1 * b2 + a2 * b1 + b1 * b2 : ℤ))) * ((1 + Real.sqrt 5) / 2) := by
  have hsq := alpha_sq
  push_cast
  linear_combination ((b1 : ℝ) * (b2 : ℝ)) * hsq

private lemma norm_mul (a1 b1 a2 b2 : ℤ) :
    (a1 * a2 + b1 * b2) ^ 2 + (a1 * a2 + b1 * b2) * (a1 * b2 + a2 * b1 + b1 * b2)
      - (a1 * b2 + a2 * b1 + b1 * b2) ^ 2
    = (a1 ^ 2 + a1 * b1 - b1 ^ 2) * (a2 ^ 2 + a2 * b2 - b2 ^ 2) := by
  ring

private lemma norm_rep (a b : ℤ) :
    ((a : ℝ) + (b : ℝ) * ((1 + Real.sqrt 5) / 2 : ℝ)) *
    ((a : ℝ) + (b : ℝ) * ((1 - Real.sqrt 5) / 2 : ℝ))
    = (((a ^ 2 + a * b - b ^ 2 : ℤ)) : ℝ) := by
  have hs := sqrt5_sq
  push_cast
  nlinarith [hs]

private lemma trace_rep (a b : ℤ) :
    ((a : ℝ) + (b : ℝ) * ((1 + Real.sqrt 5) / 2 : ℝ)) +
    ((a : ℝ) + (b : ℝ) * ((1 - Real.sqrt 5) / 2 : ℝ))
    = (((2 * a + b : ℤ)) : ℝ) := by
  push_cast
  ring

private lemma alpha_mem_R :
    ((1 + Real.sqrt 5) / 2 : ℝ) ∈ Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ) :=
  Algebra.subset_adjoin rfl

private lemma alpha_sub_one_mem_R :
    (((1 + Real.sqrt 5) / 2 : ℝ) - 1) ∈ Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ) :=
  Subalgebra.sub_mem _ alpha_mem_R (Subalgebra.one_mem _)

private lemma pow_mem_R (n : ℕ) :
    (((1 + Real.sqrt 5) / 2 : ℝ) ^ n) ∈ Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have : ((1 + Real.sqrt 5) / 2 : ℝ) ^ (k + 1) = ((1 + Real.sqrt 5) / 2 : ℝ) ^ k * ((1 + Real.sqrt 5) / 2) := by ring
    rw [this]
    exact Subalgebra.mul_mem _ ih alpha_mem_R

private lemma inv_pow_mem_R (n : ℕ) :
    ((((1 + Real.sqrt 5) / 2 : ℝ) - 1) ^ n) ∈ Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have : ((((1 + Real.sqrt 5) / 2 : ℝ) - 1) ^ (k + 1)) = ((((1 + Real.sqrt 5) / 2 : ℝ) - 1) ^ k) * ((((1 + Real.sqrt 5) / 2 : ℝ) - 1)) := by ring
    rw [this]
    exact Subalgebra.mul_mem _ ih alpha_sub_one_mem_R

private lemma zpow_mem_R (n : ℤ) :
    (((1 + Real.sqrt 5) / 2 : ℝ) ^ n) ∈ Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ) := by
  by_cases h : 0 ≤ n
  · have hn : n = ((n.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg h).symm
    rw [hn, zpow_natCast]
    exact pow_mem_R _
  · have hlt : n < 0 := lt_of_not_ge h
    have h2 : 0 ≤ -n := le_of_lt (neg_pos.mpr hlt)
    have hn : n = -(((-n).toNat : ℕ) : ℤ) := by
      have h3 : -n = (((-n).toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg h2).symm
      omega
    have hpow : (((1 + Real.sqrt 5) / 2 : ℝ) ^ n) = ((((1 + Real.sqrt 5) / 2 : ℝ) - 1) ^ ((-n).toNat : ℕ)) := by
      conv_lhs => rw [hn, zpow_neg, zpow_natCast, ← inv_pow, alpha_inv_eq]
    rw [hpow]
    exact inv_pow_mem_R _

private lemma exists_rep_of_mem (x : ℝ)
    (hx : x ∈ Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) :
    ∃ a b : ℤ, x = (a : ℝ) + (b : ℝ) * ((1 + Real.sqrt 5) / 2 : ℝ) := by
  refine Algebra.adjoin_induction (p := fun x _ => ∃ a b : ℤ, x = (a : ℝ) + (b : ℝ) * ((1 + Real.sqrt 5) / 2 : ℝ)) ?_ ?_ ?_ ?_ hx
  · intro y hy
    simp at hy
    subst hy
    exact ⟨0, 1, by simp⟩
  · intro r
    exact ⟨r, 0, by simp⟩
  · intro y z _ _ ihy ihz
    obtain ⟨a1, b1, rfl⟩ := ihy
    obtain ⟨a2, b2, rfl⟩ := ihz
    refine ⟨a1 + a2, b1 + b2, ?_⟩
    push_cast
    ring
  · intro y z _ _ ihy ihz
    obtain ⟨a1, b1, rfl⟩ := ihy
    obtain ⟨a2, b2, rfl⟩ := ihz
    refine ⟨a1 * a2 + b1 * b2, a1 * b2 + a2 * b1 + b1 * b2, ?_⟩
    exact mul_rep a1 b1 a2 b2

private lemma exists_unit_pow (n : ℤ) :
    ∃ u : (Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))ˣ,
      ((u : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) : ℝ) = ((1 + Real.sqrt 5) / 2 : ℝ) ^ n := by
  let R := Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)
  have hr : (((1 + Real.sqrt 5) / 2 : ℝ) ^ n) ∈ R := zpow_mem_R n
  have hs : (((1 + Real.sqrt 5) / 2 : ℝ) ^ (-n)) ∈ R := zpow_mem_R (-n)
  let r : R := ⟨(((1 + Real.sqrt 5) / 2 : ℝ) ^ n), hr⟩
  let s : R := ⟨(((1 + Real.sqrt 5) / 2 : ℝ) ^ (-n)), hs⟩
  have hrs : r * s = 1 := by
    ext
    show ((r * s : R) : ℝ) = ((1 : R) : ℝ)
    have h1 : ((r * s : R) : ℝ) = (((1 + Real.sqrt 5) / 2 : ℝ) ^ n) * (((1 + Real.sqrt 5) / 2 : ℝ) ^ (-n)) := by
      simp [r, s]
    have h2 : (((1 : R)) : ℝ) = 1 := Subalgebra.coe_one R
    rw [h1, h2, ← zpow_add₀ alpha_ne_zero]
    simp
  have hsr : s * r = 1 := by rw [mul_comm]; exact hrs
  exact ⟨Units.mk r s hrs hsr, rfl⟩

private lemma exists_unit_neg_pow (n : ℤ) :
    ∃ u : (Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))ˣ,
      ((u : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) : ℝ) = -(((1 + Real.sqrt 5) / 2 : ℝ) ^ n) := by
  obtain ⟨w, hw⟩ := exists_unit_pow n
  let R := Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)
  let r : R := ⟨-(((1 + Real.sqrt 5) / 2 : ℝ) ^ n), by
    have hmem : (((1 + Real.sqrt 5) / 2 : ℝ) ^ n) ∈ R := zpow_mem_R n
    have := Subalgebra.neg_mem R hmem
    simpa using this⟩
  have hr_coe : ((r : R) : ℝ) = -(((1 + Real.sqrt 5) / 2 : ℝ) ^ n) := rfl
  -- inverse is -((α^n)⁻¹) = image of -w⁻¹
  have hs_mem : (-(((1 + Real.sqrt 5) / 2 : ℝ) ^ (-n))) ∈ R := by
    have hmem : (((1 + Real.sqrt 5) / 2 : ℝ) ^ (-n)) ∈ R := zpow_mem_R (-n)
    have := Subalgebra.neg_mem R hmem
    simpa using this
  let s : R := ⟨-(((1 + Real.sqrt 5) / 2 : ℝ) ^ (-n)), hs_mem⟩
  have hrs : r * s = 1 := by
    ext
    show ((r * s : R) : ℝ) = ((1 : R) : ℝ)
    have h1 : ((r * s : R) : ℝ) = (-(((1 + Real.sqrt 5) / 2 : ℝ) ^ n)) * (-(((1 + Real.sqrt 5) / 2 : ℝ) ^ (-n))) := by
      simp [r, s]
    have h2 : (((1 : R)) : ℝ) = 1 := Subalgebra.coe_one R
    rw [h1, h2, neg_mul_neg, ← zpow_add₀ alpha_ne_zero]
    simp
  have hsr : s * r = 1 := by rw [mul_comm]; exact hrs
  exact ⟨Units.mk r s hrs hsr, rfl⟩

private lemma unit_norm (u : (Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))ˣ)
    (a b : ℤ)
    (hrep : ((u : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) : ℝ) = (a : ℝ) + (b : ℝ) * ((1 + Real.sqrt 5) / 2 : ℝ)) :
    a ^ 2 + a * b - b ^ 2 = 1 ∨ a ^ 2 + a * b - b ^ 2 = -1 := by
  have hinv_mem : (((u⁻¹ : (Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))ˣ) : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) : ℝ) ∈ Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ) :=
    (((u⁻¹ : (Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))ˣ) : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))).property
  obtain ⟨c, d, hcd⟩ := exists_rep_of_mem _ hinv_mem
  have hRs : (u : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) * (((u⁻¹ : (Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))ˣ) : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))) = 1 :=
    u.mul_inv
  have hR := congrArg (fun x : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ) => (x : ℝ)) hRs
  rw [Subalgebra.coe_mul, Subalgebra.coe_one] at hR
  rw [hrep, hcd] at hR
  have hprod2 : ((a : ℝ) + (b : ℝ) * ((1 + Real.sqrt 5) / 2)) * ((c : ℝ) + (d : ℝ) * ((1 + Real.sqrt 5) / 2))
      = ((1 : ℤ) : ℝ) + ((0 : ℤ) : ℝ) * ((1 + Real.sqrt 5) / 2) := by
    simpa using hR
  have hmul := mul_rep a b c d
  rw [hmul] at hprod2
  have huniq := uniq_rep _ _ 1 0 hprod2
  obtain ⟨h1, h2⟩ := huniq
  have hnorm2 : (a * c + b * d) ^ 2 + (a * c + b * d) * (a * d + c * b + b * d) - (a * d + c * b + b * d) ^ 2
      = (a ^ 2 + a * b - b ^ 2) * (c ^ 2 + c * d - d ^ 2) := by ring
  have hN : (a ^ 2 + a * b - b ^ 2) * (c ^ 2 + c * d - d ^ 2) = 1 := by
    have h0 : (a * c + b * d) ^ 2 + (a * c + b * d) * (a * d + c * b + b * d) - (a * d + c * b + b * d) ^ 2 = 1 := by
      rw [h1, h2]
      norm_num
    rw [← hnorm2]
    exact h0
  have hcase := Int.eq_one_or_neg_one_of_mul_eq_one hN
  rcases hcase with h | h
  · left
    exact h
  · right
    exact h

private lemma no_unit_in_interval (a b : ℤ)
    (hv1 : (1 : ℝ) ≤ (a : ℝ) + (b : ℝ) * ((1 + Real.sqrt 5) / 2 : ℝ))
    (hv2 : (a : ℝ) + (b : ℝ) * ((1 + Real.sqrt 5) / 2 : ℝ) < (1 + Real.sqrt 5) / 2)
    (hnorm : a ^ 2 + a * b - b ^ 2 = 1 ∨ a ^ 2 + a * b - b ^ 2 = -1) :
    (a : ℝ) + (b : ℝ) * ((1 + Real.sqrt 5) / 2 : ℝ) = 1 := by
  set v : ℝ := (a : ℝ) + (b : ℝ) * ((1 + Real.sqrt 5) / 2 : ℝ) with hv
  set vp : ℝ := (a : ℝ) + (b : ℝ) * ((1 - Real.sqrt 5) / 2 : ℝ) with hvp
  have hmul : v * vp = (((a ^ 2 + a * b - b ^ 2 : ℤ)) : ℝ) := norm_rep a b
  have hadd : v + vp = (((2 * a + b : ℤ)) : ℝ) := trace_rep a b
  have hvpos : (0 : ℝ) < v := lt_of_lt_of_le (by norm_num) hv1
  have hvne : v ≠ 0 := ne_of_gt hvpos
  rcases hnorm with hN | hN
  · have hN1 : (((a ^ 2 + a * b - b ^ 2 : ℤ)) : ℝ) = 1 := by rw [hN]; norm_num
    rw [hN1] at hmul
    have hcomm : vp * v = 1 := by rw [mul_comm]; exact hmul
    have hvp_eq : vp = 1 / v := eq_div_of_mul_eq hvne hcomm
    have hvp_pos : (0 : ℝ) < vp := by rw [hvp_eq]; exact div_pos (by norm_num) hvpos
    have hvp_le : vp ≤ 1 := by
      rw [hvp_eq, div_le_one hvpos]
      exact hv1
    have ht_gt : (1 : ℝ) < v + vp := by linarith
    have ht_lt : v + vp < 3 := by linarith [hv2, hvp_le, alpha_lt_two]
    have ht_eq : (2 * a + b) = 2 := by
      have h1 : (1 : ℝ) < (((2 * a + b : ℤ)) : ℝ) := by rw [← hadd]; exact ht_gt
      have h2 : (((2 * a + b : ℤ)) : ℝ) < 3 := by rw [← hadd]; exact ht_lt
      have h1c : (1 : ℤ) < 2 * a + b := by exact_mod_cast h1
      have h2c : (2 * a + b : ℤ) < 3 := by exact_mod_cast h2
      omega
    have hsum : v + 1 / v = 2 := by
      have htr : v + vp = (((2 * a + b : ℤ)) : ℝ) := hadd
      rw [ht_eq] at htr
      norm_num at htr
      rw [hvp_eq] at htr
      linarith
    have hv_eq : v = 1 := by
      have hsq2 : (v - 1) ^ 2 = 0 := by
        have hvm : v * (v + 1 / v - 2) = 0 := by
          field_simp
          nlinarith [hsum]
        have hexpand : (v - 1) ^ 2 = v * (v + 1 / v - 2) := by
          field_simp
          ring
        rw [hexpand, hvm]
      have hzero : v - 1 = 0 := pow_eq_zero_iff (by norm_num) |>.mp hsq2
      linarith
    exact hv_eq
  · have hN1 : (((a ^ 2 + a * b - b ^ 2 : ℤ)) : ℝ) = -1 := by rw [hN]; norm_num
    rw [hN1] at hmul
    have hcomm : vp * v = -1 := by rw [mul_comm]; exact hmul
    have hvp_eq : vp = -1 / v := eq_div_of_mul_eq hvne hcomm
    have hvp_neg : vp < 0 := by
      have hpos : (0 : ℝ) < 1 / v := div_pos (by norm_num) hvpos
      have hneg : (-1 : ℝ) / v = -(1 / v) := by rw [neg_div]
      rw [hneg] at hvp_eq
      linarith [hvp_eq, hpos]
    have hle : (1 : ℝ) / v ≤ 1 := by
      rw [div_le_one hvpos]
      exact hv1
    have hvp_ge : (-1 : ℝ) ≤ vp := by
      have hneg : (-1 : ℝ) / v = -(1 / v) := by rw [neg_div]
      rw [hneg] at hvp_eq
      linarith [hvp_eq, hle]
    have ht_ge : (0 : ℝ) ≤ v + vp := by linarith [hv1, hvp_ge]
    have ht_lt : v + vp < 1 := by
      have hdiv_lt : (1 : ℝ) / ((1 + Real.sqrt 5) / 2) < 1 / v :=
        one_div_lt_one_div_of_lt hvpos hv2
      have h1α := one_div_alpha
      have hneg : (-1 : ℝ) / v = -(1 / v) := by rw [neg_div]
      have hvp_lt : vp < -(((1 + Real.sqrt 5) / 2) - 1) := by
        rw [hvp_eq, hneg]
        have : -(1 / v) < -((1 : ℝ) / ((1 + Real.sqrt 5) / 2)) := by linarith [hdiv_lt]
        rw [h1α] at this
        linarith [this]
      linarith [hv2, hvp_lt]
    have ht_eq : (2 * a + b) = 0 := by
      have h1 : (0 : ℝ) ≤ (((2 * a + b : ℤ)) : ℝ) := by rw [← hadd]; exact ht_ge
      have h2 : (((2 * a + b : ℤ)) : ℝ) < 1 := by rw [← hadd]; exact ht_lt
      have h1c : (0 : ℤ) ≤ 2 * a + b := by exact_mod_cast h1
      have h2c : (2 * a + b : ℤ) < 1 := by exact_mod_cast h2
      omega
    have hv_sq : v ^ 2 = 1 := by
      have htr : v + vp = (((2 * a + b : ℤ)) : ℝ) := hadd
      rw [ht_eq] at htr
      norm_num at htr
      have hvp_zero : vp = -v := by linarith [htr]
      have hmul2 : v * vp = -1 := hmul
      rw [hvp_zero] at hmul2
      nlinarith [hmul2]
    have hv_eq : v = 1 := by
      have hfac : (v - 1) * (v + 1) = 0 := by nlinarith [hv_sq]
      have hor : v - 1 = 0 ∨ v + 1 = 0 := mul_eq_zero.mp hfac
      rcases hor with h | h
      · linarith
      · have : v = -1 := by linarith
        linarith [hvpos, this]
    exact hv_eq

private lemma log_sandwich (y : ℝ) (hy : (0 : ℝ) < y) :
    ∃ n : ℤ, ((1 + Real.sqrt 5) / 2 : ℝ) ^ n ≤ y ∧ y < ((1 + Real.sqrt 5) / 2 : ℝ) ^ (n + 1) := by
  have hLpos : (0 : ℝ) < Real.log ((1 + Real.sqrt 5) / 2) := Real.log_pos alpha_gt_one
  set L : ℝ := Real.log ((1 + Real.sqrt 5) / 2) with hL
  set t : ℝ := Real.log y / L with ht
  set n : ℤ := ⌊t⌋ with hn
  have hn1 : ((n : ℤ) : ℝ) ≤ t := Int.floor_le t
  have hn2 : t < ((n : ℤ) : ℝ) + 1 := Int.lt_floor_add_one t
  have hle : ((n : ℤ) : ℝ) * L ≤ Real.log y := by
    rw [ht] at hn1
    have h := (le_div_iff₀ hLpos).mp hn1
    linarith [h]
  have hlt : Real.log y < ((((n : ℤ) : ℝ)) + 1) * L := by
    rw [ht] at hn2
    have h := (div_lt_iff₀ hLpos).mp hn2
    linarith [h]
  have hexp_le : Real.exp (((n : ℤ) : ℝ) * L) ≤ y := by
    have h := Real.exp_le_exp.mpr hle
    rwa [Real.exp_log hy] at h
  have hexp_lt : y < Real.exp ((((n : ℤ) : ℝ) + 1) * L) := by
    have h := Real.exp_lt_exp.mpr hlt
    rwa [Real.exp_log hy] at h
  have hpow_n : Real.exp (((n : ℤ) : ℝ) * L) = ((1 + Real.sqrt 5) / 2 : ℝ) ^ n := by
    have hlog : Real.log ((((1 + Real.sqrt 5) / 2 : ℝ) ^ n)) = ((n : ℤ) : ℝ) * L := by
      rw [Real.log_zpow]
    have hpos : (0 : ℝ) < (((1 + Real.sqrt 5) / 2 : ℝ) ^ n) := zpow_pos alpha_pos n
    have hexp := Real.exp_log hpos
    rw [hlog] at hexp
    exact hexp
  have hpow_n1 : Real.exp ((((n : ℤ) : ℝ) + 1) * L) = ((1 + Real.sqrt 5) / 2 : ℝ) ^ (n + 1) := by
    have hlog : Real.log ((((1 + Real.sqrt 5) / 2 : ℝ) ^ (n + 1))) = ((((n + 1 : ℤ)) : ℝ)) * L := by
      rw [Real.log_zpow]
    have hcast : ((((n + 1 : ℤ)) : ℝ)) = ((n : ℤ) : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hlog
    have hpos : (0 : ℝ) < (((1 + Real.sqrt 5) / 2 : ℝ) ^ (n + 1)) := zpow_pos alpha_pos (n + 1)
    have hexp := Real.exp_log hpos
    rw [hlog] at hexp
    exact hexp
  rw [hpow_n] at hexp_le
  rw [hpow_n1] at hexp_lt
  exact ⟨n, hexp_le, hexp_lt⟩

private lemma pos_unit_eq_pow (u : (Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))ˣ)
    (hypos : (0 : ℝ) < ((u : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) : ℝ)) :
    ∃ n : ℤ, ((u : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) : ℝ) = ((1 + Real.sqrt 5) / 2 : ℝ) ^ n := by
  set y : ℝ := ((u : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) : ℝ) with hy
  obtain ⟨n, hle, hlt⟩ := log_sandwich y hypos
  have hαpos_n : (0 : ℝ) < (((1 + Real.sqrt 5) / 2 : ℝ) ^ n) := zpow_pos alpha_pos n
  have hαne_n : (((1 + Real.sqrt 5) / 2 : ℝ) ^ n) ≠ 0 := ne_of_gt hαpos_n
  -- v = y / α^n satisfies 1 ≤ v < α
  set v : ℝ := y / (((1 + Real.sqrt 5) / 2 : ℝ) ^ n) with hvdef
  have hv1 : (1 : ℝ) ≤ v := by
    rw [hvdef, le_div_iff₀ hαpos_n]
    linarith [hle]
    -- 1 * α^n ≤ y ↔ α^n ≤ y
  have hpow_succ : (((1 + Real.sqrt 5) / 2 : ℝ) ^ (n + 1)) = (((1 + Real.sqrt 5) / 2 : ℝ) ^ n) * ((1 + Real.sqrt 5) / 2) :=
    zpow_add_one₀ alpha_ne_zero n
  have hv2 : v < (1 + Real.sqrt 5) / 2 := by
    rw [hvdef, div_lt_iff₀ hαpos_n]
    rw [hpow_succ] at hlt
    linarith [hlt]
  -- v is a unit image: v = y * (α^n)⁻¹
  obtain ⟨w, hw⟩ := exists_unit_pow n
  -- w has image α^n; w⁻¹ has image (α^n)⁻¹
  have hw_inv_image : (((w⁻¹ : (Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))ˣ) : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) : ℝ) = ((((1 + Real.sqrt 5) / 2 : ℝ) ^ n)⁻¹) := by
    have hprod : (((w : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) : ℝ)) * (((((w⁻¹ : (Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))ˣ) : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))) : ℝ)) = 1 := by
      have hRs : (w : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) * (((w⁻¹ : (Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))ˣ) : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))) = 1 :=
        w.mul_inv
      have hR := congrArg (fun x : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ) => (x : ℝ)) hRs
      rw [Subalgebra.coe_mul, Subalgebra.coe_one] at hR
      exact hR
    rw [hw] at hprod
    have h := eq_inv_of_mul_eq_one_left hprod
    -- h : ((w⁻¹..):ℝ)⁻¹ = α^n? Actually eq_inv_of_mul_eq_one_left: a*b=1 → b⁻¹=a? Here a=α^n, b=... gives b⁻¹=α^n → b=(α^n)⁻¹?
    -- hprod : α^n * X = 1 → X⁻¹ = α^n (by inv_eq_of_mul_eq_one_left?) Let's use eq_inv_of_mul_eq_one_right instead:
    -- α^n * X = 1 → X = (α^n)⁻¹
    have h2 : (((((w⁻¹ : (Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))ˣ) : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))) : ℝ)) = ((((1 + Real.sqrt 5) / 2 : ℝ) ^ n)⁻¹) :=
      eq_inv_of_mul_eq_one_right hprod
    exact h2
  -- v = image of u * w⁻¹
  have huv : ∃ uw : (Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))ˣ,
      ((uw : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) : ℝ) = v := by
    refine ⟨u * w⁻¹, ?_⟩
    have hval : (((u * w⁻¹ : (Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))ˣ) : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) : ℝ)
        = ((u : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) : ℝ) * (((((w⁻¹ : (Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))ˣ) : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))) : ℝ)) := by
      have h1 : (((u * w⁻¹ : (Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))ˣ) : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)))
          = (u : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) * (((w⁻¹ : (Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))ˣ) : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))) := by
        simp [Units.val_mul]
      have hR := congrArg (fun x : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ) => (x : ℝ)) h1
      rw [Subalgebra.coe_mul] at hR
      exact hR
    rw [hval, hw_inv_image]
    simp [hvdef, hy, div_eq_mul_inv]
  obtain ⟨uw, huw⟩ := huv
  -- v ∈ R, get rep
  have hv_mem : v ∈ Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ) :=
    huw ▸ (((uw : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))).property)
  -- rewrite huw to match? huw : ((uw..):ℝ) = v, so v = ...; need rep for v
  have huw_symm : v = ((uw : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) : ℝ) := huw.symm
  obtain ⟨a, b, hab⟩ := exists_rep_of_mem v hv_mem
  -- norm of v is ±1
  have hnorm : a ^ 2 + a * b - b ^ 2 = 1 ∨ a ^ 2 + a * b - b ^ 2 = -1 := by
    have hrep : ((uw : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) : ℝ) = (a : ℝ) + (b : ℝ) * ((1 + Real.sqrt 5) / 2 : ℝ) := by
      rw [← huw_symm]
      exact hab
    exact unit_norm uw a b hrep
  have hab2 : (a : ℝ) + (b : ℝ) * ((1 + Real.sqrt 5) / 2 : ℝ) = 1 := by
      have hv1a : (1 : ℝ) ≤ (a : ℝ) + (b : ℝ) * ((1 + Real.sqrt 5) / 2 : ℝ) := hab ▸ hv1
      have hv2a : (a : ℝ) + (b : ℝ) * ((1 + Real.sqrt 5) / 2 : ℝ) < (1 + Real.sqrt 5) / 2 := hab ▸ hv2
      exact no_unit_in_interval a b hv1a hv2a hnorm
  have hv_eq_one : v = 1 := hab.trans hab2
  -- y / α^n = 1 → y = α^n
  have hy_eq : y / (((1 + Real.sqrt 5) / 2 : ℝ) ^ n) = 1 := by rw [← hvdef]; exact hv_eq_one
  have hy_eq2 : y = (((1 + Real.sqrt 5) / 2 : ℝ) ^ n) := by
    have h := (div_eq_one_iff_eq hαne_n).mp hy_eq
    exact h
  rw [hy] at hy_eq2
  exact ⟨n, hy_eq2⟩

/-- **Units of the ring generated by the golden ratio.** Let $\alpha = (1 + \sqrt{5})/2$ and
let $\mathbb{Z}[\alpha]$ be the subring of $\mathbb{R}$ generated by $\alpha$. A real number is
a unit of $\mathbb{Z}[\alpha]$ if and only if it equals $\alpha^n$ or $-\alpha^n$ for some
integer $n$.

Source: Bahar Demirtürk and Refik Keskin, "Integer Solutions of Some
Diophantine Equations via Fibonacci and Lucas Numbers," Journal of Integer
Sequences 12 (2009), Article 09.8.7, Theorem 1.1 (label t:1.1),
lines 160–167,
https://cs.uwaterloo.ca/journals/JIS/VOL12/Demirturk/demirturk3.tex
Proves `Wanted` entry `golden_ratio_integer_ring_units`.
-/
theorem golden_ratio_integer_ring_units :
    let α : ℝ := (1 + Real.sqrt 5) / 2
    let R := Algebra.adjoin ℤ ({α} : Set ℝ)
    Set.range (fun u : Rˣ => ((u : R) : ℝ)) =
      {x : ℝ | ∃ n : ℤ, x = α ^ n ∨ x = -(α ^ n)} := by
  intro α R
  have hα : α = ((1 + Real.sqrt 5) / 2 : ℝ) := rfl
  have hR : R = Algebra.adjoin ℤ ({((1 + Real.sqrt 5) / 2 : ℝ)} : Set ℝ) := rfl
  rw [hR, hα]
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    -- x = ((u:R):ℝ), need ∃ n, ...
    have hprod : ((u : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) : ℝ) * (((((u⁻¹ : (Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))ˣ) : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))) : ℝ)) = 1 := by
      have hRs : (u : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) * (((u⁻¹ : (Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))ˣ) : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))) = 1 :=
        u.mul_inv
      have hR := congrArg (fun x : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ) => (x : ℝ)) hRs
      rw [Subalgebra.coe_mul, Subalgebra.coe_one] at hR
      exact hR
    have hx_ne : ((u : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) : ℝ) ≠ 0 :=
      left_ne_zero_of_mul_eq_one hprod
    rcases lt_or_gt_of_ne hx_ne with hneg | hpos
    · -- x < 0: -x > 0 is a unit image
      have hpos_neg : (0 : ℝ) < -((u : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) : ℝ) := by linarith [hneg]
      -- construct neg unit
      have hmem_neg : (-((u : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) : ℝ)) ∈ Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ) := by
        have hmem : ((u : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) : ℝ) ∈ Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ) :=
          (u : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)).property
        exact Subalgebra.neg_mem _ hmem
      -- build unit with image -x via -r, -s
      have hmem_inv : (((((u⁻¹ : (Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))ˣ) : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))) : ℝ)) ∈ Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ) :=
        (((u⁻¹ : (Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))ˣ) : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))).property
      let r : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ) := ⟨-((u : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) : ℝ), hmem_neg⟩
      let s : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ) := ⟨-((((u⁻¹ : (Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))ˣ) : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))) : ℝ),
        Subalgebra.neg_mem _ hmem_inv⟩
      have hrs : r * s = 1 := by
        ext
        show ((r * s : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) : ℝ) = ((1 : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) : ℝ)
        have h1 : ((r * s : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) : ℝ) = (-((u : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) : ℝ)) * (-((((u⁻¹ : (Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))ˣ) : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))) : ℝ)) := by
          simp [r, s]
        have h2 : (((1 : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))) : ℝ) = 1 := Subalgebra.coe_one _
        rw [h1, h2, neg_mul_neg]
        exact hprod
      have hsr : s * r = 1 := by rw [mul_comm]; exact hrs
      let uneg : (Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ))ˣ := Units.mk r s hrs hsr
      have huneg_coe : ((uneg : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) : ℝ) = -((u : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) : ℝ) := rfl
      have huneg_pos : (0 : ℝ) < ((uneg : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) : ℝ) := by
        rw [huneg_coe]; exact hpos_neg
      obtain ⟨n, hn⟩ := pos_unit_eq_pow uneg huneg_pos
      refine ⟨n, Or.inr ?_⟩
      have hx_eq : ((u : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) : ℝ) = -(((1 + Real.sqrt 5) / 2 : ℝ) ^ n) := by
        have : ((uneg : Algebra.adjoin ℤ ({(1 + Real.sqrt 5) / 2} : Set ℝ)) : ℝ) = (((1 + Real.sqrt 5) / 2 : ℝ) ^ n) := hn
        rw [huneg_coe] at this
        linarith [this]
      exact hx_eq
    · -- 0 < x: directly positive
      obtain ⟨n, hn⟩ := pos_unit_eq_pow u hpos
      exact ⟨n, Or.inl hn⟩
  · rintro ⟨n, h | h⟩
    · subst h
      obtain ⟨u, hu⟩ := exists_unit_pow n
      exact ⟨u, hu⟩
      -- range membership: ∃ u, ((u:R):ℝ) = α^n; hu : ((u:R):ℝ)=α^n, need ((u:R):ℝ)=x where x=α^n? After subst, x=α^n, so ⟨u, hu.symm⟩? Actually ⟨u, hu⟩? Set.range: x ∈ range ↔ ∃ u, f u = x. Here f u = ((u:R):ℝ), x=α^n, hu: f u = α^n = x, so ⟨u, hu⟩.
      -- hu.symm vs hu? f u = x is hu (since x=α^n after subst? subst replaces x with α^n, goal becomes α^n ∈ range, i.e., ∃ u, f u = α^n, so ⟨u, hu⟩.
    · subst h
      obtain ⟨u, hu⟩ := exists_unit_neg_pow n
      exact ⟨u, hu⟩

end MetaMathlibExt
