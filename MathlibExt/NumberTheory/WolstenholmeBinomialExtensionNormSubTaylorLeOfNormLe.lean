/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.NatInt
public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log

/-!
# Higher `p`-adic mean value theorem

This module proves the higher `p`-adic mean value theorem
`MetaMathlibExt.norm_sub_taylor_le_of_norm_le`, which bounds the remainder of a
Taylor expansion of a polynomial with coefficients in an ultrametric normed
space over `ℚ_[p]`.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Theorem 1.
-/

namespace MetaMathlibExt

private theorem add_succ_lt_pow (p d : ℕ) (hp2 : 2 ≤ p) : p + (d + 1) < p ^ (d + 2) := by
  induction d with
  | zero =>
    have h1 : p + 1 < p + p := by omega
    have h2 : p + p ≤ p * p := by
      have h : 2 * p ≤ p * p := Nat.mul_le_mul_right p hp2
      simpa [two_mul] using h
    have h3 : p * p = p ^ 2 := by ring
    simp only [Nat.zero_add]
    calc p + 1 < p + p := h1
      _ ≤ p * p := h2
      _ = p ^ 2 := h3
  | succ d ih =>
    have e1 : d + 1 + 1 = d + 2 := by ring
    have e2 : d + 1 + 2 = d + 3 := by ring
    rw [e1, e2]
    have h1 : (1 : ℕ) ≤ p ^ (d + 2) := Nat.one_le_pow _ _ (by omega)
    have h2 : 2 * p ^ (d + 2) ≤ p * p ^ (d + 2) := Nat.mul_le_mul_right _ hp2
    have hpow : p ^ (d + 3) = p * p ^ (d + 2) := by
      have he : d + 3 = (d + 2) + 1 := by ring
      rw [he, pow_succ]
      ring
    calc p + (d + 2) = (p + (d + 1)) + 1 := by omega
      _ < p ^ (d + 2) + 1 := Nat.add_lt_add_right ih 1
      _ ≤ p ^ (d + 2) + p ^ (d + 2) := Nat.add_le_add_left h1 _
      _ = 2 * p ^ (d + 2) := by ring
      _ ≤ p * p ^ (d + 2) := h2
      _ = p ^ (d + 3) := hpow.symm

private theorem log_le_sub_of_lt (p m q : ℕ) (hp2 : 2 ≤ p) (hmp : m ≤ p)
    (hmq : m < q) : Nat.log p q ≤ q - m := by
  have hq0 : q ≠ 0 := by omega
  have hlt : q < p ^ (q - m + 1) := by
    obtain ⟨d, rfl⟩ : ∃ d, q = m + (d + 1) := ⟨q - m - 1, by omega⟩
    have h1 : m + (d + 1) - m + 1 = d + 2 := by omega
    rw [h1]
    have h2 := add_succ_lt_pow p d hp2
    omega
  have hlog : Nat.log p q < q - m + 1 := Nat.log_lt_of_lt_pow hq0 hlt
  omega

private theorem factorization_K_le (p m q : ℕ) (hp : p.Prime) (hm : 1 ≤ m)
    (hmp : m ≤ p) (hmq : m ≤ q) :
    (Nat.factorial (m - 1) * q.choose m).factorization p ≤ q - m := by
  have hp2 : 2 ≤ p := hp.two_le
  have hfact_ne : Nat.factorial (m - 1) ≠ 0 := Nat.factorial_ne_zero _
  have hch_ne : q.choose m ≠ 0 := (Nat.choose_pos hmq).ne'
  have hfact0 : (Nat.factorial (m - 1)).factorization p = 0 := by
    apply Nat.factorization_factorial_eq_zero_of_lt
    omega
  have hmul : (Nat.factorial (m - 1) * q.choose m).factorization p =
      (Nat.factorial (m - 1)).factorization p + (q.choose m).factorization p := by
    rw [Nat.factorization_mul hfact_ne hch_ne]
    rfl
  rw [hmul, hfact0, Nat.zero_add]
  rcases eq_or_lt_of_le hmq with rfl | hlt
  · simp [Nat.choose_self]
  · have h1 : (q.choose m).factorization p ≤ Nat.log p q :=
      Nat.factorization_choose_le_log
    have h2 : Nat.log p q ≤ q - m := log_le_sub_of_lt p m q hp2 hmp hlt
    omega

private theorem norm_nat_ge_pow {p : ℕ} [Fact p.Prime] (K e : ℕ) (hK0 : K ≠ 0)
    (hfact : K.factorization p ≤ e) :
    (p : ℝ) ^ (-(e : ℤ)) ≤ ‖(K : ℚ_[p])‖ := by
  by_contra hlt
  have hlt' : ‖(K : ℚ_[p])‖ < (p : ℝ) ^ (-(e : ℤ)) := lt_of_not_ge hlt
  have hle : ‖(K : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(e : ℤ) - 1) :=
    (Padic.norm_lt_pow_iff_norm_le_pow_sub_one (K : ℚ_[p]) (-(e : ℤ))).mp hlt'
  have heq : (-(e : ℤ) - 1 : ℤ) = -(((e + 1 : ℕ) : ℤ)) := by push_cast; ring
  rw [heq] at hle
  have hle_int : ‖((K : ℤ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(((e + 1 : ℕ) : ℤ))) := by
    rwa [Int.cast_natCast]
  have hdvd : (p ^ (e + 1) : ℤ) ∣ (K : ℤ) :=
    (Padic.norm_int_le_pow_iff_dvd (K : ℤ) (e + 1)).mp hle_int
  have hdvd_nat : p ^ (e + 1) ∣ K := Int.natCast_dvd_natCast.mp hdvd
  have hpprime := (Fact.out : p.Prime)
  have hle_fact : e + 1 ≤ K.factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hpprime hK0).mp hdvd_nat
  omega

private theorem pow_le_norm_K {p : ℕ} [Fact p.Prime] (m q : ℕ) (h : ℚ_[p])
    (hh : ‖h‖ ≤ (p : ℝ)⁻¹) (hm : 1 ≤ m) (hmp : m ≤ p) (hmq : m ≤ q) :
    ‖h‖ ^ (q - m) ≤ ‖((Nat.factorial (m - 1) * q.choose m : ℕ) : ℚ_[p])‖ := by
  have hpprime := (Fact.out : p.Prime)
  have hK0 : Nat.factorial (m - 1) * q.choose m ≠ 0 :=
    mul_ne_zero (Nat.factorial_ne_zero _) (Nat.choose_pos hmq).ne'
  have hfact : (Nat.factorial (m - 1) * q.choose m).factorization p ≤ q - m :=
    factorization_K_le p m q hpprime hm hmp hmq
  have hge : (p : ℝ) ^ (-((q - m : ℕ) : ℤ)) ≤
      ‖((Nat.factorial (m - 1) * q.choose m : ℕ) : ℚ_[p])‖ :=
    norm_nat_ge_pow _ _ hK0 hfact
  have hpow : ‖h‖ ^ (q - m) ≤ ((p : ℝ)⁻¹) ^ (q - m) :=
    pow_le_pow_left₀ (norm_nonneg _) hh _
  have hinv : ((p : ℝ)⁻¹) ^ (q - m) = (p : ℝ) ^ (-((q - m : ℕ) : ℤ)) := by
    rw [inv_pow, ← zpow_natCast, ← zpow_neg]
  rw [hinv] at hpow
  exact hpow.trans hge

private theorem field_id {p : ℕ} [Fact p.Prime] (j q m : ℕ) (hm : 1 ≤ m)
    (hmq : m ≤ q) (hqj : q ≤ j) :
    (j.choose q : ℚ_[p]) * (m : ℚ_[p]) / (j.descFactorial m : ℚ_[p]) =
      ((j - m).choose (q - m) : ℚ_[p]) /
        ((Nat.factorial (m - 1) * q.choose m : ℕ) : ℚ_[p]) := by
  have hmj : m ≤ j := hmq.trans hqj
  have hdesc_ne : j.descFactorial m ≠ 0 := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    exact mul_ne_zero (Nat.factorial_ne_zero _) (Nat.choose_pos hmj).ne'
  have hK_ne : Nat.factorial (m - 1) * q.choose m ≠ 0 :=
    mul_ne_zero (Nat.factorial_ne_zero _) (Nat.choose_pos hmq).ne'
  have hn0 : (j.descFactorial m : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hdesc_ne
  have hK0 : ((Nat.factorial (m - 1) * q.choose m : ℕ) : ℚ_[p]) ≠ 0 :=
    Nat.cast_ne_zero.mpr hK_ne
  rw [div_eq_div_iff hn0 hK0]
  have hmul : m * Nat.factorial (m - 1) = Nat.factorial m := by
    match m with
    | 0 => omega
    | k + 1 =>
      simp [Nat.factorial_succ]
  have hchoose : j.choose q * q.choose m = j.choose m * (j - m).choose (q - m) :=
    Nat.choose_mul hmq
  have hdesc : j.descFactorial m = Nat.factorial m * j.choose m :=
    Nat.descFactorial_eq_factorial_mul_choose _ _
  have hnat : j.choose q * m * (Nat.factorial (m - 1) * q.choose m) =
      (j - m).choose (q - m) * (Nat.factorial m * j.choose m) := by
    have h1 : j.choose q * m * (Nat.factorial (m - 1) * q.choose m) =
        Nat.factorial m * (j.choose q * q.choose m) := by
      rw [← hmul]
      ring
    have h2 : (j - m).choose (q - m) * (Nat.factorial m * j.choose m) =
        Nat.factorial m * (j.choose m * (j - m).choose (q - m)) := by
      ring
    rw [h1, h2, hchoose]
  have hcast : ((j.choose q * m * (Nat.factorial (m - 1) * q.choose m) : ℕ) : ℚ_[p]) =
      (((j - m).choose (q - m) * (Nat.factorial m * j.choose m) : ℕ) : ℚ_[p]) := by
    rw [hnat]
  push_cast at hcast
  have hdesc_cast : (j.descFactorial m : ℚ_[p]) =
      (Nat.factorial m : ℚ_[p]) * (j.choose m : ℚ_[p]) := by
    rw [hdesc]
    push_cast
    ring
  rw [hdesc_cast]
  push_cast at hcast ⊢
  exact hcast

private theorem term_le {p : ℕ} [Fact p.Prime] {B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℚ_[p] B] [IsUltrametricDist B] (j q m : ℕ) (a : ℕ → B)
    (t h : ℚ_[p]) (C : ℝ) (ht : ‖t‖ ≤ 1) (hm : 1 ≤ m) (hmp : m ≤ p)
    (hh : ‖h‖ ≤ (p : ℝ)⁻¹) (hC : ‖j.descFactorial m • a j‖ ≤ C)
    (hmq : m ≤ q) (hqj : q ≤ j) :
    ‖(((j.choose q : ℚ_[p]) * t ^ (j - q) * h ^ q) • a j)‖ ≤
      ‖h ^ m / (m : ℚ_[p])‖ * C := by
  have hcho_nn : 0 ≤ ‖(j.choose q : ℚ_[p])‖ := norm_nonneg _
  have ht_nn : 0 ≤ ‖t‖ := norm_nonneg _
  have hh_nn : 0 ≤ ‖h‖ := norm_nonneg _
  have ha_nn : 0 ≤ ‖a j‖ := norm_nonneg _
  have ht_pow_le : ‖t‖ ^ (j - q) ≤ 1 := pow_le_one₀ ht_nn ht
  have hsmul : ‖(((j.choose q : ℚ_[p]) * t ^ (j - q) * h ^ q) • a j)‖ =
      ‖(j.choose q : ℚ_[p]) * t ^ (j - q) * h ^ q‖ * ‖a j‖ := norm_smul _ _
  have hmul : ‖(j.choose q : ℚ_[p]) * t ^ (j - q) * h ^ q‖ =
      ‖(j.choose q : ℚ_[p])‖ * ‖t‖ ^ (j - q) * ‖h‖ ^ q := by
    rw [norm_mul, norm_mul, norm_pow, norm_pow]
  have hdrop : ‖(j.choose q : ℚ_[p])‖ * ‖t‖ ^ (j - q) * ‖h‖ ^ q ≤
      ‖(j.choose q : ℚ_[p])‖ * ‖h‖ ^ q := by
    have h1 : ‖t‖ ^ (j - q) * ‖h‖ ^ q ≤ 1 * ‖h‖ ^ q :=
      mul_le_mul_of_nonneg_right ht_pow_le (pow_nonneg hh_nn _)
    have h2 : ‖(j.choose q : ℚ_[p])‖ * (‖t‖ ^ (j - q) * ‖h‖ ^ q) ≤
        ‖(j.choose q : ℚ_[p])‖ * (1 * ‖h‖ ^ q) :=
      mul_le_mul_of_nonneg_left h1 hcho_nn
    simpa [mul_assoc] using h2
  have hm_ne : (m : ℚ_[p]) ≠ 0 := by
    have : (m : ℚ_[p]) = ((m : ℕ) : ℚ_[p]) := rfl
    rw [this]
    exact Nat.cast_ne_zero.mpr (by omega)
  have hRHS : ‖h ^ m / (m : ℚ_[p])‖ = ‖h‖ ^ m / ‖(m : ℚ_[p])‖ := by
    rw [norm_div, norm_pow]
  have hdesc_ne : j.descFactorial m ≠ 0 := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    exact mul_ne_zero (Nat.factorial_ne_zero _) (Nat.choose_pos (hmq.trans hqj)).ne'
  have hn0 : (j.descFactorial m : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hdesc_ne
  have hCa : ‖(j.descFactorial m : ℚ_[p])‖ * ‖a j‖ ≤ C := by
    have h1 : ‖j.descFactorial m • a j‖ = ‖(j.descFactorial m : ℚ_[p])‖ * ‖a j‖ := by
      rw [← Nat.cast_smul_eq_nsmul ℚ_[p]]
      exact norm_smul _ _
    rwa [h1] at hC
  have hpow_q : ‖h‖ ^ q = ‖h‖ ^ m * ‖h‖ ^ (q - m) := by
    have hqm : m + (q - m) = q := Nat.add_sub_cancel' hmq
    conv_lhs => rw [← hqm]
    rw [pow_add]
  have hK0_nat : Nat.factorial (m - 1) * q.choose m ≠ 0 :=
    mul_ne_zero (Nat.factorial_ne_zero _) (Nat.choose_pos hmq).ne'
  have hK0 : ((Nat.factorial (m - 1) * q.choose m : ℕ) : ℚ_[p]) ≠ 0 :=
    Nat.cast_ne_zero.mpr hK0_nat
  have hKpos : 0 < ‖((Nat.factorial (m - 1) * q.choose m : ℕ) : ℚ_[p])‖ :=
    norm_pos_iff.mpr hK0
  have hb2_le : ‖((j - m).choose (q - m) : ℚ_[p])‖ ≤ 1 :=
    IsUltrametricDist.norm_natCast_le_one ℚ_[p] _
  have hfid := field_id (p := p) j q m hm hmq hqj
  have hR_le : ‖(j.choose q : ℚ_[p]) * (m : ℚ_[p]) / (j.descFactorial m : ℚ_[p])‖ ≤
      1 / ‖((Nat.factorial (m - 1) * q.choose m : ℕ) : ℚ_[p])‖ := by
    rw [hfid, norm_div]
    have : ‖((j - m).choose (q - m) : ℚ_[p])‖ /
        ‖((Nat.factorial (m - 1) * q.choose m : ℕ) : ℚ_[p])‖ ≤
        1 / ‖((Nat.factorial (m - 1) * q.choose m : ℕ) : ℚ_[p])‖ :=
      div_le_div_of_nonneg_right hb2_le (le_of_lt hKpos)
    exact this
  have hR_eq : ‖(j.choose q : ℚ_[p]) * (m : ℚ_[p]) / (j.descFactorial m : ℚ_[p])‖ =
      ‖(j.choose q : ℚ_[p])‖ * ‖(m : ℚ_[p])‖ / ‖(j.descFactorial m : ℚ_[p])‖ := by
    rw [norm_div, norm_mul]
  have hpowK : ‖h‖ ^ (q - m) ≤ ‖((Nat.factorial (m - 1) * q.choose m : ℕ) : ℚ_[p])‖ :=
    pow_le_norm_K m q h hh hm hmp hmq
  have hcomb : (‖(j.choose q : ℚ_[p])‖ * ‖(m : ℚ_[p])‖ /
      ‖(j.descFactorial m : ℚ_[p])‖) * ‖h‖ ^ (q - m) ≤ 1 := by
    rw [← hR_eq] at *
    have h1 : ‖(j.choose q : ℚ_[p]) * (m : ℚ_[p]) / (j.descFactorial m : ℚ_[p])‖ *
        ‖h‖ ^ (q - m) ≤
        (1 / ‖((Nat.factorial (m - 1) * q.choose m : ℕ) : ℚ_[p])‖) *
          ‖((Nat.factorial (m - 1) * q.choose m : ℕ) : ℚ_[p])‖ := by
      apply mul_le_mul hR_le hpowK (pow_nonneg hh_nn _) (by positivity)
    have h2 : (1 / ‖((Nat.factorial (m - 1) * q.choose m : ℕ) : ℚ_[p])‖) *
        ‖((Nat.factorial (m - 1) * q.choose m : ℕ) : ℚ_[p])‖ = 1 := by
      field_simp
    rwa [h2] at h1
  have hm_pos : 0 < ‖(m : ℚ_[p])‖ := norm_pos_iff.mpr hm_ne
  have hn_pos : 0 < ‖(j.descFactorial m : ℚ_[p])‖ := norm_pos_iff.mpr hn0
  have hkey : ‖(j.choose q : ℚ_[p])‖ * ‖h‖ ^ q ≤
      (‖h‖ ^ m / ‖(m : ℚ_[p])‖) * ‖(j.descFactorial m : ℚ_[p])‖ := by
    rw [hpow_q]
    have h1 : ‖(j.choose q : ℚ_[p])‖ * (‖h‖ ^ m * ‖h‖ ^ (q - m)) =
        ‖h‖ ^ m * (‖(j.choose q : ℚ_[p])‖ * ‖h‖ ^ (q - m)) := by ring
    have h2 : (‖h‖ ^ m / ‖(m : ℚ_[p])‖) * ‖(j.descFactorial m : ℚ_[p])‖ =
        ‖h‖ ^ m * (‖(j.descFactorial m : ℚ_[p])‖ / ‖(m : ℚ_[p])‖) := by ring
    rw [h1, h2]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hh_nn _)
    rw [le_div_iff₀ hm_pos]
    have h3 : ‖(j.choose q : ℚ_[p])‖ * ‖h‖ ^ (q - m) * ‖(m : ℚ_[p])‖ =
        ((‖(j.choose q : ℚ_[p])‖ * ‖(m : ℚ_[p])‖ /
          ‖(j.descFactorial m : ℚ_[p])‖) * ‖h‖ ^ (q - m)) *
          ‖(j.descFactorial m : ℚ_[p])‖ := by
      field_simp
    rw [h3]
    have h4 : ((‖(j.choose q : ℚ_[p])‖ * ‖(m : ℚ_[p])‖ /
        ‖(j.descFactorial m : ℚ_[p])‖) * ‖h‖ ^ (q - m)) *
        ‖(j.descFactorial m : ℚ_[p])‖ ≤
        1 * ‖(j.descFactorial m : ℚ_[p])‖ :=
      mul_le_mul_of_nonneg_right hcomb (le_of_lt hn_pos)
    rwa [one_mul] at h4
  rw [hsmul, hmul, hRHS]
  have hstep1 : ‖(j.choose q : ℚ_[p])‖ * ‖t‖ ^ (j - q) * ‖h‖ ^ q * ‖a j‖ ≤
      ‖(j.choose q : ℚ_[p])‖ * ‖h‖ ^ q * ‖a j‖ :=
    mul_le_mul_of_nonneg_right hdrop ha_nn
  have hstep2 : ‖(j.choose q : ℚ_[p])‖ * ‖h‖ ^ q * ‖a j‖ ≤
      ((‖h‖ ^ m / ‖(m : ℚ_[p])‖) * ‖(j.descFactorial m : ℚ_[p])‖) * ‖a j‖ :=
    mul_le_mul_of_nonneg_right hkey ha_nn
  have hstep3 : ((‖h‖ ^ m / ‖(m : ℚ_[p])‖) * ‖(j.descFactorial m : ℚ_[p])‖) * ‖a j‖ ≤
      (‖h‖ ^ m / ‖(m : ℚ_[p])‖) * C := by
    have h1 : (‖h‖ ^ m / ‖(m : ℚ_[p])‖) * (‖(j.descFactorial m : ℚ_[p])‖ * ‖a j‖) ≤
        (‖h‖ ^ m / ‖(m : ℚ_[p])‖) * C :=
      mul_le_mul_of_nonneg_left hCa (by positivity)
    rw [mul_assoc]
    exact h1
  exact hstep1.trans (hstep2.trans hstep3)

private theorem norm_le_inv_of_rpow_bound {p : ℕ} [Fact p.Prime] (m : ℕ)
    (h : ℚ_[p]) (hmp : m ≤ p)
    (hh₁ : m < p → ‖h‖ ≤ (p : ℝ) ^ (-(1 / ((p : ℝ) - m))))
    (hh₂ : m = p → ‖h‖ ≤ (p : ℝ) ^ (-(1 / (p : ℝ)))) :
    ‖h‖ ≤ (p : ℝ)⁻¹ := by
  have hpprime := (Fact.out : p.Prime)
  have hpR1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpprime.one_lt
  have hlt1 : ‖h‖ < 1 := by
    rcases lt_or_eq_of_le hmp with hlt | heq
    · have hpos : (0 : ℝ) < (p : ℝ) - m := by
        have : (m : ℝ) < (p : ℝ) := by exact_mod_cast hlt
        linarith
      have hexp : (-(1 / ((p : ℝ) - m)) : ℝ) < 0 := by
        have : (0 : ℝ) < 1 / ((p : ℝ) - m) := by positivity
        linarith
      have hrpow_lt : (p : ℝ) ^ (-(1 / ((p : ℝ) - m))) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg hpR1 hexp
      exact lt_of_le_of_lt (hh₁ hlt) hrpow_lt
    · have hexp : (-(1 / (p : ℝ)) : ℝ) < 0 := by
        have hppos : (0 : ℝ) < (p : ℝ) := by positivity
        have : (0 : ℝ) < 1 / (p : ℝ) := by positivity
        linarith
      have hrpow_lt : (p : ℝ) ^ (-(1 / (p : ℝ))) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg hpR1 hexp
      exact lt_of_le_of_lt (hh₂ heq) hrpow_lt
  by_cases hh0 : h = 0
  · simp only [hh0, norm_zero]
    positivity
  · have hnorm_eq : ‖h‖ = (p : ℝ) ^ (-h.valuation) :=
      Padic.norm_eq_zpow_neg_valuation hh0
    have hval_pos : 0 < h.valuation := by
      rw [hnorm_eq] at hlt1
      rw [zpow_lt_one_iff_right₀ hpR1] at hlt1
      omega
    rw [hnorm_eq]
    have hle : (-h.valuation : ℤ) ≤ (-1 : ℤ) := by omega
    have hmono : (p : ℝ) ^ (-h.valuation) ≤ (p : ℝ) ^ (-1 : ℤ) := by
      rw [zpow_le_zpow_iff_right₀ hpR1]
      exact hle
    simpa using hmono

/-- **Higher $p$-adic mean value theorem.** Let $p$ be a prime, let $|\cdot|$ be the $p$-adic
absolute value on $\mathbb{Q}_p$, and let $B$ be a normed vector space over $\mathbb{Q}_p$ whose
norm is ultrametric. Let $N$ and $m$ be natural numbers with $1 \le m \le p$, let
$f(t) = \sum_{j<N} a_j t^j$ be a polynomial with coefficients $a_j \in B$, and let
$t, h \in \mathbb{Q}_p$ with $|t| \le 1$. Suppose that $|h| \le p^{-1/(p-m)}$ if $m < p$, that
$|h| \le p^{-1/p}$ if $m = p$, and that $C \ge 0$ is a real number with
$\|j(j-1)\cdots(j-m+1) \, a_j\| \le C$ for every $j < N$. Then
$$\Big\| f(t+h) - \sum_{q<m} \sum_{q \le j < N} \binom{j}{q} t^{j-q} h^q a_j \Big\| \le
\Big| \frac{h^m}{m} \Big| \, C.$$

The inner sum $\sum_{q \le j < N} \binom{j}{q} t^{j-q} a_j$ is $f^{(q)}(t)/q!$, and the least
admissible $C$ is the sup of the norms of the coefficients of $f^{(m)}$.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Theorem 1
(`integers-2026-A32-thm-1`). -/
public theorem norm_sub_taylor_le_of_norm_le {p : ℕ} [Fact p.Prime] {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℚ_[p] B] [IsUltrametricDist B] (N m : ℕ) (a : ℕ → B)
    (t h : ℚ_[p]) (C : ℝ) (ht : ‖t‖ ≤ 1) (hm : 1 ≤ m) (hmp : m ≤ p)
    (hh₁ : m < p → ‖h‖ ≤ (p : ℝ) ^ (-(1 / ((p : ℝ) - m))))
    (hh₂ : m = p → ‖h‖ ≤ (p : ℝ) ^ (-(1 / (p : ℝ))))
    (hC₀ : 0 ≤ C) (hC : ∀ j ∈ Finset.range N, ‖j.descFactorial m • a j‖ ≤ C) :
    ‖∑ j ∈ Finset.range N, (t + h) ^ j • a j -
        ∑ q ∈ Finset.range m, ∑ j ∈ Finset.range N,
          ((j.choose q : ℚ_[p]) * t ^ (j - q) * h ^ q) • a j‖ ≤
      ‖h ^ m / (m : ℚ_[p])‖ * C := by
  have hh_inv : ‖h‖ ≤ (p : ℝ)⁻¹ := norm_le_inv_of_rpow_bound m h hmp hh₁ hh₂
  have hRHS_nn : 0 ≤ ‖h ^ m / (m : ℚ_[p])‖ * C :=
    mul_nonneg (norm_nonneg _) hC₀
  set K := max N m
  have hNK : N ≤ K := Nat.le_max_left _ _
  have hmK : m ≤ K := Nat.le_max_right _ _
  have hS_eq : ∀ j ∈ Finset.range N, (t + h) ^ j • a j =
      ∑ q ∈ Finset.range K, (((j.choose q : ℚ_[p]) * t ^ (j - q) * h ^ q) • a j) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hjK : j + 1 ≤ K := (Nat.succ_le_of_lt hj).trans hNK
    have hbin : (t + h) ^ j = ∑ q ∈ Finset.range (j + 1),
        ((j.choose q : ℚ_[p]) * t ^ (j - q) * h ^ q) := by
      have h1 : (t + h) ^ j = (h + t) ^ j := by rw [add_comm]
      rw [h1, add_pow]
      apply Finset.sum_congr rfl
      intro q _
      ring
    have hsmul : (t + h) ^ j • a j = ∑ q ∈ Finset.range (j + 1),
        ((((j.choose q : ℚ_[p]) * t ^ (j - q) * h ^ q)) • a j) := by
      rw [hbin, Finset.sum_smul]
    rw [hsmul]
    apply Finset.sum_subset (Finset.range_mono hjK)
    intro q _ hqj1
    have hnot : ¬ q < j + 1 := by
      intro hlt
      exact hqj1 (Finset.mem_range.mpr hlt)
    have hjq : j < q := by omega
    simp [Nat.choose_eq_zero_of_lt hjq]
  have hS : ∑ j ∈ Finset.range N, (t + h) ^ j • a j =
      ∑ j ∈ Finset.range N, ∑ q ∈ Finset.range K,
        (((j.choose q : ℚ_[p]) * t ^ (j - q) * h ^ q) • a j) :=
    Finset.sum_congr rfl hS_eq
  have hT : (∑ q ∈ Finset.range m, ∑ j ∈ Finset.range N,
        (((j.choose q : ℚ_[p]) * t ^ (j - q) * h ^ q) • a j)) =
      ∑ j ∈ Finset.range N, ∑ q ∈ Finset.range m,
        (((j.choose q : ℚ_[p]) * t ^ (j - q) * h ^ q) • a j) :=
    Finset.sum_comm
  rw [hS, hT, ← Finset.sum_sub_distrib]
  have hdiff : ∀ j ∈ Finset.range N,
      (∑ q ∈ Finset.range K, (((j.choose q : ℚ_[p]) * t ^ (j - q) * h ^ q) • a j)) -
        (∑ q ∈ Finset.range m, (((j.choose q : ℚ_[p]) * t ^ (j - q) * h ^ q) • a j)) =
        ∑ q ∈ Finset.Ico m K, (((j.choose q : ℚ_[p]) * t ^ (j - q) * h ^ q) • a j) := by
    intro j _
    have h := Finset.sum_range_add_sum_Ico
      (fun q => (((j.choose q : ℚ_[p]) * t ^ (j - q) * h ^ q) • a j)) hmK
    rw [← h, add_sub_cancel_left]
  have hsum : (∑ j ∈ Finset.range N,
      ((∑ q ∈ Finset.range K, (((j.choose q : ℚ_[p]) * t ^ (j - q) * h ^ q) • a j)) -
        (∑ q ∈ Finset.range m, (((j.choose q : ℚ_[p]) * t ^ (j - q) * h ^ q) • a j)))) =
      ∑ j ∈ Finset.range N, ∑ q ∈ Finset.Ico m K,
        (((j.choose q : ℚ_[p]) * t ^ (j - q) * h ^ q) • a j) :=
    Finset.sum_congr rfl hdiff
  rw [hsum]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hRHS_nn
  intro j hj
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hRHS_nn
  intro q hq
  rw [Finset.mem_Ico] at hq
  by_cases hqj : q ≤ j
  · exact term_le (p := p) j q m a t h C ht hm hmp hh_inv (hC j hj) hq.1 hqj
  · have hjq : j < q := not_le.mp hqj
    have h0 : (((j.choose q : ℚ_[p]) * t ^ (j - q) * h ^ q) • a j) = 0 := by
      simp [Nat.choose_eq_zero_of_lt hjq]
    rw [h0, norm_zero]
    exact hRHS_nn

end MetaMathlibExt
