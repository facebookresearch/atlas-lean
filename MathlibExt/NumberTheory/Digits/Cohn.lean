/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.List.Indexes
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators

namespace MetaMathlibExt

section

private lemma complex_sum_root_radius
    (b n : ℕ) (a : ℕ → ℕ) (z : ℂ)
    (hn : 1 ≤ n) (han : 1 ≤ a n) (ha : ∀ i, a i < b)
    (hz : ∑ i ∈ Finset.range (n + 1), (a i : ℂ) * z ^ i = 0)
    (hre : 0 < z.re) (hr : 1 < ‖z‖) :
    ‖z‖ * (‖z‖ - 1) < (b : ℝ) - 1 := by
  have hsplit :
      (a n : ℂ) * z ^ n + (a (n - 1) : ℂ) * z ^ (n - 1) =
        -∑ i ∈ Finset.range (n - 1), (a i : ℂ) * z ^ i := by
    rw [show n + 1 = (n - 1) + 2 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ] at hz
    rw [add_assoc] at hz
    have hnm1 : n - 1 + 1 = n := by omega
    rw [hnm1] at hz
    linear_combination hz
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    norm_num at hr
  have hpow : z ^ n = z ^ (n - 1) * z := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
  have hfac :
      (a n : ℂ) * z ^ n + (a (n - 1) : ℂ) * z ^ (n - 1) =
        z ^ (n - 1) * ((a n : ℂ) * z + a (n - 1)) := by
    rw [hpow]
    ring
  have hleft : ‖z‖ ^ n ≤
      ‖(a n : ℂ) * z ^ n + (a (n - 1) : ℂ) * z ^ (n - 1)‖ := by
    rw [hfac, norm_mul, norm_pow]
    have hinner : ‖z‖ ≤ ‖(a n : ℂ) * z + a (n - 1)‖ := by
      rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm,
        Complex.sq_norm]
      change z.re * z.re + z.im * z.im ≤
        (↑(a n) * z + ↑(a (n - 1))).re * (↑(a n) * z + ↑(a (n - 1))).re +
          (↑(a n) * z + ↑(a (n - 1))).im * (↑(a n) * z + ↑(a (n - 1))).im
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
      have han' : (1 : ℝ) ≤ a n := by exact_mod_cast han
      have hc : (0 : ℝ) ≤ a (n - 1) := by exact_mod_cast Nat.zero_le (a (n - 1))
      nlinarith [sq_nonneg (((a n : ℝ) - 1) * z.re),
        sq_nonneg (((a n : ℝ) - 1) * z.im),
        mul_nonneg hc (le_of_lt hre)]
    have hpnonneg : 0 ≤ ‖z‖ ^ (n - 1) := pow_nonneg (norm_nonneg _) _
    calc
      ‖z‖ ^ n = ‖z‖ ^ (n - 1) * ‖z‖ := by
        conv_lhs => rw [show n = (n - 1) + 1 by omega]
        rw [pow_succ]
      _ ≤ ‖z‖ ^ (n - 1) * ‖(a n : ℂ) * z + a (n - 1)‖ :=
        mul_le_mul_of_nonneg_left hinner hpnonneg
  have hright :
      ‖(a n : ℂ) * z ^ n + (a (n - 1) : ℂ) * z ^ (n - 1)‖ ≤
        ((b : ℝ) - 1) * ∑ i ∈ Finset.range (n - 1), ‖z‖ ^ i := by
    rw [hsplit, norm_neg]
    calc
      ‖∑ i ∈ Finset.range (n - 1), (a i : ℂ) * z ^ i‖ ≤
          ∑ i ∈ Finset.range (n - 1), ‖(a i : ℂ) * z ^ i‖ := norm_sum_le _ _
      _ = ∑ i ∈ Finset.range (n - 1), (a i : ℝ) * ‖z‖ ^ i := by
        apply Finset.sum_congr rfl
        intro i hi
        simp
      _ ≤ ∑ i ∈ Finset.range (n - 1), ((b : ℝ) - 1) * ‖z‖ ^ i := by
        gcongr with i hi
        have hai : a i ≤ b - 1 := Nat.le_sub_one_of_lt (ha i)
        have hbn : 1 < b := lt_of_le_of_lt han (ha n)
        have hbcast : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
          rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (by omega)), Nat.cast_one]
        rw [← hbcast]
        exact_mod_cast hai
      _ = ((b : ℝ) - 1) * ∑ i ∈ Finset.range (n - 1), ‖z‖ ^ i := by
        rw [Finset.mul_sum]
  have hmain : ‖z‖ ^ n ≤ ((b : ℝ) - 1) * ∑ i ∈ Finset.range (n - 1), ‖z‖ ^ i :=
    hleft.trans hright
  have hb2 : 2 ≤ b := by
    have : 1 < b := lt_of_le_of_lt han (ha n)
    omega
  have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by
    exact sub_pos.mpr (by exact_mod_cast (show 1 < b by omega))
  have hgeom :
      ∑ i ∈ Finset.range (n - 1), ‖z‖ ^ i < ‖z‖ ^ (n - 1) / (‖z‖ - 1) := by
    rw [geom_sum_eq (ne_of_gt hr)]
    apply div_lt_div_of_pos_right _ (sub_pos.mpr hr)
    linarith
  have hstrict :
      ‖z‖ ^ n < ((b : ℝ) - 1) * (‖z‖ ^ (n - 1) / (‖z‖ - 1)) :=
    hmain.trans_lt (mul_lt_mul_of_pos_left hgeom hb1)
  have hden : 0 < ‖z‖ - 1 := sub_pos.mpr hr
  have hstrict' : ‖z‖ ^ n * (‖z‖ - 1) < ((b : ℝ) - 1) * ‖z‖ ^ (n - 1) := by
    calc
      ‖z‖ ^ n * (‖z‖ - 1) <
          (((b : ℝ) - 1) * (‖z‖ ^ (n - 1) / (‖z‖ - 1))) * (‖z‖ - 1) :=
        mul_lt_mul_of_pos_right hstrict hden
      _ = ((b : ℝ) - 1) * ‖z‖ ^ (n - 1) := by field_simp
  have hp : 0 < ‖z‖ ^ (n - 1) := pow_pos (norm_pos_iff.mpr hz0) _
  have hpn : ‖z‖ ^ n = ‖z‖ ^ (n - 1) * ‖z‖ := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
  rw [hpn] at hstrict'
  nlinarith

private lemma complex_sum_root_dist_gt_one
    (b n : ℕ) (a : ℕ → ℕ) (z : ℂ)
    (hn : 1 ≤ n) (han : 1 ≤ a n) (ha : ∀ i, a i < b) (hb : 3 ≤ b)
    (hz : ∑ i ∈ Finset.range (n + 1), (a i : ℂ) * z ^ i = 0) :
    1 < ‖(b : ℂ) - z‖ := by
  by_cases hre : 0 < z.re
  · by_cases hr : 1 < ‖z‖
    · have hrad := complex_sum_root_radius b n a z hn han ha hz hre hr
      have hbR : (3 : ℝ) ≤ b := by exact_mod_cast hb
      have hrlt : ‖z‖ < (b : ℝ) - 1 := by
        by_contra h
        have hge : (b : ℝ) - 1 ≤ ‖z‖ := le_of_not_gt h
        have hrm : (b : ℝ) - 2 ≤ ‖z‖ - 1 := by linarith
        have hprod : ((b : ℝ) - 1) * ((b : ℝ) - 2) ≤ ‖z‖ * (‖z‖ - 1) := by
          exact mul_le_mul hge hrm (by linarith) (by linarith)
        have : (b : ℝ) - 1 ≤ ((b : ℝ) - 1) * ((b : ℝ) - 2) := by
          nlinarith
        linarith
      have htri := norm_sub_norm_le (b : ℂ) z
      norm_num at htri
      linarith
    · have hrle : ‖z‖ ≤ 1 := le_of_not_gt hr
      have htri := norm_sub_norm_le (b : ℂ) z
      norm_num at htri
      have hbR : (3 : ℝ) ≤ b := by exact_mod_cast hb
      linarith
  · have hre' : z.re ≤ 0 := le_of_not_gt hre
    have hreal := Complex.abs_re_le_norm ((b : ℂ) - z)
    have habs : (b : ℝ) - z.re ≤ |(b : ℝ) - z.re| := le_abs_self _
    norm_num at hreal
    have hbR : (3 : ℝ) ≤ b := by exact_mod_cast hb
    linarith

private lemma complex_binary_sum_root_radius_sq
    (n : ℕ) (a : ℕ → ℕ) (z : ℂ)
    (hn : 2 ≤ n) (han : 1 ≤ a n) (ha : ∀ i, a i < 2)
    (hz : ∑ i ∈ Finset.range (n + 1), (a i : ℂ) * z ^ i = 0)
    (hre : 0 < z.re) (hre2 : 0 < (z ^ 2).re) (hr : 1 < ‖z‖) :
    ‖z‖ ^ 2 * (‖z‖ - 1) < 1 := by
  have hanlt := ha n
  have han1 : a n = 1 := by omega
  have hsplit :
      z ^ n + (a (n - 1) : ℂ) * z ^ (n - 1) +
          (a (n - 2) : ℂ) * z ^ (n - 2) =
        -∑ i ∈ Finset.range (n - 2), (a i : ℂ) * z ^ i := by
    rw [show n + 1 = (n - 2) + 3 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ] at hz
    have hn2 : n - 2 + 2 = n := by omega
    have hn1 : n - 2 + 1 = n - 1 := by omega
    rw [hn2, hn1, han1, Nat.cast_one, one_mul] at hz
    linear_combination hz
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    norm_num at hr
  have hpow2 : z ^ n = z ^ (n - 2) * z ^ 2 := by
    conv_lhs => rw [show n = (n - 2) + 2 by omega]
    rw [pow_add]
  have hpow1 : z ^ (n - 1) = z ^ (n - 2) * z := by
    conv_lhs => rw [show n - 1 = (n - 2) + 1 by omega]
    rw [pow_succ]
  have hfac :
      z ^ n + (a (n - 1) : ℂ) * z ^ (n - 1) +
          (a (n - 2) : ℂ) * z ^ (n - 2) =
        z ^ (n - 2) * (z ^ 2 + (a (n - 1) : ℂ) * z + a (n - 2)) := by
    rw [hpow2, hpow1]
    ring
  have hinner :
      ‖z‖ ^ 2 ≤ ‖z ^ 2 + (a (n - 1) : ℂ) * z + a (n - 2)‖ := by
    rw [← norm_pow]
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm,
      Complex.sq_norm]
    change (z ^ 2).re * (z ^ 2).re + (z ^ 2).im * (z ^ 2).im ≤
      (z ^ 2 + (↑(a (n - 1)) : ℂ) * z + (↑(a (n - 2)) : ℂ)).re *
          (z ^ 2 + (↑(a (n - 1)) : ℂ) * z + (↑(a (n - 2)) : ℂ)).re +
        (z ^ 2 + (↑(a (n - 1)) : ℂ) * z + (↑(a (n - 2)) : ℂ)).im *
          (z ^ 2 + (↑(a (n - 1)) : ℂ) * z + (↑(a (n - 2)) : ℂ)).im
    have hclt := ha (n - 1)
    have hdlt := ha (n - 2)
    have hc : a (n - 1) ≤ 1 := by omega
    have hd : a (n - 2) ≤ 1 := by omega
    interval_cases a (n - 1) <;> interval_cases a (n - 2) <;>
      simp only [Nat.cast_zero, Nat.cast_one, zero_mul, one_mul,
        Complex.add_re, Complex.add_im,
        Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im] <;>
      norm_num [pow_two] at hre2 ⊢ <;>
      nlinarith [sq_nonneg z.re, sq_nonneg z.im,
        mul_nonneg (le_of_lt hre) (sq_nonneg z.re),
        mul_nonneg (le_of_lt hre) (sq_nonneg z.im)]
  have hleft : ‖z‖ ^ n ≤
      ‖z ^ n + (a (n - 1) : ℂ) * z ^ (n - 1) +
        (a (n - 2) : ℂ) * z ^ (n - 2)‖ := by
    rw [hfac, norm_mul, norm_pow]
    have hpnonneg : 0 ≤ ‖z‖ ^ (n - 2) := pow_nonneg (norm_nonneg _) _
    calc
      ‖z‖ ^ n = ‖z‖ ^ (n - 2) * ‖z‖ ^ 2 := by
        conv_lhs => rw [show n = (n - 2) + 2 by omega]
        rw [pow_add]
      _ ≤ _ := mul_le_mul_of_nonneg_left hinner hpnonneg
  have hright :
      ‖z ^ n + (a (n - 1) : ℂ) * z ^ (n - 1) +
        (a (n - 2) : ℂ) * z ^ (n - 2)‖ ≤
          ∑ i ∈ Finset.range (n - 2), ‖z‖ ^ i := by
    rw [hsplit, norm_neg]
    calc
      ‖∑ i ∈ Finset.range (n - 2), (a i : ℂ) * z ^ i‖ ≤
          ∑ i ∈ Finset.range (n - 2), ‖(a i : ℂ) * z ^ i‖ := norm_sum_le _ _
      _ = ∑ i ∈ Finset.range (n - 2), (a i : ℝ) * ‖z‖ ^ i := by
        apply Finset.sum_congr rfl
        intro i hi
        simp
      _ ≤ ∑ i ∈ Finset.range (n - 2), ‖z‖ ^ i := by
        apply Finset.sum_le_sum
        intro i hi
        have hailt := ha i
        have hai : a i ≤ 1 := by omega
        have haiR : (a i : ℝ) ≤ 1 := by exact_mod_cast hai
        exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) haiR
  have hmain : ‖z‖ ^ n ≤ ∑ i ∈ Finset.range (n - 2), ‖z‖ ^ i :=
    hleft.trans hright
  have hgeom :
      ∑ i ∈ Finset.range (n - 2), ‖z‖ ^ i < ‖z‖ ^ (n - 2) / (‖z‖ - 1) := by
    rw [geom_sum_eq (ne_of_gt hr)]
    apply div_lt_div_of_pos_right _ (sub_pos.mpr hr)
    linarith
  have hstrict := hmain.trans_lt hgeom
  have hden : 0 < ‖z‖ - 1 := sub_pos.mpr hr
  have hstrict' : ‖z‖ ^ n * (‖z‖ - 1) < ‖z‖ ^ (n - 2) := by
    calc
      ‖z‖ ^ n * (‖z‖ - 1) <
          (‖z‖ ^ (n - 2) / (‖z‖ - 1)) * (‖z‖ - 1) :=
        mul_lt_mul_of_pos_right hstrict hden
      _ = ‖z‖ ^ (n - 2) := by field_simp
  have hp : 0 < ‖z‖ ^ (n - 2) := pow_pos (norm_pos_iff.mpr hz0) _
  have hpn : ‖z‖ ^ n = ‖z‖ ^ (n - 2) * ‖z‖ ^ 2 := by
    conv_lhs => rw [show n = (n - 2) + 2 by omega]
    rw [pow_add]
  rw [hpn] at hstrict'
  nlinarith

private lemma complex_binary_sum_root_re_lt
    (n : ℕ) (a : ℕ → ℕ) (z : ℂ)
    (han : 1 ≤ a n) (ha : ∀ i, a i < 2)
    (hz : ∑ i ∈ Finset.range (n + 1), (a i : ℂ) * z ^ i = 0) :
    z.re < (3 : ℝ) / 2 := by
  have hanlt := ha n
  have han1 : a n = 1 := by omega
  by_cases hn0 : n = 0
  · subst n
    simp [han1] at hz
  by_cases hn1 : n = 1
  · subst n
    norm_num [Finset.sum_range_succ, han1] at hz
    have hzre := congrArg Complex.re hz
    norm_num at hzre
    have ha0 : (0 : ℝ) ≤ a 0 := by exact_mod_cast Nat.zero_le (a 0)
    linarith
  have hn : 2 ≤ n := by omega
  by_cases hr : 1 < ‖z‖
  · by_cases hre : 0 < z.re
    · have hrad := complex_sum_root_radius 2 n a z (by omega) han ha hz hre hr
      norm_num at hrad
      have hrlt : ‖z‖ < 2 := by nlinarith
      by_contra hrez
      have hrege : (3 : ℝ) / 2 ≤ z.re := le_of_not_gt hrez
      have hnorm : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := Complex.sq_norm z
      have hre2 : 0 < (z ^ 2).re := by
        norm_num [pow_two, Complex.mul_re]
        nlinarith [sq_nonneg z.im]
      have hs := complex_binary_sum_root_radius_sq n a z hn han ha hz hre hre2 hr
      have hreznorm := Complex.abs_re_le_norm z
      have : z.re ≤ ‖z‖ := (le_abs_self z.re).trans hreznorm
      nlinarith
    · linarith
  · have hrle : ‖z‖ ≤ 1 := le_of_not_gt hr
    have hreznorm := Complex.abs_re_le_norm z
    have : z.re ≤ ‖z‖ := (le_abs_self z.re).trans hreznorm
    linarith

private lemma norm_multiset_prod (s : Multiset ℂ) :
    ‖s.prod‖ = (s.map norm).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons x s ih => simp [ih]

private lemma one_lt_multiset_prod (s : Multiset ℝ) (hs : s ≠ 0)
    (h : ∀ x ∈ s, 1 < x) : 1 < s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp at hs
  | @cons x s ih =>
      by_cases hs0 : s = 0
      · subst s
        simpa using h x (by simp)
      · have hx : 1 < x := h x (by simp)
        have hi : 1 < s.prod := ih hs0 (by
          intro y hy
          exact h y (by simp [hy]))
        simp only [Multiset.prod_cons]
        nlinarith [mul_pos (lt_trans zero_lt_one hx) (lt_trans zero_lt_one hi)]

private lemma multiset_prod_nonneg (s : Multiset ℝ) (h : ∀ x ∈ s, 0 ≤ x) :
    0 ≤ s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons x s ih =>
      simp only [Multiset.prod_cons]
      exact mul_nonneg (h x (by simp)) (ih (by
        intro y hy
        exact h y (by simp [hy])))

private lemma multiset_prod_lt_prod_of_nonempty_nonneg
    (s : Multiset ℂ) (f g : ℂ → ℝ) (hs : s ≠ 0)
    (hf : ∀ x ∈ s, 0 ≤ f x) (hfg : ∀ x ∈ s, f x < g x) :
    (s.map f).prod < (s.map g).prod := by
  induction s using Multiset.induction_on with
  | empty => simp at hs
  | @cons x s ih =>
      by_cases hs0 : s = 0
      · subst s
        simpa using hfg x (by simp)
      · have hx0 := hf x (by simp)
        have hx := hfg x (by simp)
        have hgx : 0 < g x := lt_of_le_of_lt hx0 hx
        have htail0 : 0 ≤ (s.map f).prod := multiset_prod_nonneg _ (by
          intro y hy
          obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hy
          exact hf z (by simp [hz]))
        have htail := ih hs0 (by
          intro y hy
          exact hf y (by simp [hy])) (by
          intro y hy
          exact hfg y (by simp [hy]))
        simp only [Multiset.map_cons, Multiset.prod_cons]
        calc
          f x * (s.map f).prod ≤ g x * (s.map f).prod :=
            mul_le_mul_of_nonneg_right hx.le htail0
          _ < g x * (s.map g).prod := mul_lt_mul_of_pos_left htail hgx

private lemma isUnit_of_dvd_of_all_roots_far
    (P q : Polynomial ℤ) (b : ℕ) (hq : q ∣ P)
    (hu : IsUnit (Polynomial.eval (b : ℤ) q))
    (hroot : ∀ z : ℂ,
      (P.map (Int.castRingHom ℂ)).IsRoot z → 1 < ‖(b : ℂ) - z‖) :
    IsUnit q := by
  by_cases hdeg : q.natDegree = 0
  · have hqC := Polynomial.eq_C_of_natDegree_eq_zero hdeg
    rw [hqC] at hu
    rw [hqC]
    exact Polynomial.isUnit_C.mpr (by simpa using hu)
  have hdegpos : 0 < q.natDegree := Nat.pos_of_ne_zero hdeg
  let Q : Polynomial ℂ := q.map (Int.castRingHom ℂ)
  have hq0 : q ≠ 0 := by
    intro h
    subst q
    simp at hu
  have hQ0 : Q ≠ 0 := (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hq0
  have hQdeg : Q.natDegree = q.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective q
  have hroots : Q.roots ≠ 0 := by
    intro h
    have := IsAlgClosed.roots_eq_zero_iff_natDegree_eq_zero.mp h
    rw [hQdeg] at this
    exact hdeg this
  have hrootQ : ∀ z ∈ Q.roots, 1 < ‖(b : ℂ) - z‖ := by
    intro z hz
    apply hroot z
    obtain ⟨r, hr⟩ := hq
    have hm : Q * r.map (Int.castRingHom ℂ) = P.map (Int.castRingHom ℂ) := by
      simpa [Q, Polynomial.map_mul] using (congrArg (Polynomial.map (Int.castRingHom ℂ)) hr).symm
    rw [← hm, Polynomial.IsRoot.def, Polynomial.eval_mul]
    have hzQ : Q.eval z = 0 := (Polynomial.mem_roots hQ0).mp hz
    simp [hzQ]
  have hprod : 1 < (Q.roots.map fun z => ‖(b : ℂ) - z‖).prod := by
    apply one_lt_multiset_prod _ (by simpa using hroots)
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
    exact hrootQ z hz
  have hlead0 : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ0
  have hlead : 1 ≤ ‖Q.leadingCoeff‖ := by
    have hleadmap : Q.leadingCoeff = (q.leadingCoeff : ℂ) := by
      exact Polynomial.leadingCoeff_map_of_injective Int.cast_injective q
    rw [hleadmap]
    have hqlead0 : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq0
    rw [Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hqlead0
  have hformula := (IsAlgClosed.splits Q).eval_eq_prod_roots (b : ℂ)
  have hnormformula := congrArg norm hformula
  rw [norm_mul, norm_multiset_prod, Multiset.map_map] at hnormformula
  have hnormformula' :
      ‖Q.eval (b : ℂ)‖ = ‖Q.leadingCoeff‖ *
        (Q.roots.map fun z => ‖(b : ℂ) - z‖).prod := by
    simpa [Function.comp_apply] using hnormformula
  have hevalmap : Q.eval (b : ℂ) = ((Polynomial.eval (b : ℤ) q : ℤ) : ℂ) := by
    dsimp [Q]
    rw [Polynomial.eval_map]
    have hbcast : (b : ℂ) = Int.castRingHom ℂ (b : ℤ) := by norm_num
    rw [hbcast, Polynomial.eval₂_at_apply]
    rfl
  rw [hevalmap] at hnormformula'
  have hevalnorm : ‖((Polynomial.eval (b : ℤ) q : ℤ) : ℂ)‖ = 1 := by
    rcases Int.isUnit_iff.mp hu with h | h <;> rw [h] <;> norm_num
  have : 1 < ‖((Polynomial.eval (b : ℤ) q : ℤ) : ℂ)‖ := by
    rw [hnormformula']
    nlinarith [mul_pos (lt_of_lt_of_le zero_lt_one hlead) (lt_trans zero_lt_one hprod)]
  rw [hevalnorm] at this
  exact (lt_irrefl 1 this).elim

private lemma isUnit_of_dvd_of_binary_root_re_lt
    (P q : Polynomial ℤ) (hq : q ∣ P)
    (hu : IsUnit (Polynomial.eval (2 : ℤ) q))
    (hP1 : Polynomial.eval (1 : ℤ) P ≠ 0)
    (hroot : ∀ z : ℂ,
      (P.map (Int.castRingHom ℂ)).IsRoot z → z.re < (3 : ℝ) / 2) :
    IsUnit q := by
  by_cases hdeg : q.natDegree = 0
  · have hqC := Polynomial.eq_C_of_natDegree_eq_zero hdeg
    rw [hqC] at hu
    rw [hqC]
    exact Polynomial.isUnit_C.mpr (by simpa using hu)
  let Q : Polynomial ℂ := q.map (Int.castRingHom ℂ)
  have hq0 : q ≠ 0 := by
    intro h
    subst q
    simp at hu
  have hQ0 : Q ≠ 0 := (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hq0
  have hQdeg : Q.natDegree = q.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective q
  have hroots : Q.roots ≠ 0 := by
    intro h
    have := IsAlgClosed.roots_eq_zero_iff_natDegree_eq_zero.mp h
    rw [hQdeg] at this
    exact hdeg this
  have hrootQ : ∀ z ∈ Q.roots, z.re < (3 : ℝ) / 2 := by
    intro z hz
    apply hroot z
    obtain ⟨r, hr⟩ := hq
    have hm : Q * r.map (Int.castRingHom ℂ) = P.map (Int.castRingHom ℂ) := by
      simpa [Q, Polynomial.map_mul] using
        (congrArg (Polynomial.map (Int.castRingHom ℂ)) hr).symm
    rw [← hm, Polynomial.IsRoot.def, Polynomial.eval_mul]
    have hzQ : Q.eval z = 0 := (Polynomial.mem_roots hQ0).mp hz
    simp [hzQ]
  have hdist : ∀ z ∈ Q.roots, ‖(1 : ℂ) - z‖ < ‖(2 : ℂ) - z‖ := by
    intro z hz
    rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm,
      Complex.sq_norm]
    change ((1 : ℂ) - z).re * ((1 : ℂ) - z).re +
        ((1 : ℂ) - z).im * ((1 : ℂ) - z).im <
      ((2 : ℂ) - z).re * ((2 : ℂ) - z).re +
        ((2 : ℂ) - z).im * ((2 : ℂ) - z).im
    norm_num
    nlinarith [hrootQ z hz]
  have hprods :
      (Q.roots.map fun z => ‖(1 : ℂ) - z‖).prod <
        (Q.roots.map fun z => ‖(2 : ℂ) - z‖).prod := by
    exact multiset_prod_lt_prod_of_nonempty_nonneg Q.roots _ _ hroots
      (by intros; positivity) hdist
  have hleadpos : 0 < ‖Q.leadingCoeff‖ := norm_pos_iff.mpr
    (Polynomial.leadingCoeff_ne_zero.mpr hQ0)
  have hformula1 := (IsAlgClosed.splits Q).eval_eq_prod_roots (1 : ℂ)
  have hformula2 := (IsAlgClosed.splits Q).eval_eq_prod_roots (2 : ℂ)
  have hnorm1 := congrArg norm hformula1
  have hnorm2 := congrArg norm hformula2
  rw [norm_mul, norm_multiset_prod, Multiset.map_map] at hnorm1 hnorm2
  have hnorm1' :
      ‖Q.eval (1 : ℂ)‖ = ‖Q.leadingCoeff‖ *
        (Q.roots.map fun z => ‖(1 : ℂ) - z‖).prod := by
    simpa [Function.comp_apply] using hnorm1
  have hnorm2' :
      ‖Q.eval (2 : ℂ)‖ = ‖Q.leadingCoeff‖ *
        (Q.roots.map fun z => ‖(2 : ℂ) - z‖).prod := by
    simpa [Function.comp_apply] using hnorm2
  have heval_lt : ‖Q.eval (1 : ℂ)‖ < ‖Q.eval (2 : ℂ)‖ := by
    rw [hnorm1', hnorm2']
    exact mul_lt_mul_of_pos_left hprods hleadpos
  have hevalmap (k : ℤ) :
      Q.eval (k : ℂ) = ((Polynomial.eval k q : ℤ) : ℂ) := by
    dsimp [Q]
    rw [Polynomial.eval_map]
    have hkcast : (k : ℂ) = Int.castRingHom ℂ k := rfl
    rw [hkcast, Polynomial.eval₂_at_apply]
    rfl
  have hevalmap1 := hevalmap 1
  have hevalmap2 := hevalmap 2
  norm_num at hevalmap1 hevalmap2
  rw [hevalmap1, hevalmap2] at heval_lt
  have heval2 : ‖((Polynomial.eval (2 : ℤ) q : ℤ) : ℂ)‖ = 1 := by
    rcases Int.isUnit_iff.mp hu with h | h <;> rw [h] <;> norm_num
  rw [heval2] at heval_lt
  have heval1zero : Polynomial.eval (1 : ℤ) q = 0 := by
    by_contra h
    have hone : (1 : ℤ) ≤ |Polynomial.eval (1 : ℤ) q| := Int.one_le_abs h
    rw [Complex.norm_intCast] at heval_lt
    rw [← Int.cast_abs] at heval_lt
    have honeR : (1 : ℝ) ≤ (|Polynomial.eval (1 : ℤ) q| : ℤ) := by
      exact_mod_cast hone
    exact (not_lt_of_ge honeR) heval_lt
  obtain ⟨r, hr⟩ := hq
  have hevalP : Polynomial.eval (1 : ℤ) P = 0 := by
    rw [hr, Polynomial.eval_mul, heval1zero, zero_mul]
  exact (hP1 hevalP).elim

private lemma digits_getElemBang_lt_base (b p i : ℕ) (hb : 1 < b) :
    (Nat.digits b p)[i]! < b := by
  by_cases hi : i < (Nat.digits b p).length
  · rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    simp only [Option.getD_some]
    exact Nat.digits_lt_base hb (List.getElem_mem hi)
  · rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt hi)]
    simp
    omega

private lemma digits_last_getElemBang_pos (b p : ℕ) (hp : p ≠ 0) :
    1 ≤ (Nat.digits b p)[(Nat.digits b p).length - 1]! := by
  have hL : Nat.digits b p ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hp
  have hlen : 0 < (Nat.digits b p).length := by
    have : (Nat.digits b p).length ≠ 0 := by simpa using hL
    omega
  have hi : (Nat.digits b p).length - 1 < (Nat.digits b p).length := by omega
  have heq : (Nat.digits b p)[(Nat.digits b p).length - 1]! =
      (Nat.digits b p).getLast hL := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      List.getLast_eq_getElem hL]
    simp only [Option.getD_some]
  rw [heq]
  exact Nat.one_le_iff_ne_zero.mpr (Nat.getLast_digit_ne_zero b hp)

private lemma digitPolynomial_map_root_sum
    (b p : ℕ) (z : ℂ)
    (hz : (Polynomial.map (Int.castRingHom ℂ)
      (∑ i ∈ Finset.range (Nat.digits b p).length,
        Polynomial.monomial i ((Nat.digits b p)[i]! : ℤ) : Polynomial ℤ)).IsRoot z) :
    ∑ i ∈ Finset.range (Nat.digits b p).length,
      ((Nat.digits b p)[i]! : ℂ) * z ^ i = 0 := by
  rw [Polynomial.IsRoot.def] at hz
  rw [Polynomial.eval_map, Polynomial.eval₂_finsetSum] at hz
  simpa using hz

private lemma digitPolynomial_roots_far
    (b p : ℕ) (hp : p ≠ 0) (hb : 3 ≤ b) (z : ℂ)
    (hz : (Polynomial.map (Int.castRingHom ℂ)
      (∑ i ∈ Finset.range (Nat.digits b p).length,
        Polynomial.monomial i ((Nat.digits b p)[i]! : ℤ) : Polynomial ℤ)).IsRoot z) :
    1 < ‖(b : ℂ) - z‖ := by
  let L := Nat.digits b p
  let n := L.length - 1
  have hL : L ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hp
  have hlenpos : 0 < L.length := by
    have : L.length ≠ 0 := by simpa using hL
    omega
  have hlen : L.length = n + 1 := by omega
  have hzsum := digitPolynomial_map_root_sum b p z hz
  change ∑ i ∈ Finset.range L.length, (L[i]! : ℂ) * z ^ i = 0 at hzsum
  rw [hlen] at hzsum
  by_cases hn : n = 0
  · have hlen1 : L.length = 1 := by omega
    rw [hn] at hzsum
    norm_num [Finset.sum_range_succ] at hzsum
    have hlead : 1 ≤ L[0]! := by
      have h := digits_last_getElemBang_pos b p hp
      simpa [L, hlen1] using h
    have hne : (L[0]! : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hlead)
    exfalso
    apply hne
    simpa [List.getElem!_eq_getElem?_getD] using hzsum
  · apply complex_sum_root_dist_gt_one b n (fun i => L[i]!) z (Nat.one_le_iff_ne_zero.mpr hn)
      (by simpa [L, n] using digits_last_getElemBang_pos b p hp)
      (fun i => by simpa [L] using digits_getElemBang_lt_base b p i (by omega)) hb hzsum

private lemma digitPolynomial_binary_roots_re_lt
    (p : ℕ) (hp : p ≠ 0) (z : ℂ)
    (hz : (Polynomial.map (Int.castRingHom ℂ)
      (∑ i ∈ Finset.range (Nat.digits 2 p).length,
        Polynomial.monomial i ((Nat.digits 2 p)[i]! : ℤ) : Polynomial ℤ)).IsRoot z) :
    z.re < (3 : ℝ) / 2 := by
  let L := Nat.digits 2 p
  let n := L.length - 1
  have hL : L ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hp
  have hlenpos : 0 < L.length := by
    have : L.length ≠ 0 := by simpa using hL
    omega
  have hlen : L.length = n + 1 := by omega
  have hzsum := digitPolynomial_map_root_sum 2 p z hz
  change ∑ i ∈ Finset.range L.length, (L[i]! : ℂ) * z ^ i = 0 at hzsum
  rw [hlen] at hzsum
  apply complex_binary_sum_root_re_lt n (fun i => L[i]!) z
    (by simpa [L, n] using digits_last_getElemBang_pos 2 p hp)
    (fun i => by simpa [L] using digits_getElemBang_lt_base 2 p i (by omega)) hzsum

private lemma digitPolynomial_eval_one_ne_zero (b p : ℕ) (hp : p ≠ 0) :
    Polynomial.eval (1 : ℤ)
      (∑ i ∈ Finset.range (Nat.digits b p).length,
        Polynomial.monomial i ((Nat.digits b p)[i]! : ℤ) : Polynomial ℤ) ≠ 0 := by
  let L := Nat.digits b p
  let n := L.length - 1
  have hL : L ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hp
  have hlenpos : 0 < L.length := by
    have : L.length ≠ 0 := by simpa using hL
    omega
  have hnmem : n ∈ Finset.range L.length := Finset.mem_range.mpr (by omega)
  have hlead : 1 ≤ L[n]! := by
    simpa [L, n] using digits_last_getElemBang_pos b p hp
  rw [Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial, one_pow, mul_one]
  have hle : L[n]! ≤ ∑ i ∈ Finset.range L.length, L[i]! := by
    exact Finset.single_le_sum (fun i _ => Nat.zero_le _) hnmem
  have hpos : 0 < ∑ i ∈ Finset.range L.length, L[i]! := lt_of_lt_of_le hlead hle
  exact_mod_cast (Nat.ne_of_gt hpos)

private lemma eval_digitPolynomial (b p : ℕ) :
    Polynomial.eval (b : ℤ) (∑ i ∈ Finset.range (Nat.digits b p).length,
      Polynomial.monomial i ((Nat.digits b p)[i]! : ℤ) : Polynomial ℤ) = (p : ℤ) := by
  rw [Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial]
  norm_cast
  have hp := Nat.ofDigits_digits b p
  rw [Nat.ofDigits_eq_sum_mapIdx] at hp
  calc
    ∑ x ∈ Finset.range (b.digits p).length, (b.digits p)[x]! * b ^ x =
        (List.mapIdx (fun i a => a * b ^ i) (b.digits p)).sum := by
      rw [List.mapIdx_eq_ofFn, List.sum_ofFn]
      simpa [List.get_eq_getElem] using
        (Fin.sum_univ_eq_sum_range
          (fun i => (b.digits p)[i]! * b ^ i) (b.digits p).length).symm
    _ = p := hp

private lemma irreducible_of_prime_eval_of_unit_reflects_on_divisors
    (f : Polynomial ℤ) (b : ℤ) (hp : Prime (Polynomial.eval b f))
    (hreflect : ∀ g : Polynomial ℤ, g ∣ f → IsUnit (Polynomial.eval b g) → IsUnit g) :
    Irreducible f := by
  rw [irreducible_iff]
  constructor
  · intro hf
    exact hp.not_isUnit (hf.map (Polynomial.evalRingHom b))
  · intro g h hfactor
    have heval : Polynomial.eval b f = Polynomial.eval b g * Polynomial.eval b h := by
      rw [hfactor, Polynomial.eval_mul]
    rcases hp.irreducible.isUnit_or_isUnit heval with hg | hh
    · exact Or.inl (hreflect g (by use h) hg)
    · exact Or.inr (hreflect h (by use g; rw [hfactor, mul_comm]) hh)

/-- **Cohn's irreducibility criterion.** Let $b \ge 2$ be an integer and let $p$ be a prime whose
base-$b$ digits are $a_0, a_1, \dots, a_n$, with units digit $a_0$ and leading digit $a_n \ne 0$.
Then the polynomial $f(x) = a_0 + a_1 x + \dots + a_n x^n$ is irreducible in $\mathbb{Z}[x]$.

Proves `Wanted` entry `cohn_criterion`.

Source: https://en.wikipedia.org/wiki/Cohn%27s_irreducibility_criterion
-/
theorem cohn_criterion (b p : ℕ) (hp : Nat.Prime p) (hb : 2 ≤ b) :
    Irreducible (∑ i ∈ Finset.range (Nat.digits b p).length,
      Polynomial.monomial i ((Nat.digits b p)[i]! : ℤ) : Polynomial ℤ) := by
  let P : Polynomial ℤ := ∑ i ∈ Finset.range (Nat.digits b p).length,
    Polynomial.monomial i ((Nat.digits b p)[i]! : ℤ)
  have heval : Polynomial.eval (b : ℤ) P = (p : ℤ) := by
    simpa [P] using eval_digitPolynomial b p
  apply irreducible_of_prime_eval_of_unit_reflects_on_divisors P (b : ℤ)
  · rw [heval]
    exact Nat.prime_iff_prime_int.mp hp
  · intro q hq hu
    rcases eq_or_lt_of_le hb with hb2 | hb3
    · subst b
      apply isUnit_of_dvd_of_binary_root_re_lt P q hq hu
      · simpa [P] using digitPolynomial_eval_one_ne_zero 2 p hp.ne_zero
      · intro z hz
        exact digitPolynomial_binary_roots_re_lt p hp.ne_zero z (by simpa [P] using hz)
    · apply isUnit_of_dvd_of_all_roots_far P q b hq hu
      intro z hz
      exact digitPolynomial_roots_far b p hp.ne_zero hb3 z (by simpa [P] using hz)

end

end MetaMathlibExt
