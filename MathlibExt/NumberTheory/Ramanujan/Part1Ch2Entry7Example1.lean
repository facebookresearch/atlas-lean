/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 2, Entry 7, Example 1

Sum of arctan(2/(n+k+1)²) evaluates via arctan((2n+1)/(n²+n-1)).
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2

namespace Entry7Example1

private lemma halg_core (s : ℝ) (h1 : s ^ 2 + s - 1 ≠ 0) (h2 : (s + 1) ^ 2 + (s + 1) - 1 ≠ 0)
    (hv : (s + 1) ^ 2 ≠ 0)
    (hden : (1 + ((2 * s + 1) / (s ^ 2 + s - 1)) * ((2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1))) ≠ 0) :
    (((2 * s + 1) / (s ^ 2 + s - 1) - ((2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1))) /
    (1 + ((2 * s + 1) / (s ^ 2 + s - 1)) * ((2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1)))) =
    2 / (s + 1) ^ 2 := by
  have key : (s + 1) ^ 2 * ((2 * s + 1) * ((s + 1) ^ 2 + (s + 1) - 1) - (2 * (s + 1) + 1) * (s ^ 2 + s - 1)) =
    2 * ((s ^ 2 + s - 1) * ((s + 1) ^ 2 + (s + 1) - 1) + (2 * s + 1) * (2 * (s + 1) + 1)) := by ring
  have hprod : (s ^ 2 + s - 1) * ((s + 1) ^ 2 + (s + 1) - 1) ≠ 0 := mul_ne_zero h1 h2
  rw [div_eq_div_iff hden hv]
  have e : ((s ^ 2 + s - 1) * ((s + 1) ^ 2 + (s + 1) - 1)) *
      (((2 * s + 1) / (s ^ 2 + s - 1) - (2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1)) * (s + 1) ^ 2)
      = (((2 * s + 1) * ((s + 1) ^ 2 + (s + 1) - 1) - (2 * (s + 1) + 1) * (s ^ 2 + s - 1))) * (s + 1) ^ 2 := by
    rw [div_sub_div _ _ h1 h2, div_mul_eq_mul_div, mul_div_cancel₀ _ hprod]
    ring
  have e2 : ((s ^ 2 + s - 1) * ((s + 1) ^ 2 + (s + 1) - 1)) *
      (2 * (1 + (2 * s + 1) / (s ^ 2 + s - 1) * ((2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1))))
      = 2 * ((s ^ 2 + s - 1) * ((s + 1) ^ 2 + (s + 1) - 1) + (2 * s + 1) * (2 * (s + 1) + 1)) := by
    rw [div_mul_div_comm]
    have hP : ((s ^ 2 + s - 1) * ((s + 1) ^ 2 + (s + 1) - 1)) *
        (1 + (2 * s + 1) * (2 * (s + 1) + 1) / ((s ^ 2 + s - 1) * ((s + 1) ^ 2 + (s + 1) - 1)))
        = ((s ^ 2 + s - 1) * ((s + 1) ^ 2 + (s + 1) - 1) + (2 * s + 1) * (2 * (s + 1) + 1)) := by
      rw [mul_add, mul_one, mul_div_cancel₀ _ hprod]
    linear_combination 2 * hP
  apply mul_left_cancel₀ hprod
  linear_combination e - e2 + key

private lemma halg_of_pos (s : ℝ) (hs : 0 < s) (h1 : s ^ 2 + s - 1 ≠ 0) :
    (((2 * s + 1) / (s ^ 2 + s - 1) - ((2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1))) /
    (1 + ((2 * s + 1) / (s ^ 2 + s - 1)) * ((2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1)))) =
    2 / (s + 1) ^ 2 := by
  have hs1 : (0 : ℝ) < s + 1 := by linarith
  have h2 : (s + 1) ^ 2 + (s + 1) - 1 ≠ 0 := by
    have : (0 : ℝ) < (s + 1) ^ 2 + (s + 1) - 1 := by nlinarith [sq_nonneg (s + 1)]
    exact ne_of_gt this
  have hv : (s + 1) ^ 2 ≠ 0 := by positivity
  have hprod : (s ^ 2 + s - 1) * ((s + 1) ^ 2 + (s + 1) - 1) ≠ 0 := mul_ne_zero h1 h2
  have hD : (s ^ 2 + s - 1) * ((s + 1) ^ 2 + (s + 1) - 1) + (2 * s + 1) * (2 * (s + 1) + 1)
      = (s + 1) ^ 2 * ((s + 1) ^ 2 + 1) := by ring
  have hDne : (s ^ 2 + s - 1) * ((s + 1) ^ 2 + (s + 1) - 1) + (2 * s + 1) * (2 * (s + 1) + 1) ≠ 0 := by
    rw [hD]
    apply mul_ne_zero hv
    have : (0 : ℝ) < (s + 1) ^ 2 + 1 := by positivity
    exact ne_of_gt this
  have h1ab : (1 + ((2 * s + 1) / (s ^ 2 + s - 1)) * ((2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1)))
      = ((s ^ 2 + s - 1) * ((s + 1) ^ 2 + (s + 1) - 1) + (2 * s + 1) * (2 * (s + 1) + 1)) /
        ((s ^ 2 + s - 1) * ((s + 1) ^ 2 + (s + 1) - 1)) := by
    rw [div_mul_div_comm]
    rw [eq_div_iff hprod]
    rw [add_mul, one_mul, div_mul_cancel₀ _ hprod]
  have hden : (1 + ((2 * s + 1) / (s ^ 2 + s - 1)) * ((2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1))) ≠ 0 := by
    rw [h1ab]
    exact div_ne_zero hDne hprod
  exact halg_core s h1 h2 hv hden

private lemma harctan_sub_of_pos (s : ℝ) (hs : 0 < s)
    (hd1 : 0 < s ^ 2 + s - 1) (hd2 : 0 < (s + 1) ^ 2 + (s + 1) - 1)
    (halg : (((2 * s + 1) / (s ^ 2 + s - 1) - ((2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1))) /
      (1 + ((2 * s + 1) / (s ^ 2 + s - 1)) * ((2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1)))) =
      2 / (s + 1) ^ 2) :
    Real.arctan ((2 * s + 1) / (s ^ 2 + s - 1)) - Real.arctan ((2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1))
      = Real.arctan (2 / (s + 1) ^ 2) := by
  have hn1 : (0 : ℝ) < 2 * s + 1 := by linarith
  have hn2 : (0 : ℝ) < 2 * (s + 1) + 1 := by linarith
  have ha : (0 : ℝ) < (2 * s + 1) / (s ^ 2 + s - 1) := div_pos hn1 hd1
  have hb : (0 : ℝ) < (2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1) := div_pos hn2 hd2
  have hlt : ((2 * s + 1) / (s ^ 2 + s - 1)) * (-((2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1))) < 1 := by
    have : ((2 * s + 1) / (s ^ 2 + s - 1)) * (-((2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1)))
        = -(((2 * s + 1) / (s ^ 2 + s - 1)) * ((2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1))) := by ring
    rw [this]
    have hpos : (0 : ℝ) < ((2 * s + 1) / (s ^ 2 + s - 1)) * ((2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1)) :=
      mul_pos ha hb
    linarith
  have hadd := Real.arctan_add (x := (2 * s + 1) / (s ^ 2 + s - 1)) (y := -((2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1))) hlt
  rw [Real.arctan_neg] at hadd
  have earg : (((2 * s + 1) / (s ^ 2 + s - 1) + -((2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1))) /
      (1 - (2 * s + 1) / (s ^ 2 + s - 1) * (-((2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1)))))
      = (((2 * s + 1) / (s ^ 2 + s - 1) - (2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1)) /
        (1 + ((2 * s + 1) / (s ^ 2 + s - 1)) * ((2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1)))) := by
    congr 1 <;> ring
  rw [earg, halg] at hadd
  have hsub : Real.arctan ((2 * s + 1) / (s ^ 2 + s - 1)) - Real.arctan ((2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1))
      = Real.arctan ((2 * s + 1) / (s ^ 2 + s - 1)) + -(Real.arctan ((2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1))) := by ring
  rw [hsub]
  exact hadd

private lemma hstep_pos (s : ℝ) (hs1 : 1 < s) :
    Real.arctan (2 / (s + 1) ^ 2)
      = Real.arctan ((2 * s + 1) / (s ^ 2 + s - 1))
        - Real.arctan ((2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1)) := by
  have hs : (0 : ℝ) < s := by linarith
  have hd1 : (0 : ℝ) < s ^ 2 + s - 1 := by nlinarith [sq_nonneg s]
  have hd2 : (0 : ℝ) < (s + 1) ^ 2 + (s + 1) - 1 := by nlinarith [sq_nonneg (s + 1)]
  have halg := halg_of_pos s hs (ne_of_gt hd1)
  have h := harctan_sub_of_pos s hs hd1 hd2 halg
  linarith [h]

private lemma hstep_zero_pos (n : ℝ) (hn_pos : 0 < n) (hd : 0 < n ^ 2 + n - 1) :
    Real.arctan (2 / (n + 1) ^ 2)
      = Real.arctan ((2 * n + 1) / (n ^ 2 + n - 1))
        - Real.arctan ((2 * (n + 1) + 1) / ((n + 1) ^ 2 + (n + 1) - 1)) := by
  have hd2 : (0 : ℝ) < (n + 1) ^ 2 + (n + 1) - 1 := by nlinarith [sq_nonneg (n + 1)]
  have halg := halg_of_pos n hn_pos (ne_of_gt hd)
  have h := harctan_sub_of_pos n hn_pos hd hd2 halg
  linarith [h]

private lemma hgt_of_neg (n1 n2 d1 d2 : ℝ)
    (hn1 : 0 < n1) (hn2 : 0 < n2) (hd1 : d1 < 0) (hd2 : 0 < d2)
    (hD : 0 < d1 * d2 + n1 * n2) :
    1 < (n1 / d1) * (-(n2 / d2)) := by
  have hA : (0 : ℝ) < n1 * n2 := mul_pos hn1 hn2
  have hPneg : d1 * d2 < 0 := mul_neg_of_neg_of_pos hd1 hd2
  have hneg : (0 : ℝ) < -(d1 * d2) := neg_pos.mpr hPneg
  have hlt : -(d1 * d2) < n1 * n2 := by linarith
  have e1 : (n1 / d1) * (-(n2 / d2)) = (n1 * n2) / (-(d1 * d2)) := by
    rw [← neg_div, div_mul_div_comm, mul_neg, neg_div, div_neg]
  rw [e1]
  exact (one_lt_div hneg).mpr hlt

private lemma harctan_sub_of_neg (s : ℝ)
    (ha_neg : (2 * s + 1) / (s ^ 2 + s - 1) < 0)
    (hgt : 1 < ((2 * s + 1) / (s ^ 2 + s - 1)) * (-((2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1))))
    (halg : (((2 * s + 1) / (s ^ 2 + s - 1) - ((2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1))) /
      (1 + ((2 * s + 1) / (s ^ 2 + s - 1)) * ((2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1)))) =
      2 / (s + 1) ^ 2) :
    Real.arctan (2 / (s + 1) ^ 2)
      = Real.arctan ((2 * s + 1) / (s ^ 2 + s - 1)) - Real.arctan ((2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1))
        + Real.pi := by
  have hadd := Real.arctan_add_eq_sub_pi
    (x := (2 * s + 1) / (s ^ 2 + s - 1)) (y := -((2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1))) hgt ha_neg
  rw [Real.arctan_neg] at hadd
  have earg : (((2 * s + 1) / (s ^ 2 + s - 1) + -((2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1))) /
      (1 - (2 * s + 1) / (s ^ 2 + s - 1) * (-((2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1)))))
      = (((2 * s + 1) / (s ^ 2 + s - 1) - (2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1)) /
        (1 + ((2 * s + 1) / (s ^ 2 + s - 1)) * ((2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1)))) := by
    congr 1 <;> ring
  rw [earg, halg] at hadd
  have hsub : Real.arctan ((2 * s + 1) / (s ^ 2 + s - 1)) - Real.arctan ((2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1))
      = Real.arctan ((2 * s + 1) / (s ^ 2 + s - 1)) + -(Real.arctan ((2 * (s + 1) + 1) / ((s + 1) ^ 2 + (s + 1) - 1))) := by ring
  linarith [hadd, hsub]

private lemma hstep_zero_neg (n : ℝ) (hn_pos : 0 < n) (hd : n ^ 2 + n - 1 < 0) :
    Real.arctan (2 / (n + 1) ^ 2)
      = Real.arctan ((2 * n + 1) / (n ^ 2 + n - 1))
        - Real.arctan ((2 * (n + 1) + 1) / ((n + 1) ^ 2 + (n + 1) - 1))
        + Real.pi := by
  have hd2 : (0 : ℝ) < (n + 1) ^ 2 + (n + 1) - 1 := by nlinarith [sq_nonneg (n + 1)]
  have h1 : n ^ 2 + n - 1 ≠ 0 := ne_of_lt hd
  have halg := halg_of_pos n hn_pos h1
  have hn1 : (0 : ℝ) < 2 * n + 1 := by linarith
  have hn2 : (0 : ℝ) < 2 * (n + 1) + 1 := by linarith
  have ha_neg : (2 * n + 1) / (n ^ 2 + n - 1) < 0 := div_neg_of_pos_of_neg hn1 hd
  have hD : (0 : ℝ) < (n ^ 2 + n - 1) * ((n + 1) ^ 2 + (n + 1) - 1) + (2 * n + 1) * (2 * (n + 1) + 1) := by
    have hDeq : (n ^ 2 + n - 1) * ((n + 1) ^ 2 + (n + 1) - 1) + (2 * n + 1) * (2 * (n + 1) + 1)
        = (n + 1) ^ 2 * ((n + 1) ^ 2 + 1) := by ring
    rw [hDeq]
    have hn1' : (0 : ℝ) < n + 1 := by linarith
    have hsq : (0 : ℝ) < (n + 1) ^ 2 := pow_pos hn1' 2
    have hplus : (0 : ℝ) < (n + 1) ^ 2 + 1 := by linarith
    exact mul_pos hsq hplus
  have hgt := hgt_of_neg (2 * n + 1) (2 * (n + 1) + 1) (n ^ 2 + n - 1) ((n + 1) ^ 2 + (n + 1) - 1)
    hn1 hn2 hd hd2 hD
  exact harctan_sub_of_neg n ha_neg hgt halg

private lemma hden0 (n : ℝ) (hn_pos : 0 < n) (hn_ne : n ≠ (Real.sqrt 5 - 1) / 2) :
    n ^ 2 + n - 1 ≠ 0 := by
  intro h
  apply hn_ne
  have h2 : (2 * n + 1) ^ 2 = 5 := by linear_combination 4 * h
  have hpos : (0 : ℝ) < 2 * n + 1 := by linarith
  have hsq : 2 * n + 1 = Real.sqrt 5 := by
    conv_lhs => rw [← Real.sqrt_sq (le_of_lt hpos), h2]
  linarith

private lemma hsign (n : ℝ) (hn_pos : 0 < n) :
    (n < (Real.sqrt 5 - 1) / 2 ↔ n ^ 2 + n - 1 < 0) := by
  have h2 : (2 * n + 1) ^ 2 - 5 = 4 * (n ^ 2 + n - 1) := by ring
  have hsq5 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : (0 : ℝ) < 2 * n + 1 := by linarith
  have h5pos : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  constructor
  · intro hlt
    have h21 : 2 * n + 1 < Real.sqrt 5 := by linarith
    have hsq : (2 * n + 1) ^ 2 < (Real.sqrt 5) ^ 2 := by
      have := (pow_lt_pow_iff_left₀ (le_of_lt hpos) (le_of_lt h5pos) (by norm_num : (2 : ℕ) ≠ 0)).mpr h21
      simpa using this
    nlinarith
  · intro hlt
    have hsq : (2 * n + 1) ^ 2 < (Real.sqrt 5) ^ 2 := by nlinarith
    have habs : |2 * n + 1| < Real.sqrt 5 := abs_lt_of_sq_lt_sq hsq (le_of_lt h5pos)
    rw [abs_of_pos hpos] at habs
    linarith

private lemma hsum (n : ℝ) (hn_pos : 0 < n)
    (f : ℕ → ℝ) (hf : f = fun k : ℕ => Real.arctan (2 / ((n + (k : ℝ) + 1) ^ 2))) :
    Summable f := by
  rw [hf]
  have hbase : Summable (fun m : ℕ => (1 : ℝ) / (((m : ℝ)) ^ 2)) :=
    (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  have hshift : Summable (fun k : ℕ => (1 : ℝ) / (((((k + 1 : ℕ)) : ℝ)) ^ 2)) :=
    (summable_nat_add_iff 1).mpr hbase
  have hmaj : Summable (fun k : ℕ => (2 : ℝ) / ((((k : ℝ)) + 1) ^ 2)) := by
    have e : (fun k : ℕ => (2 : ℝ) / ((((k : ℝ)) + 1) ^ 2))
        = (fun k : ℕ => 2 * ((1 : ℝ) / (((((k + 1 : ℕ)) : ℝ)) ^ 2))) := by
      funext k
      push_cast
      ring
    rw [e]
    exact hshift.mul_left 2
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hmaj
  · show (0 : ℝ) ≤ Real.arctan (2 / ((n + ((k : ℝ)) + 1) ^ 2))
    rw [Real.arctan_nonneg]
    positivity
  · show Real.arctan (2 / ((n + ((k : ℝ)) + 1) ^ 2)) ≤ (2 : ℝ) / ((((k : ℝ)) + 1) ^ 2)
    have hnn : (0 : ℝ) ≤ n := le_of_lt hn_pos
    have h1 : (0 : ℝ) ≤ 2 / ((n + ((k : ℝ)) + 1) ^ 2) := by positivity
    have h2 := Real.arctan_le_self h1
    have h3 : (2 : ℝ) / ((n + ((k : ℝ)) + 1) ^ 2) ≤ 2 / ((((k : ℝ)) + 1) ^ 2) := by
      have hk1 : (0 : ℝ) < ((k : ℝ)) + 1 := by positivity
      have hC : (0 : ℝ) < ((((k : ℝ)) + 1) ^ 2) := pow_pos hk1 2
      have ha : (0 : ℝ) ≤ ((k : ℝ)) + 1 := le_of_lt hk1
      have hab : ((k : ℝ)) + 1 ≤ n + ((k : ℝ)) + 1 := by linarith [hnn]
      have hle : ((((k : ℝ)) + 1) ^ 2) ≤ ((n + ((k : ℝ)) + 1) ^ 2) :=
        pow_le_pow_left₀ ha hab 2
      exact div_le_div_of_nonneg_left (by norm_num) hC hle
    exact le_trans h2 h3

private lemma hTlim (n : ℝ) (hn_pos : 0 < n)
    (T : ℕ → ℝ)
    (hT : T = fun k : ℕ => Real.arctan ((2 * (n + (k : ℝ)) + 1) / ((n + (k : ℝ)) ^ 2 + (n + (k : ℝ)) - 1))) :
    Filter.Tendsto T Filter.atTop (nhds 0) := by
  have hu0 : Filter.Tendsto (fun N : ℕ => (2 * (n + ((N : ℝ))) + 1) / ((n + ((N : ℝ))) ^ 2 + (n + ((N : ℝ))) - 1))
      Filter.atTop (nhds 0) := by
    have h3 : Filter.Tendsto (fun N : ℕ => (3 : ℝ) / (((N : ℝ)))) Filter.atTop (nhds 0) := by
      have h := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
      have h2 := h.const_mul (3 : ℝ)
      rw [mul_zero] at h2
      exact h2.congr (fun x => mul_one_div _ _)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h3 ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      have hNr : (1 : ℝ) ≤ ((N : ℝ)) := by exact_mod_cast hN
      have hs : (1 : ℝ) ≤ n + ((N : ℝ)) := by linarith [hn_pos]
      have hnum : (0 : ℝ) < 2 * (n + ((N : ℝ))) + 1 := by linarith
      have hden : (0 : ℝ) < (n + ((N : ℝ))) ^ 2 + (n + ((N : ℝ))) - 1 := by
        nlinarith [sq_nonneg (n + ((N : ℝ)))]
      show (0 : ℝ) ≤ (2 * (n + ((N : ℝ))) + 1) / ((n + ((N : ℝ))) ^ 2 + (n + ((N : ℝ))) - 1)
      exact le_of_lt (div_pos hnum hden)
    · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      have hNr : (1 : ℝ) ≤ ((N : ℝ)) := by exact_mod_cast hN
      have hN0 : (0 : ℝ) < ((N : ℝ)) := by linarith
      have hs : (1 : ℝ) ≤ n + ((N : ℝ)) := by linarith [hn_pos]
      have hspos : (0 : ℝ) < n + ((N : ℝ)) := by linarith
      have hNs : ((N : ℝ)) ≤ n + ((N : ℝ)) := by linarith [le_of_lt hn_pos]
      have hnum : 2 * (n + ((N : ℝ))) + 1 ≤ 3 * (n + ((N : ℝ))) := by linarith
      have hden_ge : (n + ((N : ℝ))) ^ 2 ≤ (n + ((N : ℝ))) ^ 2 + (n + ((N : ℝ))) - 1 := by
        have : (0 : ℝ) ≤ (n + ((N : ℝ))) - 1 := by linarith
        linarith
      have hden_pos : (0 : ℝ) < (n + ((N : ℝ))) ^ 2 + (n + ((N : ℝ))) - 1 := by
        nlinarith [sq_nonneg (n + ((N : ℝ)))]
      have hsq_pos : (0 : ℝ) < (n + ((N : ℝ))) ^ 2 := pow_pos hspos 2
      show (2 * (n + ((N : ℝ))) + 1) / ((n + ((N : ℝ))) ^ 2 + (n + ((N : ℝ))) - 1) ≤ (3 : ℝ) / (((N : ℝ)))
      calc (2 * (n + ((N : ℝ))) + 1) / ((n + ((N : ℝ))) ^ 2 + (n + ((N : ℝ))) - 1)
          ≤ (3 * (n + ((N : ℝ)))) / ((n + ((N : ℝ))) ^ 2 + (n + ((N : ℝ))) - 1) :=
            (div_le_div_iff_of_pos_right hden_pos).mpr hnum
        _ ≤ (3 * (n + ((N : ℝ)))) / ((n + ((N : ℝ))) ^ 2) :=
            div_le_div_of_nonneg_left (by positivity) hsq_pos hden_ge
        _ = 3 / (n + ((N : ℝ))) := by
            have hsne : n + ((N : ℝ)) ≠ 0 := ne_of_gt hspos
            field_simp
        _ ≤ 3 / (((N : ℝ))) :=
            div_le_div_of_nonneg_left (by norm_num) hN0 hNs
  have hcomp : Filter.Tendsto
      (fun N : ℕ => Real.arctan ((2 * (n + ((N : ℝ))) + 1) / ((n + ((N : ℝ))) ^ 2 + (n + ((N : ℝ))) - 1)))
      Filter.atTop (nhds 0) := by
    have hcc := (Real.continuous_arctan.tendsto 0).comp hu0
    rw [Real.arctan_zero] at hcc
    exact hcc
  rw [hT]
  exact hcomp

private lemma hpart (n : ℝ)
    (f T : ℕ → ℝ)
    (hzero : f 0 = T 0 - T 1 + (if n < (Real.sqrt 5 - 1) / 2 then Real.pi else 0))
    (hsucc : ∀ k : ℕ, f (k + 1) = T (k + 1) - T ((k + 1) + 1)) :
    ∀ N : ℕ, ∑ k ∈ Finset.range (N + 1), f k
      = (T 0 + (if n < (Real.sqrt 5 - 1) / 2 then Real.pi else 0)) - T (N + 1) := by
  intro N
  induction N with
  | zero =>
    show ∑ k ∈ Finset.range 1, f k
      = (T 0 + (if n < (Real.sqrt 5 - 1) / 2 then Real.pi else 0)) - T 1
    rw [Finset.sum_range_one, hzero]
    ring
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, hsucc N]
    ring

/-- **Arctangent series over consecutive shifts (Entry 7, Example 1).** Let $n > 0$ be a real
number with $n \ne (\sqrt{5} - 1)/2$. Then the series
$$\sum_{k=0}^{\infty} \arctan \frac{2}{(n + k + 1)^2}$$
converges absolutely; its sum is $\arctan \frac{2n + 1}{n^2 + n - 1}$ when $n > (\sqrt{5} - 1)/2$,
and $\arctan \frac{2n + 1}{n^2 + n - 1} + \pi$ when $n < (\sqrt{5} - 1)/2$. Here $\arctan$ is the
principal branch, with values in $(-\pi/2, \pi/2)$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 2, Entry
    7, Example 1, formula (7.4), printed p. 36 / PDF p. 46.
Proves `Wanted` entry `ramanujan_part1_ch2_entry7_example1`.
-/
theorem ramanujan_part1_ch2_entry7_example1 (n : ℝ)
    (hn_pos : 0 < n) (hn_ne : n ≠ (Real.sqrt 5 - 1) / 2) :
    HasSum (fun k : ℕ => Real.arctan (2 / ((n + (k : ℝ) + 1) ^ 2)))
      (Real.arctan ((2 * n + 1) / (n ^ 2 + n - 1)) + if n < (Real.sqrt 5 - 1) / 2 then Real.pi else
          0) := by
  set f : ℕ → ℝ := fun k : ℕ => Real.arctan (2 / ((n + (k : ℝ) + 1) ^ 2)) with hf
  set T : ℕ → ℝ := fun k : ℕ => Real.arctan ((2 * (n + (k : ℝ)) + 1) / ((n + (k : ℝ)) ^ 2 + (n + (k : ℝ)) - 1)) with hT
  set C : ℝ := Real.arctan ((2 * n + 1) / (n ^ 2 + n - 1)) + (if n < (Real.sqrt 5 - 1) / 2 then Real.pi else 0) with hC
  have hT0 : T 0 = Real.arctan ((2 * n + 1) / (n ^ 2 + n - 1)) := by simp [hT]
  have hf0 : f 0 = Real.arctan (2 / (n + 1) ^ 2) := by simp [hf]
  have hT1 : T 1 = Real.arctan ((2 * (n + 1) + 1) / ((n + 1) ^ 2 + (n + 1) - 1)) := by simp [hT]
  have hzero : f 0 = T 0 - T 1 + (if n < (Real.sqrt 5 - 1) / 2 then Real.pi else 0) := by
    by_cases hlt : n < (Real.sqrt 5 - 1) / 2
    · have hd := (hsign n hn_pos).mp hlt
      have hstep := hstep_zero_neg n hn_pos hd
      rw [hf0, hT0, hT1, ite_eq_left hlt]
      linarith [hstep]
    · have hdpos : 0 < n ^ 2 + n - 1 := by
        have hne := hden0 n hn_pos hn_ne
        have hiff := hsign n hn_pos
        by_contra hcon
        push_neg at hcon
        have hlt' : n ^ 2 + n - 1 < 0 := lt_of_le_of_ne hcon hne
        exact hlt (hiff.mpr hlt')
      have hstep := hstep_zero_pos n hn_pos hdpos
      rw [hf0, hT0, hT1, ite_eq_right hlt]
      linarith [hstep]
  have hsucc : ∀ k : ℕ, f (k + 1) = T (k + 1) - T ((k + 1) + 1) := by
    intro k
    have hs1 : (1 : ℝ) < n + (((k + 1 : ℕ) : ℝ)) := by
      have h1k : 1 ≤ k + 1 := Nat.le_add_left 1 k
      have hk : (1 : ℝ) ≤ (((k + 1 : ℕ) : ℝ)) := by exact_mod_cast h1k
      linarith [hn_pos]
    have hstep := hstep_pos (n + (((k + 1 : ℕ) : ℝ))) hs1
    have e1 : n + (((k + 1 : ℕ) : ℝ)) + 1 = n + ((((k + 1 : ℕ) + 1 : ℕ) : ℝ)) := by
      push_cast
      ring
    simp only [hf, hT]
    rw [← e1]
    exact hstep
  have hpart := hpart n f T hzero hsucc
  have hpartC : ∀ N : ℕ, ∑ k ∈ Finset.range (N + 1), f k = C - T (N + 1) := by
    intro N
    have h := hpart N
    rw [hT0] at h
    rw [hC]
    exact h
  have hsum := hsum n hn_pos f hf
  have hTlim := hTlim n hn_pos T hT
  have hCconst : Filter.Tendsto (fun _ : ℕ => C) Filter.atTop (nhds C) := tendsto_const_nhds
  have hg : Filter.Tendsto (fun N : ℕ => C - T N) Filter.atTop (nhds C) := by
    have h := hCconst.sub hTlim
    simpa using h
  have hev : (fun N : ℕ => C - T N) =ᶠ[Filter.atTop] (fun N : ℕ => ∑ k ∈ Finset.range N, f k) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
    exact (hpartC M).symm
  have htend : Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, f k) Filter.atTop (nhds C) :=
    Filter.Tendsto.congr' hev hg
  exact (Summable.hasSum_iff_tendsto_nat hsum).mpr htend

end Entry7Example1

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2
