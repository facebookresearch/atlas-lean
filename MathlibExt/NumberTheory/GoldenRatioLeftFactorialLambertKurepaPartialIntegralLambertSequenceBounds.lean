/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import MathlibExt.Analysis.SpecialFunctions.LambertWFunction
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import MathlibExt.NumberTheory.GoldenRatioLeftFactorialLambertKurepaPartialIntegralGoldenFactorialExponentBounds

/-!
# Lambert bounds for the left factorial

We prove `kurepaPartialIntegral_lambertSequence_bounds`: for `n ≥ 5`, Kurepa's partial
integral at the Lambert sequence value `a` bounds the left factorial `!n` within an
interval of length one.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Theorem 10 (`jis-2024-24.5.7-thm-10`).
-/

namespace MetaMathlibExt

open Set

@[expose] public section

end

private lemma lambertMul (n : ℕ) (hn : 5 ≤ n) (a : ℝ)
    (hW : lambertMap (-a / ((n : ℝ) - 1)) =
      -(1 / ((n : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1))) :
    a * Real.exp (-a / ((n : ℝ) - 1)) = (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1)) := by
  have hn5 : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hd : ((n : ℝ) - 1) ≠ 0 := ne_of_gt hpos
  have hW2 : ((-a / ((n : ℝ) - 1)) * Real.exp (-a / ((n : ℝ) - 1))) * (-((n : ℝ) - 1))
      = ((-(1 / ((n : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1)))) * (-((n : ℝ) - 1)) := by
    unfold lambertMap at hW
    rw [hW]
  have hL : ((-a / ((n : ℝ) - 1)) * Real.exp (-a / ((n : ℝ) - 1))) * (-((n : ℝ) - 1))
      = a * Real.exp (-a / ((n : ℝ) - 1)) := by
    field_simp
  have hR : ((-(1 / ((n : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1)))) * (-((n : ℝ) - 1))
      = (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1)) := by
    field_simp
  rw [hL, hR] at hW2
  exact hW2

private lemma cast_sub_one (n : ℕ) (hn1 : 1 ≤ n) :
    (((n - 1 : ℕ)) : ℝ) = (n : ℝ) - 1 := by
  rw [Nat.cast_sub hn1]
  norm_num

private lemma lambertPow (n : ℕ) (hn : 5 ≤ n) (a : ℝ)
    (hW : lambertMap (-a / ((n : ℝ) - 1)) =
      -(1 / ((n : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1))) :
    a ^ (n - 1) * Real.exp (-a) = 4 / 7 := by
  have hn1 : 1 ≤ n := by omega
  have hn5 : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hd : ((n : ℝ) - 1) ≠ 0 := ne_of_gt hpos
  have hdcast := cast_sub_one n hn1
  have hEq := lambertMul n hn a hW
  have hEqn := congrArg (fun x : ℝ => x ^ (n - 1)) hEq
  rw [mul_pow] at hEqn
  have hexp : (Real.exp (-a / ((n : ℝ) - 1))) ^ (n - 1) = Real.exp (-a) := by
    rw [← Real.exp_nat_mul]
    congr 1
    rw [hdcast]
    field_simp
  rw [hexp] at hEqn
  have hcrhs : (((4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1))) ^ (n - 1)) = 4 / 7 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    rw [show (1 / ((n : ℝ) - 1)) * (((n - 1 : ℕ)) : ℝ) = 1 by rw [hdcast]; field_simp]
    exact Real.rpow_one _
  rw [hcrhs] at hEqn
  exact hEqn

private lemma a_gt (n : ℕ) (hn : 5 ≤ n) (a : ℝ) (ha : (n : ℝ) - 1 ≤ a)
    (hW : lambertMap (-a / ((n : ℝ) - 1)) =
      -(1 / ((n : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1))) :
    (n : ℝ) - 1 < a := by
  have hn5 : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hd : ((n : ℝ) - 1) ≠ 0 := ne_of_gt hpos
  rcases eq_or_lt_of_le ha with hEq_a | hlt
  · exfalso
    have hc1 : (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1)) ≤ 1 :=
      Real.rpow_le_one (by norm_num) (by norm_num) (by positivity)
    have hEq := lambertMul n hn a hW
    rw [← hEq_a] at hEq
    rw [neg_div, div_self hd] at hEq
    have hepos : 0 < Real.exp (-1) := Real.exp_pos _
    have hd_le : (n : ℝ) - 1 ≤ 1 / Real.exp (-1) := by
      rw [le_div_iff₀ hepos]
      linarith [hEq, hc1]
    have hexp1 : 1 / Real.exp (-1) = Real.exp 1 := by
      rw [Real.exp_neg]
      simp
    rw [hexp1] at hd_le
    have hn4 : (4 : ℝ) ≤ (n : ℝ) - 1 := by linarith
    have hexp9 := Real.exp_one_lt_d9
    linarith
  · exact hlt

private lemma uexp_strictAnti :
    StrictAntiOn (fun u : ℝ => u * Real.exp (-u)) (Ioi 1) := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun u : ℝ => u * Real.exp (-u))
      (1 * Real.exp (-x) + x * (Real.exp (-x) * -1)) x := by
    intro x
    have h1 : HasDerivAt (fun t : ℝ => -t) (-1) x := (hasDerivAt_id x).neg
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-x) * -1) x :=
      (Real.hasDerivAt_exp (-x)).comp x h1
    exact (hasDerivAt_id x).mul h2
  apply strictAntiOn_of_deriv_neg (convex_Ioi _) _ _
  · exact (continuous_id.mul (Real.continuous_exp.comp continuous_neg)).continuousOn
  · intro x hx
    rw [IsOpen.interior_eq isOpen_Ioi] at hx
    have hx1 : (1 : ℝ) < x := hx
    have hde : deriv (fun u : ℝ => u * Real.exp (-u)) x
        = Real.exp (-x) * (1 - x) := by
      have e := (hderiv x).deriv
      have hrw : 1 * Real.exp (-x) + x * (Real.exp (-x) * -1)
          = Real.exp (-x) * (1 - x) := by ring
      rw [hrw] at e
      exact e
    rw [hde]
    exact mul_neg_of_pos_of_neg (Real.exp_pos _) (by linarith)

private lemma a_ge_of_exp_bound (n : ℕ) (hn : 5 ≤ n) (a : ℝ) (ha : (n : ℝ) - 1 ≤ a)
    (hW : lambertMap (-a / ((n : ℝ) - 1)) =
      -(1 / ((n : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1)))
    (L : ℝ) (hL1 : 1 < L / ((n : ℝ) - 1)) (E V : ℝ) (hV0 : 0 ≤ V)
    (hexp_le : Real.exp (L / ((n : ℝ) - 1)) ≤ E)
    (hc_le : (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1)) ≤ V)
    (hEV : V * E ≤ L) : L ≤ a := by
  have hn5 : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hd : ((n : ℝ) - 1) ≠ 0 := ne_of_gt hpos
  have ha_gt := a_gt n hn a ha hW
  have hEq := lambertMul n hn a hW
  by_contra hcon
  rw [not_le] at hcon
  have hu_mem : a / ((n : ℝ) - 1) ∈ Ioi (1 : ℝ) :=
    Set.mem_Ioi.mpr ((one_lt_div hpos).mpr ha_gt)
  have hU_mem : L / ((n : ℝ) - 1) ∈ Ioi (1 : ℝ) := hL1
  have hult : a / ((n : ℝ) - 1) < L / ((n : ℝ) - 1) := by gcongr
  have hanti : (L / ((n : ℝ) - 1)) * Real.exp (-(L / ((n : ℝ) - 1)))
      < (a / ((n : ℝ) - 1)) * Real.exp (-(a / ((n : ℝ) - 1))) :=
    uexp_strictAnti hu_mem hU_mem hult
  have hgu : (a / ((n : ℝ) - 1)) * Real.exp (-(a / ((n : ℝ) - 1)))
      = ((4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1))) / ((n : ℝ) - 1) := by
    have h1 : (a / ((n : ℝ) - 1)) * Real.exp (-(a / ((n : ℝ) - 1)))
        = (a * Real.exp (-a / ((n : ℝ) - 1))) / ((n : ℝ) - 1) := by
      rw [← neg_div, div_mul_eq_mul_div]
    rw [h1, hEq]
  rw [hgu] at hanti
  have hce : (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1)) * Real.exp (L / ((n : ℝ) - 1)) ≤ L :=
    (mul_le_mul hc_le hexp_le (Real.exp_pos _).le hV0).trans hEV
  have hkey : (L / ((n : ℝ) - 1)) * Real.exp (-(L / ((n : ℝ) - 1)))
      ≥ ((4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1))) / ((n : ℝ) - 1) := by
    have h2 : L * Real.exp (-(L / ((n : ℝ) - 1)))
        ≥ (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1)) := by
      have h4 : Real.exp (L / ((n : ℝ) - 1)) * Real.exp (-(L / ((n : ℝ) - 1))) = 1 := by
        rw [← Real.exp_add]
        simp
      have h5 := mul_le_mul_of_nonneg_right hce (Real.exp_pos (-(L / ((n : ℝ) - 1)))).le
      have hring : ((4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1)) * Real.exp (L / ((n : ℝ) - 1)))
          * Real.exp (-(L / ((n : ℝ) - 1)))
          = ((4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1)))
          * (Real.exp (L / ((n : ℝ) - 1)) * Real.exp (-(L / ((n : ℝ) - 1)))) := by
        ring
      rw [hring, h4, mul_one] at h5
      linarith [h5]
    have h6 : (L / ((n : ℝ) - 1)) * Real.exp (-(L / ((n : ℝ) - 1)))
        = (L * Real.exp (-(L / ((n : ℝ) - 1)))) / ((n : ℝ) - 1) := by
      rw [div_mul_eq_mul_div]
    rw [h6]
    gcongr
  linarith [hanti, hkey]

private lemma exp_rat_le (p : ℕ) (x : ℝ) (q : ℕ) (E : ℝ) (hE0 : 0 ≤ E)
    (hx : (q : ℝ) * x = (p : ℝ)) (hq : q ≠ 0) (hp : p ≠ 0)
    (hrat : (2.7182818286 : ℝ) ^ p ≤ E ^ q) : Real.exp x ≤ E := by
  have h1 : (Real.exp x) ^ q = Real.exp (p : ℝ) := by
    rw [← Real.exp_nat_mul, hx]
  have h2 : Real.exp (p : ℝ) = (Real.exp 1) ^ p := by
    rw [show (p : ℝ) = ((p : ℕ) : ℝ) * 1 by ring]
    exact Real.exp_nat_mul 1 p
  have hlt : (Real.exp x) ^ q < (2.7182818286 : ℝ) ^ p := by
    rw [h1, h2]
    exact pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le hp
  have hle : (Real.exp x) ^ q ≤ E ^ q := hlt.le.trans hrat
  exact le_of_pow_le_pow_left₀ hq hE0 hle

private lemma a_ge_three (n : ℕ) (hn : 8 ≤ n) (a : ℝ) (ha : (n : ℝ) - 1 ≤ a)
    (hW : lambertMap (-a / ((n : ℝ) - 1)) =
      -(1 / ((n : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1))) :
    3 * ((n : ℝ) - 1) ≤ a := by
  have hn5 : 5 ≤ n := by omega
  have hn8 : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hLd : (3 * ((n : ℝ) - 1)) / ((n : ℝ) - 1) = 3 := by field_simp
  have hL1 : 1 < (3 * ((n : ℝ) - 1)) / ((n : ℝ) - 1) := by rw [hLd]; norm_num
  have hexp_le : Real.exp ((3 * ((n : ℝ) - 1)) / ((n : ℝ) - 1)) ≤ 21 := by
    rw [hLd]
    exact exp_rat_le 3 3 1 21 (by norm_num) (by norm_num) (by decide) (by decide)
      (by norm_num)
  have hc_le : (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1)) ≤ 1 :=
    Real.rpow_le_one (by norm_num) (by norm_num) (by positivity)
  have hd7 : (7 : ℝ) ≤ (n : ℝ) - 1 := by linarith
  have hEV : (1 : ℝ) * 21 ≤ 3 * ((n : ℝ) - 1) := by linarith
  exact a_ge_of_exp_bound n hn5 a ha hW (3 * ((n : ℝ) - 1)) hL1 21 1 (by norm_num)
    hexp_le hc_le hEV

private lemma a_ge_five (a : ℝ) (ha : (((5 : ℕ)) : ℝ) - 1 ≤ a)
    (hW : lambertMap (-a / ((((5 : ℕ)) : ℝ) - 1)) =
      -(1 / ((((5 : ℕ)) : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((((5 : ℕ)) : ℝ) - 1))) :
    19 / 2 ≤ a := by
  have hd4 : ((((5 : ℕ)) : ℝ) - 1) = 4 := by norm_num
  have hL1 : 1 < (19 / 2 : ℝ) / ((((5 : ℕ)) : ℝ) - 1) := by rw [hd4]; norm_num
  have hexp_le : Real.exp ((19 / 2 : ℝ) / ((((5 : ℕ)) : ℝ) - 1)) ≤ 54 / 5 := by
    rw [hd4]
    have hx : (8 : ℝ) * ((19 / 2 : ℝ) / 4) = 19 := by norm_num
    exact exp_rat_le 19 ((19 / 2 : ℝ) / 4) 8 (54 / 5) (by norm_num) hx (by decide)
      (by decide) (by norm_num)
  have hc_le : (4 / 7 : ℝ) ^ (1 / ((((5 : ℕ)) : ℝ) - 1)) ≤ 1739 / 2000 := by
    rw [hd4]
    have hEq : (((4 / 7 : ℝ) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ)) = 4 / 7 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      rw [show ((1 : ℝ) / 4) * (((4 : ℕ)) : ℝ) = 1 by norm_num]
      exact Real.rpow_one _
    have hrat : (4 / 7 : ℝ) ≤ (1739 / 2000 : ℝ) ^ (4 : ℕ) := by norm_num
    have hle : (((4 / 7 : ℝ) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ)) ≤ ((1739 / 2000 : ℝ) ^ (4 : ℕ)) := by
      rw [hEq]
      exact hrat
    exact le_of_pow_le_pow_left₀ (by decide) (by norm_num) hle
  have hEV : (1739 / 2000 : ℝ) * (54 / 5 : ℝ) ≤ 19 / 2 := by norm_num
  have hV0 : (0 : ℝ) ≤ 1739 / 2000 := by norm_num
  exact a_ge_of_exp_bound 5 (by norm_num) a ha hW (19 / 2) hL1 (54 / 5) (1739 / 2000)
    hV0 hexp_le hc_le hEV

private lemma a_ge_six (a : ℝ) (ha : (((6 : ℕ)) : ℝ) - 1 ≤ a)
    (hW : lambertMap (-a / ((((6 : ℕ)) : ℝ) - 1)) =
      -(1 / ((((6 : ℕ)) : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((((6 : ℕ)) : ℝ) - 1))) :
    12 ≤ a := by
  have hd5 : ((((6 : ℕ)) : ℝ) - 1) = 5 := by norm_num
  have hL1 : 1 < (12 : ℝ) / ((((6 : ℕ)) : ℝ) - 1) := by rw [hd5]; norm_num
  have hexp_le : Real.exp ((12 : ℝ) / ((((6 : ℕ)) : ℝ) - 1)) ≤ 111 / 10 := by
    rw [hd5]
    have hx : (5 : ℝ) * ((12 : ℝ) / 5) = 12 := by norm_num
    exact exp_rat_le 12 ((12 : ℝ) / 5) 5 (111 / 10) (by norm_num) hx (by decide)
      (by decide) (by norm_num)
  have hc_le : (4 / 7 : ℝ) ^ (1 / ((((6 : ℕ)) : ℝ) - 1)) ≤ 9 / 10 := by
    rw [hd5]
    have hEq : (((4 / 7 : ℝ) ^ ((1 : ℝ) / 5)) ^ (5 : ℕ)) = 4 / 7 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      rw [show ((1 : ℝ) / 5) * (((5 : ℕ)) : ℝ) = 1 by norm_num]
      exact Real.rpow_one _
    have hrat : (4 / 7 : ℝ) ≤ (9 / 10 : ℝ) ^ (5 : ℕ) := by norm_num
    have hle : (((4 / 7 : ℝ) ^ ((1 : ℝ) / 5)) ^ (5 : ℕ)) ≤ ((9 / 10 : ℝ) ^ (5 : ℕ)) := by
      rw [hEq]
      exact hrat
    exact le_of_pow_le_pow_left₀ (by decide) (by norm_num) hle
  have hEV : (9 / 10 : ℝ) * (111 / 10 : ℝ) ≤ 12 := by norm_num
  have hV0 : (0 : ℝ) ≤ 9 / 10 := by norm_num
  exact a_ge_of_exp_bound 6 (by norm_num) a ha hW 12 hL1 (111 / 10) (9 / 10)
    hV0 hexp_le hc_le hEV

private lemma a_ge_seven (a : ℝ) (ha : (((7 : ℕ)) : ℝ) - 1 ≤ a)
    (hW : lambertMap (-a / ((((7 : ℕ)) : ℝ) - 1)) =
      -(1 / ((((7 : ℕ)) : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((((7 : ℕ)) : ℝ) - 1))) :
    29 / 2 ≤ a := by
  have hd6 : ((((7 : ℕ)) : ℝ) - 1) = 6 := by norm_num
  have hL1 : 1 < (29 / 2 : ℝ) / ((((7 : ℕ)) : ℝ) - 1) := by rw [hd6]; norm_num
  have hexp_le : Real.exp ((29 / 2 : ℝ) / ((((7 : ℕ)) : ℝ) - 1)) ≤ 113 / 10 := by
    rw [hd6]
    have hx : (12 : ℝ) * ((29 / 2 : ℝ) / 6) = 29 := by norm_num
    exact exp_rat_le 29 ((29 / 2 : ℝ) / 6) 12 (113 / 10) (by norm_num) hx (by decide)
      (by decide) (by norm_num)
  have hc_le : (4 / 7 : ℝ) ^ (1 / ((((7 : ℕ)) : ℝ) - 1)) ≤ 92 / 100 := by
    rw [hd6]
    have hEq : (((4 / 7 : ℝ) ^ ((1 : ℝ) / 6)) ^ (6 : ℕ)) = 4 / 7 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      rw [show ((1 : ℝ) / 6) * (((6 : ℕ)) : ℝ) = 1 by norm_num]
      exact Real.rpow_one _
    have hrat : (4 / 7 : ℝ) ≤ (92 / 100 : ℝ) ^ (6 : ℕ) := by norm_num
    have hle : (((4 / 7 : ℝ) ^ ((1 : ℝ) / 6)) ^ (6 : ℕ)) ≤ ((92 / 100 : ℝ) ^ (6 : ℕ)) := by
      rw [hEq]
      exact hrat
    exact le_of_pow_le_pow_left₀ (by decide) (by norm_num) hle
  have hEV : (92 / 100 : ℝ) * (113 / 10 : ℝ) ≤ 29 / 2 := by norm_num
  have hV0 : (0 : ℝ) ≤ 92 / 100 := by norm_num
  exact a_ge_of_exp_bound 7 (by norm_num) a ha hW (29 / 2) hL1 (113 / 10) (92 / 100)
    hV0 hexp_le hc_le hEV

private lemma Spow_le (k n : ℕ) (hkn : k + 1 ≤ n) (a : ℝ) (ha0 : 0 ≤ a) :
    (∑ j ∈ Finset.range (k + 1), a ^ j / (j.factorial : ℝ))
      ≤ (∑ j ∈ Finset.range n, a ^ j / (j.factorial : ℝ)) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg _ _
  · rw [Finset.range_subset]
    intro x hx
    exact Finset.mem_range.mpr (by omega)
  · intro j _ _
    exact div_nonneg (pow_nonneg ha0 _) (Nat.cast_nonneg _)

private lemma R_le_mul (n : ℕ) (a : ℝ) (ha0 : 0 ≤ a) :
    (∑ k ∈ Finset.range n, (k.factorial : ℝ)) - kurepaPartialIntegral n a
      ≤ Real.exp (-a) * (∑ j ∈ Finset.range n, a ^ j / (j.factorial : ℝ))
        * (∑ k ∈ Finset.range n, (k.factorial : ℝ)) := by
  rw [sum_factorial_sub_kurepaPartialIntegral n a]
  have h1 : (∑ k ∈ Finset.range n,
        (k.factorial : ℝ) * (∑ j ∈ Finset.range (k + 1), a ^ j / (j.factorial : ℝ)))
      ≤ (∑ k ∈ Finset.range n, (k.factorial : ℝ))
        * (∑ j ∈ Finset.range n, a ^ j / (j.factorial : ℝ)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k hk
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Spow_le k n _ a ha0
    exact Nat.succ_le_of_lt (Finset.mem_range.mp hk)
  have h2 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-a)).le
  have h3 : Real.exp (-a)
        * ((∑ k ∈ Finset.range n, (k.factorial : ℝ))
          * (∑ j ∈ Finset.range n, a ^ j / (j.factorial : ℝ)))
      = Real.exp (-a) * (∑ j ∈ Finset.range n, a ^ j / (j.factorial : ℝ))
        * (∑ k ∈ Finset.range n, (k.factorial : ℝ)) := by ring
  rw [h3] at h2
  exact h2

private lemma term_le (n j : ℕ) (hn1 : 1 ≤ n) (hj : j ≤ n - 1) (a : ℝ) (ha0 : 0 < a) :
    ((((n - 1).factorial : ℕ) : ℝ) / ((j.factorial : ℕ) : ℝ)) / a ^ (n - 1 - j)
      ≤ (((n : ℝ) - 1) / a) ^ (n - 1 - j) := by
  have hdiv : j.factorial ∣ (n - 1).factorial := Nat.factorial_dvd_factorial hj
  have hdesc := Nat.descFactorial_le_pow (n - 1) (n - 1 - j)
  rw [Nat.descFactorial_eq_div (by omega : n - 1 - j ≤ n - 1)] at hdesc
  rw [show (n - 1) - (n - 1 - j) = j by omega] at hdesc
  have hcast : ((((n - 1).factorial / j.factorial : ℕ)) : ℝ)
      ≤ ((((n - 1) ^ (n - 1 - j) : ℕ)) : ℝ) := by
    exact_mod_cast hdesc
  have hj0 : (((j.factorial : ℕ)) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero j
  rw [Nat.cast_div hdiv hj0] at hcast
  rw [Nat.cast_pow] at hcast
  have hdcast : ((((n - 1 : ℕ))) : ℝ) = (n : ℝ) - 1 := cast_sub_one n hn1
  rw [hdcast] at hcast
  have hpos : (0 : ℝ) < a ^ (n - 1 - j) := pow_pos ha0 _
  have hle : ((((n - 1).factorial : ℕ) : ℝ) / ((j.factorial : ℕ) : ℝ))
      / a ^ (n - 1 - j)
      ≤ (((n : ℝ) - 1) ^ (n - 1 - j)) / a ^ (n - 1 - j) := by
    rw [le_div_iff₀ hpos, div_mul_cancel₀ _ hpos.ne']
    exact hcast
  rw [← div_pow] at hle
  exact hle

private lemma U_le (n : ℕ) (hn : 8 ≤ n) (a : ℝ) (ha0 : 0 < a)
    (hlt : (n : ℝ) - 1 < a) :
    (∑ j ∈ Finset.range n,
        ((((n - 1).factorial : ℕ) : ℝ) / ((j.factorial : ℕ) : ℝ)) / a ^ (n - 1 - j))
      ≤ a / (a - ((n : ℝ) - 1)) := by
  have hn1 : 1 ≤ n := by omega
  have hn8 : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hρ0 : (0 : ℝ) ≤ ((n : ℝ) - 1) / a := by
    apply div_nonneg _ ha0.le
    linarith
  have hρ1 : ((n : ℝ) - 1) / a < 1 := by
    rw [div_lt_one ha0]
    linarith [hlt]
  calc (∑ j ∈ Finset.range n,
          ((((n - 1).factorial : ℕ) : ℝ) / ((j.factorial : ℕ) : ℝ)) / a ^ (n - 1 - j))
        ≤ ∑ j ∈ Finset.range n, (((n : ℝ) - 1) / a) ^ (n - 1 - j) := by
          apply Finset.sum_le_sum
          intro j hj
          have hj1 : j ≤ n - 1 := by
            have hjn := Finset.mem_range.mp hj
            omega
          exact term_le n j hn1 hj1 a ha0
      _ = ∑ i ∈ Finset.range n, (((n : ℝ) - 1) / a) ^ i :=
          Finset.sum_range_reflect (fun i => (((n : ℝ) - 1) / a) ^ i) n
      _ ≤ 1 / (1 - ((n : ℝ) - 1) / a) := by
        simpa using geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hρ0 hρ1
      _ = a / (a - ((n : ℝ) - 1)) := by
          have ha1 : a - ((n : ℝ) - 1) ≠ 0 := ne_of_gt (by linarith [hlt])
          have ha0' : a ≠ 0 := ne_of_gt ha0
          field_simp

private lemma SF_eq (n : ℕ) (hn1 : 1 ≤ n) (a : ℝ) (ha0 : 0 < a) :
    (∑ j ∈ Finset.range n, a ^ j / ((j.factorial : ℕ) : ℝ))
        * ((((n - 1).factorial : ℕ)) : ℝ) / a ^ (n - 1)
      = ∑ j ∈ Finset.range n,
        ((((n - 1).factorial : ℕ) : ℝ) / ((j.factorial : ℕ) : ℝ)) / a ^ (n - 1 - j) := by
  rw [Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < n := Finset.mem_range.mp hj
  have hj1 : j ≤ n - 1 := by omega
  have haj : a ^ j ≠ 0 := pow_ne_zero _ ha0.ne'
  have ham : a ^ (n - 1 - j) ≠ 0 := pow_ne_zero _ ha0.ne'
  have hjf : (((j.factorial : ℕ)) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero j
  have hexp_pow : a ^ (n - 1) = a ^ j * a ^ (n - 1 - j) := by
    rw [← pow_add]
    congr 1
    exact (Nat.add_sub_cancel' hj1).symm
  rw [hexp_pow]
  field_simp

private lemma hTF (n : ℕ) (hn : 9 ≤ n) :
    (∑ k ∈ Finset.range n, ((k.factorial : ℕ) : ℝ)) / ((((n - 1).factorial : ℕ)) : ℝ)
      ≤ 1 + 1 / ((n : ℝ) - 1) + 2 / (((n : ℝ) - 1) * ((n : ℝ) - 2)) := by
  have hn1 : 1 ≤ n := by omega
  have hn9 : (9 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have d1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have d2 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  have d3 : (0 : ℝ) < (n : ℝ) - 3 := by linarith
  have g1 : ((n - 1).factorial : ℕ) = (n - 1) * (n - 2).factorial := by
    have e1 : (n - 2) + 1 = n - 1 := by omega
    rw [← e1, Nat.factorial_succ]
  have g2 : ((n - 2).factorial : ℕ) = (n - 2) * (n - 3).factorial := by
    have e2 : (n - 3) + 1 = n - 2 := by omega
    rw [← e2, Nat.factorial_succ]
  have g3 : ((n - 3).factorial : ℕ) = (n - 3) * (n - 4).factorial := by
    have e3 : (n - 4) + 1 = n - 3 := by omega
    rw [← e3, Nat.factorial_succ]
  have c1 : ((((n - 1 : ℕ))) : ℝ) = (n : ℝ) - 1 := cast_sub_one n hn1
  have c2 : ((((n - 2 : ℕ))) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (show 2 ≤ n by omega)]
    norm_num
  have c3 : ((((n - 3 : ℕ))) : ℝ) = (n : ℝ) - 3 := by
    rw [Nat.cast_sub (show 3 ≤ n by omega)]
    norm_num
  have hF : ((((n - 1).factorial : ℕ)) : ℝ)
      = ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3)
        * ((((n - 4).factorial : ℕ)) : ℝ) := by
    have h1 : ((n - 1).factorial : ℕ)
        = (n - 1) * (n - 2) * (n - 3) * (n - 4).factorial := by
      rw [g1, g2, g3]
      ring
    have h2 : ((((n - 1).factorial : ℕ)) : ℝ)
        = ((((n - 1 : ℕ))) : ℝ) * ((((n - 2 : ℕ))) : ℝ) * ((((n - 3 : ℕ))) : ℝ)
          * ((((n - 4).factorial : ℕ)) : ℝ) := by
      exact_mod_cast h1
    rw [h2, c1, c2, c3]
  have hFpos : (0 : ℝ) < ((((n - 1).factorial : ℕ)) : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hFne : ((((n - 1).factorial : ℕ)) : ℝ) ≠ 0 := ne_of_gt hFpos
  have p1 : (∑ k ∈ Finset.range n, ((k.factorial : ℕ) : ℝ))
      = (∑ k ∈ Finset.range (n - 1), ((k.factorial : ℕ) : ℝ))
        + ((((n - 1).factorial : ℕ)) : ℝ) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [Finset.sum_range_succ]
  have p2 : (∑ k ∈ Finset.range (n - 1), ((k.factorial : ℕ) : ℝ))
      = (∑ k ∈ Finset.range (n - 2), ((k.factorial : ℕ) : ℝ))
        + ((((n - 2).factorial : ℕ)) : ℝ) := by
    conv_lhs => rw [show n - 1 = (n - 2) + 1 by omega]
    rw [Finset.sum_range_succ]
  have p3 : (∑ k ∈ Finset.range (n - 2), ((k.factorial : ℕ) : ℝ))
      = (∑ k ∈ Finset.range (n - 3), ((k.factorial : ℕ) : ℝ))
        + ((((n - 3).factorial : ℕ)) : ℝ) := by
    conv_lhs => rw [show n - 2 = (n - 3) + 1 by omega]
    rw [Finset.sum_range_succ]
  have hsplit : (∑ k ∈ Finset.range n, ((k.factorial : ℕ) : ℝ))
      = (∑ k ∈ Finset.range (n - 3), ((k.factorial : ℕ) : ℝ))
        + ((((n - 3).factorial : ℕ)) : ℝ) + ((((n - 2).factorial : ℕ)) : ℝ)
        + ((((n - 1).factorial : ℕ)) : ℝ) := by
    rw [p1, p2, p3]
  have hC : ((((n - 1).factorial : ℕ)) : ℝ) / ((((n - 1).factorial : ℕ)) : ℝ) = 1 :=
    div_self hFne
  have hB : ((((n - 2).factorial : ℕ)) : ℝ) / ((((n - 1).factorial : ℕ)) : ℝ)
      = 1 / ((n : ℝ) - 1) := by
    have hBg1 : ((((n - 1).factorial : ℕ)) : ℝ)
        = ((n : ℝ) - 1) * ((((n - 2).factorial : ℕ)) : ℝ) := by
      have h := congrArg (Nat.cast : ℕ → ℝ) g1
      push_cast at h
      rw [c1] at h
      exact h
    have hBne : ((((n - 2).factorial : ℕ)) : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr (Nat.factorial_pos _))
    rw [hBg1]
    field_simp
  have hA : ((((n - 3).factorial : ℕ)) : ℝ) / ((((n - 1).factorial : ℕ)) : ℝ)
      = 1 / (((n : ℝ) - 1) * ((n : ℝ) - 2)) := by
    have hAg : ((((n - 1).factorial : ℕ)) : ℝ)
        = ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((((n - 3).factorial : ℕ)) : ℝ) := by
      have h12 : ((n - 1).factorial : ℕ) = (n - 1) * (n - 2) * (n - 3).factorial := by
        rw [g1, g2]
        ring
      have h := congrArg (Nat.cast : ℕ → ℝ) h12
      push_cast at h
      rw [c1, c2] at h
      exact h
    have hAne : ((((n - 3).factorial : ℕ)) : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr (Nat.factorial_pos _))
    rw [hAg]
    field_simp
  have hT3 : (∑ k ∈ Finset.range (n - 3), ((k.factorial : ℕ) : ℝ))
        / ((((n - 1).factorial : ℕ)) : ℝ)
      ≤ 1 / (((n : ℝ) - 1) * ((n : ℝ) - 2)) := by
    have hDpos : (0 : ℝ) < ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3) :=
      mul_pos (mul_pos d1 d2) d3
    have hper : ∀ k ∈ Finset.range (n - 3),
        ((k.factorial : ℕ) : ℝ) / ((((n - 1).factorial : ℕ)) : ℝ)
          ≤ 1 / (((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3)) := by
      intro k hk
      have hk4 : k ≤ n - 4 := by
        have hkn := Finset.mem_range.mp hk
        omega
      have hkle : ((k.factorial : ℕ) : ℝ) ≤ ((((n - 4).factorial : ℕ)) : ℝ) := by
        exact_mod_cast Nat.factorial_le hk4
      rw [div_le_div_iff₀ hFpos hDpos]
      rw [hF]
      have hmul := mul_le_mul_of_nonneg_right hkle hDpos.le
      linarith [hmul]
    have hsum := Finset.sum_le_sum (fun k hk => hper k hk)
    rw [← Finset.sum_div] at hsum
    have hconst : (∑ k ∈ Finset.range (n - 3),
          1 / (((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3)))
        = ((((n - 3 : ℕ))) : ℝ)
          * (1 / (((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3))) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hconst] at hsum
    have hfin : ((((n - 3 : ℕ))) : ℝ)
          * (1 / (((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3)))
        = 1 / (((n : ℝ) - 1) * ((n : ℝ) - 2)) := by
      rw [c3]
      field_simp
    rw [hfin] at hsum
    exact hsum
  rw [hsplit, add_div, add_div, add_div, hC, hB, hA]
  have h2 : 2 / (((n : ℝ) - 1) * ((n : ℝ) - 2))
      = 2 * (1 / (((n : ℝ) - 1) * ((n : ℝ) - 2))) := by ring
  rw [h2]
  linarith [hT3]

private lemma hFinal9 (n : ℕ) (hn : 9 ≤ n) (a : ℝ) (ha : (n : ℝ) - 1 ≤ a)
    (hW : lambertMap (-a / ((n : ℝ) - 1)) =
      -(1 / ((n : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1))) :
    (∑ k ∈ Finset.range n, (k.factorial : ℝ)) - kurepaPartialIntegral n a < 1 := by
  have hn5 : 5 ≤ n := by omega
  have hn8 : 8 ≤ n := by omega
  have hn9 : (9 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ha0 : (0 : ℝ) ≤ a := by linarith [ha, hn9]
  have ha0' : (0 : ℝ) < a := by linarith [ha, hn9]
  have ha_gt := a_gt n hn5 a ha hW
  have hPow := lambertPow n hn5 a hW
  have ha3 := a_ge_three n hn8 a ha hW
  have hR0 := R_le_mul n a ha0
  have hP0 : a ^ (n - 1) ≠ 0 := pow_ne_zero _ ha0'.ne'
  have hFpos : (0 : ℝ) < ((((n - 1).factorial : ℕ)) : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hE0 : Real.exp (-a) = (4 / 7 : ℝ) / a ^ (n - 1) := by
    rw [eq_div_iff hP0]
    linear_combination hPow
  have hEq : Real.exp (-a) * (∑ j ∈ Finset.range n, a ^ j / (j.factorial : ℝ))
          * (∑ k ∈ Finset.range n, (k.factorial : ℝ))
        = (4 / 7 : ℝ) * (((∑ k ∈ Finset.range n, (k.factorial : ℝ))
            / ((((n - 1).factorial : ℕ)) : ℝ))
            * (((∑ j ∈ Finset.range n, a ^ j / (j.factorial : ℝ)))
              * ((((n - 1).factorial : ℕ)) : ℝ) / a ^ (n - 1))) := by
    rw [hE0]
    field_simp
  have hTFb := hTF n hn
  have hU := U_le n hn8 a ha0' ha_gt
  have hSFe := SF_eq n (by omega) a ha0'
  have h32 : a / (a - ((n : ℝ) - 1)) ≤ 3 / 2 := by
    have h1 : (0 : ℝ) < a - ((n : ℝ) - 1) := by linarith [ha_gt]
    rw [div_le_iff₀ h1]
    linarith [ha3]
  have hSP : (∑ j ∈ Finset.range n, a ^ j / (j.factorial : ℝ))
        * ((((n - 1).factorial : ℕ)) : ℝ) / a ^ (n - 1) ≤ 3 / 2 := by
    rw [hSFe]
    exact hU.trans h32
  have hTFnn : (0 : ℝ)
      ≤ (∑ k ∈ Finset.range n, (k.factorial : ℝ)) / ((((n - 1).factorial : ℕ)) : ℝ) :=
    div_nonneg (Finset.sum_nonneg (fun k _ => Nat.cast_nonneg _)) hFpos.le
  have hSPnn : (0 : ℝ)
      ≤ (∑ j ∈ Finset.range n, a ^ j / (j.factorial : ℝ))
        * ((((n - 1).factorial : ℕ)) : ℝ) / a ^ (n - 1) := by
    apply div_nonneg _ (pow_nonneg ha0 _)
    apply mul_nonneg _ hFpos.le
    apply Finset.sum_nonneg
    intro j _
    exact div_nonneg (pow_nonneg ha0 _) (Nat.cast_nonneg _)
  have d1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have d2 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  have hB1nn : (0 : ℝ)
      ≤ 1 + 1 / ((n : ℝ) - 1) + 2 / (((n : ℝ) - 1) * ((n : ℝ) - 2)) := by
    positivity
  have hmul := mul_le_mul hTFb hSP hSPnn hB1nn
  have hmul2 := mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 4 / 7)
  have hfin : (4 / 7 : ℝ)
        * ((1 + 1 / ((n : ℝ) - 1) + 2 / (((n : ℝ) - 1) * ((n : ℝ) - 2))) * (3 / 2))
        < 1 := by
    have hDpos : (0 : ℝ) < ((n : ℝ) - 1) * ((n : ℝ) - 2) := mul_pos d1 d2
    have hB1eq : (1 : ℝ) + 1 / ((n : ℝ) - 1) + 2 / (((n : ℝ) - 1) * ((n : ℝ) - 2))
        = 1 + (n : ℝ) / (((n : ℝ) - 1) * ((n : ℝ) - 2)) := by
      field_simp
      ring
    rw [hB1eq]
    have hkey : (n : ℝ) / (((n : ℝ) - 1) * ((n : ℝ) - 2)) < 1 / 6 := by
      rw [lt_div_iff₀ (by norm_num), div_mul_eq_mul_div, div_lt_iff₀ hDpos]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ (n : ℝ) by linarith)
        (show (0 : ℝ) ≤ (n : ℝ) - 9 by linarith)]
    have hrw : (4 / 7 : ℝ) * ((1 + (n : ℝ) / (((n : ℝ) - 1) * ((n : ℝ) - 2))) * (3 / 2))
        = 6 * (1 + (n : ℝ) / (((n : ℝ) - 1) * ((n : ℝ) - 2))) / 7 := by ring
    rw [hrw, div_lt_iff₀ (by norm_num)]
    linarith [hkey]
  have hR1 := hR0.trans_eq hEq
  exact (hR1.trans hmul2).trans_lt hfin

private lemma hFinal5 (a : ℝ) (ha : ((((5 : ℕ))) : ℝ) - 1 ≤ a)
    (hW : lambertMap (-a / ((((5 : ℕ)) : ℝ) - 1)) =
      -(1 / ((((5 : ℕ)) : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((((5 : ℕ)) : ℝ) - 1))) :
    (∑ k ∈ Finset.range 5, ((k.factorial : ℕ) : ℝ)) - kurepaPartialIntegral 5 a < 1 := by
  have haL : (19 / 2 : ℝ) ≤ a := a_ge_five a ha hW
  have ha0' : (0 : ℝ) < a := by linarith [haL]
  have hL0 : (0 : ℝ) < 19 / 2 := by norm_num
  have hPow := lambertPow 5 (by norm_num) a hW
  have hPow4 : a ^ 4 * Real.exp (-a) = 4 / 7 := hPow
  have hR := sum_factorial_sub_kurepaPartialIntegral 5 a
  have hpoly : (∑ k ∈ Finset.range 5,
        ((k.factorial : ℕ) : ℝ)
          * (∑ j ∈ Finset.range (k + 1), a ^ j / (((j.factorial : ℕ)) : ℝ)))
      = 34 + 33 * a + 16 * a ^ 2 + 5 * a ^ 3 + a ^ 4 := by
    simp [Finset.sum_range_succ,
      show ((0 : ℕ).factorial) = 1 from rfl, show ((1 : ℕ).factorial) = 1 from rfl,
      show ((2 : ℕ).factorial) = 2 from rfl, show ((3 : ℕ).factorial) = 6 from rfl,
      show ((4 : ℕ).factorial) = 24 from rfl]
    ring
  rw [hpoly] at hR
  have hP0 : a ^ 4 ≠ 0 := pow_ne_zero _ ha0'.ne'
  have hE0 : Real.exp (-a) = (4 / 7 : ℝ) / a ^ 4 := by
    rw [eq_div_iff hP0]
    linear_combination hPow4
  have ha1 : a ≠ 0 := ha0'.ne'
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero _ ha0'.ne'
  have ha3 : a ^ 3 ≠ 0 := pow_ne_zero _ ha0'.ne'
  have hsplit : (34 + 33 * a + 16 * a ^ 2 + 5 * a ^ 3 + a ^ 4) / a ^ 4
      = 34 / a ^ 4 + 33 / a ^ 3 + 16 / a ^ 2 + 5 / a + 1 := by
    field_simp
  have hle : (34 + 33 * a + 16 * a ^ 2 + 5 * a ^ 3 + a ^ 4) / a ^ 4
      ≤ 34 / (19 / 2) ^ 4 + 33 / (19 / 2) ^ 3 + 16 / (19 / 2) ^ 2 + 5 / (19 / 2) + 1 := by
    rw [hsplit]
    gcongr
  have hfin : (4 / 7 : ℝ)
        * (34 / (19 / 2) ^ 4 + 33 / (19 / 2) ^ 3 + 16 / (19 / 2) ^ 2 + 5 / (19 / 2) + 1)
        < 1 := by
    norm_num
  have hR2 : (∑ k ∈ Finset.range 5, ((k.factorial : ℕ) : ℝ))
        - kurepaPartialIntegral 5 a
      = (4 / 7 : ℝ) * ((34 + 33 * a + 16 * a ^ 2 + 5 * a ^ 3 + a ^ 4) / a ^ 4) := by
    rw [hR, hE0]
    ring
  rw [hR2]
  have hmul := mul_le_mul_of_nonneg_left hle (by norm_num : (0 : ℝ) ≤ 4 / 7)
  exact hmul.trans_lt hfin

private lemma hFinal6 (a : ℝ) (ha : ((((6 : ℕ))) : ℝ) - 1 ≤ a)
    (hW : lambertMap (-a / ((((6 : ℕ)) : ℝ) - 1)) =
      -(1 / ((((6 : ℕ)) : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((((6 : ℕ)) : ℝ) - 1))) :
    (∑ k ∈ Finset.range 6, ((k.factorial : ℕ) : ℝ)) - kurepaPartialIntegral 6 a < 1 := by
  have haL : (12 : ℝ) ≤ a := a_ge_six a ha hW
  have ha0' : (0 : ℝ) < a := by linarith [haL]
  have hL0 : (0 : ℝ) < 12 := by norm_num
  have hPow := lambertPow 6 (by norm_num) a hW
  have hPow5 : a ^ 5 * Real.exp (-a) = 4 / 7 := hPow
  have hR := sum_factorial_sub_kurepaPartialIntegral 6 a
  have hpoly : (∑ k ∈ Finset.range 6,
        ((k.factorial : ℕ) : ℝ)
          * (∑ j ∈ Finset.range (k + 1), a ^ j / (((j.factorial : ℕ)) : ℝ)))
      = 154 + 153 * a + 76 * a ^ 2 + 25 * a ^ 3 + 6 * a ^ 4 + a ^ 5 := by
    simp [Finset.sum_range_succ,
      show ((0 : ℕ).factorial) = 1 from rfl, show ((1 : ℕ).factorial) = 1 from rfl,
      show ((2 : ℕ).factorial) = 2 from rfl, show ((3 : ℕ).factorial) = 6 from rfl,
      show ((4 : ℕ).factorial) = 24 from rfl, show ((5 : ℕ).factorial) = 120 from rfl]
    ring
  rw [hpoly] at hR
  have hP0 : a ^ 5 ≠ 0 := pow_ne_zero _ ha0'.ne'
  have hE0 : Real.exp (-a) = (4 / 7 : ℝ) / a ^ 5 := by
    rw [eq_div_iff hP0]
    linear_combination hPow5
  have ha1 : a ≠ 0 := ha0'.ne'
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero _ ha0'.ne'
  have ha3 : a ^ 3 ≠ 0 := pow_ne_zero _ ha0'.ne'
  have ha4 : a ^ 4 ≠ 0 := pow_ne_zero _ ha0'.ne'
  have hsplit : (154 + 153 * a + 76 * a ^ 2 + 25 * a ^ 3 + 6 * a ^ 4 + a ^ 5) / a ^ 5
      = 154 / a ^ 5 + 153 / a ^ 4 + 76 / a ^ 3 + 25 / a ^ 2 + 6 / a + 1 := by
    field_simp
  have hle : (154 + 153 * a + 76 * a ^ 2 + 25 * a ^ 3 + 6 * a ^ 4 + a ^ 5) / a ^ 5
      ≤ 154 / (12 : ℝ) ^ 5 + 153 / (12 : ℝ) ^ 4 + 76 / (12 : ℝ) ^ 3 + 25 / (12 : ℝ) ^ 2
        + 6 / (12 : ℝ) + 1 := by
    rw [hsplit]
    gcongr
  have hfin : (4 / 7 : ℝ)
        * (154 / (12 : ℝ) ^ 5 + 153 / (12 : ℝ) ^ 4 + 76 / (12 : ℝ) ^ 3
          + 25 / (12 : ℝ) ^ 2 + 6 / (12 : ℝ) + 1) < 1 := by
    norm_num
  have hR2 : (∑ k ∈ Finset.range 6, ((k.factorial : ℕ) : ℝ))
        - kurepaPartialIntegral 6 a
      = (4 / 7 : ℝ)
        * ((154 + 153 * a + 76 * a ^ 2 + 25 * a ^ 3 + 6 * a ^ 4 + a ^ 5) / a ^ 5) := by
    rw [hR, hE0]
    ring
  rw [hR2]
  have hmul := mul_le_mul_of_nonneg_left hle (by norm_num : (0 : ℝ) ≤ 4 / 7)
  exact hmul.trans_lt hfin

private lemma hFinal7 (a : ℝ) (ha : ((((7 : ℕ))) : ℝ) - 1 ≤ a)
    (hW : lambertMap (-a / ((((7 : ℕ)) : ℝ) - 1)) =
      -(1 / ((((7 : ℕ)) : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((((7 : ℕ)) : ℝ) - 1))) :
    (∑ k ∈ Finset.range 7, ((k.factorial : ℕ) : ℝ)) - kurepaPartialIntegral 7 a < 1 := by
  have haL : (29 / 2 : ℝ) ≤ a := a_ge_seven a ha hW
  have ha0' : (0 : ℝ) < a := by linarith [haL]
  have hL0 : (0 : ℝ) < 29 / 2 := by norm_num
  have hPow := lambertPow 7 (by norm_num) a hW
  have hPow6 : a ^ 6 * Real.exp (-a) = 4 / 7 := hPow
  have hR := sum_factorial_sub_kurepaPartialIntegral 7 a
  have hpoly : (∑ k ∈ Finset.range 7,
        ((k.factorial : ℕ) : ℝ)
          * (∑ j ∈ Finset.range (k + 1), a ^ j / (((j.factorial : ℕ)) : ℝ)))
      = 874 + 873 * a + 436 * a ^ 2 + 145 * a ^ 3 + 36 * a ^ 4 + 7 * a ^ 5
        + a ^ 6 := by
    simp [Finset.sum_range_succ,
      show ((0 : ℕ).factorial) = 1 from rfl, show ((1 : ℕ).factorial) = 1 from rfl,
      show ((2 : ℕ).factorial) = 2 from rfl, show ((3 : ℕ).factorial) = 6 from rfl,
      show ((4 : ℕ).factorial) = 24 from rfl, show ((5 : ℕ).factorial) = 120 from rfl,
      show ((6 : ℕ).factorial) = 720 from rfl]
    ring
  rw [hpoly] at hR
  have hP0 : a ^ 6 ≠ 0 := pow_ne_zero _ ha0'.ne'
  have hE0 : Real.exp (-a) = (4 / 7 : ℝ) / a ^ 6 := by
    rw [eq_div_iff hP0]
    linear_combination hPow6
  have ha1 : a ≠ 0 := ha0'.ne'
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero _ ha0'.ne'
  have ha3 : a ^ 3 ≠ 0 := pow_ne_zero _ ha0'.ne'
  have ha4 : a ^ 4 ≠ 0 := pow_ne_zero _ ha0'.ne'
  have ha5 : a ^ 5 ≠ 0 := pow_ne_zero _ ha0'.ne'
  have hsplit : (874 + 873 * a + 436 * a ^ 2 + 145 * a ^ 3 + 36 * a ^ 4 + 7 * a ^ 5
        + a ^ 6) / a ^ 6
      = 874 / a ^ 6 + 873 / a ^ 5 + 436 / a ^ 4 + 145 / a ^ 3 + 36 / a ^ 2 + 7 / a
        + 1 := by
    field_simp
  have hle : (874 + 873 * a + 436 * a ^ 2 + 145 * a ^ 3 + 36 * a ^ 4 + 7 * a ^ 5
        + a ^ 6) / a ^ 6
      ≤ 874 / (29 / 2) ^ 6 + 873 / (29 / 2) ^ 5 + 436 / (29 / 2) ^ 4
        + 145 / (29 / 2) ^ 3 + 36 / (29 / 2) ^ 2 + 7 / (29 / 2) + 1 := by
    rw [hsplit]
    gcongr
  have hfin : (4 / 7 : ℝ)
        * (874 / (29 / 2) ^ 6 + 873 / (29 / 2) ^ 5 + 436 / (29 / 2) ^ 4
          + 145 / (29 / 2) ^ 3 + 36 / (29 / 2) ^ 2 + 7 / (29 / 2) + 1) < 1 := by
    norm_num
  have hR2 : (∑ k ∈ Finset.range 7, ((k.factorial : ℕ) : ℝ))
        - kurepaPartialIntegral 7 a
      = (4 / 7 : ℝ)
        * ((874 + 873 * a + 436 * a ^ 2 + 145 * a ^ 3 + 36 * a ^ 4 + 7 * a ^ 5
          + a ^ 6) / a ^ 6) := by
    rw [hR, hE0]
    ring
  rw [hR2]
  have hmul := mul_le_mul_of_nonneg_left hle (by norm_num : (0 : ℝ) ≤ 4 / 7)
  exact hmul.trans_lt hfin

private lemma hFinal8 (a : ℝ) (ha : ((((8 : ℕ))) : ℝ) - 1 ≤ a)
    (hW : lambertMap (-a / ((((8 : ℕ)) : ℝ) - 1)) =
      -(1 / ((((8 : ℕ)) : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((((8 : ℕ)) : ℝ) - 1))) :
    (∑ k ∈ Finset.range 8, ((k.factorial : ℕ) : ℝ)) - kurepaPartialIntegral 8 a < 1 := by
  have ha21 : (3 : ℝ) * ((((8 : ℕ)) : ℝ) - 1) = 21 := by norm_num
  have haL : (21 : ℝ) ≤ a := by
    rw [← ha21]
    exact a_ge_three 8 le_rfl a ha hW
  have ha0' : (0 : ℝ) < a := by linarith [haL]
  have hL0 : (0 : ℝ) < 21 := by norm_num
  have hPow := lambertPow 8 (by norm_num) a hW
  have hPow7 : a ^ 7 * Real.exp (-a) = 4 / 7 := hPow
  have hR := sum_factorial_sub_kurepaPartialIntegral 8 a
  have hpoly : (∑ k ∈ Finset.range 8,
        ((k.factorial : ℕ) : ℝ)
          * (∑ j ∈ Finset.range (k + 1), a ^ j / (((j.factorial : ℕ)) : ℝ)))
      = 5914 + 5913 * a + 2956 * a ^ 2 + 985 * a ^ 3 + 246 * a ^ 4 + 49 * a ^ 5
        + 8 * a ^ 6 + a ^ 7 := by
    simp [Finset.sum_range_succ,
      show ((0 : ℕ).factorial) = 1 from rfl, show ((1 : ℕ).factorial) = 1 from rfl,
      show ((2 : ℕ).factorial) = 2 from rfl, show ((3 : ℕ).factorial) = 6 from rfl,
      show ((4 : ℕ).factorial) = 24 from rfl, show ((5 : ℕ).factorial) = 120 from rfl,
      show ((6 : ℕ).factorial) = 720 from rfl, show ((7 : ℕ).factorial) = 5040 from rfl]
    ring
  rw [hpoly] at hR
  have hP0 : a ^ 7 ≠ 0 := pow_ne_zero _ ha0'.ne'
  have hE0 : Real.exp (-a) = (4 / 7 : ℝ) / a ^ 7 := by
    rw [eq_div_iff hP0]
    linear_combination hPow7
  have ha1 : a ≠ 0 := ha0'.ne'
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero _ ha0'.ne'
  have ha3 : a ^ 3 ≠ 0 := pow_ne_zero _ ha0'.ne'
  have ha4 : a ^ 4 ≠ 0 := pow_ne_zero _ ha0'.ne'
  have ha5 : a ^ 5 ≠ 0 := pow_ne_zero _ ha0'.ne'
  have ha6 : a ^ 6 ≠ 0 := pow_ne_zero _ ha0'.ne'
  have hsplit : (5914 + 5913 * a + 2956 * a ^ 2 + 985 * a ^ 3 + 246 * a ^ 4
        + 49 * a ^ 5 + 8 * a ^ 6 + a ^ 7) / a ^ 7
      = 5914 / a ^ 7 + 5913 / a ^ 6 + 2956 / a ^ 5 + 985 / a ^ 4 + 246 / a ^ 3
        + 49 / a ^ 2 + 8 / a + 1 := by
    field_simp
  have hle : (5914 + 5913 * a + 2956 * a ^ 2 + 985 * a ^ 3 + 246 * a ^ 4
        + 49 * a ^ 5 + 8 * a ^ 6 + a ^ 7) / a ^ 7
      ≤ 5914 / (21 : ℝ) ^ 7 + 5913 / (21 : ℝ) ^ 6 + 2956 / (21 : ℝ) ^ 5
        + 985 / (21 : ℝ) ^ 4 + 246 / (21 : ℝ) ^ 3 + 49 / (21 : ℝ) ^ 2 + 8 / (21 : ℝ)
        + 1 := by
    rw [hsplit]
    gcongr
  have hfin : (4 / 7 : ℝ)
        * (5914 / (21 : ℝ) ^ 7 + 5913 / (21 : ℝ) ^ 6 + 2956 / (21 : ℝ) ^ 5
          + 985 / (21 : ℝ) ^ 4 + 246 / (21 : ℝ) ^ 3 + 49 / (21 : ℝ) ^ 2
          + 8 / (21 : ℝ) + 1) < 1 := by
    norm_num
  have hR2 : (∑ k ∈ Finset.range 8, ((k.factorial : ℕ) : ℝ))
        - kurepaPartialIntegral 8 a
      = (4 / 7 : ℝ)
        * ((5914 + 5913 * a + 2956 * a ^ 2 + 985 * a ^ 3 + 246 * a ^ 4
          + 49 * a ^ 5 + 8 * a ^ 6 + a ^ 7) / a ^ 7) := by
    rw [hR, hE0]
    ring
  rw [hR2]
  have hmul := mul_le_mul_of_nonneg_left hle (by norm_num : (0 : ℝ) ≤ 4 / 7)
  exact hmul.trans_lt hfin

/-- **Lambert bounds for the left factorial.** Let $n \ge 5$ be an integer, let
$!n = \sum_{k=0}^{n-1} k!$ be the left factorial, let
$K_n(x) = \int_0^x e^{-t} \sum_{k=0}^{n-1} t^k \, dt$ be Kurepa's partial integral, let
$h(y) = y e^y$ be the Lambert map, and let $a$ be a real number with $a \ge n - 1$ and
$$h\left(-\frac{a}{n-1}\right) = -\frac{1}{n-1}\left(\frac{4}{7}\right)^{1/(n-1)}.$$
Then $K_n(a) < {!n} < K_n(a) + 1$.

The two conditions on $a$ say exactly that
$a = -(n-1)\, W_{-1}\left(-\frac{1}{n-1}\left(\frac{4}{7}\right)^{1/(n-1)}\right)$, where $W_{-1}$
is the lower real branch of the Lambert $W$ function; this is the paper's $a(n)$, and $K_n(a)$
is its $b(n)$.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Theorem 10 (`jis-2024-24.5.7-thm-10`). -/
public theorem kurepaPartialIntegral_lambertSequence_bounds (n : ℕ) (hn : 5 ≤ n)
    (a : ℝ) (ha : (n : ℝ) - 1 ≤ a)
    (hW : lambertMap (-a / ((n : ℝ) - 1)) =
      -(1 / ((n : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1))) :
    kurepaPartialIntegral n a < ∑ k ∈ Finset.range n, (k.factorial : ℝ) ∧
      ∑ k ∈ Finset.range n, (k.factorial : ℝ) < kurepaPartialIntegral n a + 1 := by
  have hn5 : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ha0' : (0 : ℝ) < a := by linarith [ha, hn5]
  refine ⟨kurepaPartialIntegral_lt_sum_factorial n (by omega) a ha0'.le, ?_⟩
  by_cases hn9 : 9 ≤ n
  · have h := hFinal9 n hn9 a ha hW
    linarith [h]
  · have hsmall : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
    rcases hsmall with rfl | rfl | rfl | rfl
    · have h := hFinal5 a ha hW
      linarith [h]
    · have h := hFinal6 a ha hW
      linarith [h]
    · have h := hFinal7 a ha hW
      linarith [h]
    · have h := hFinal8 a ha hW
      linarith [h]

end MetaMathlibExt
