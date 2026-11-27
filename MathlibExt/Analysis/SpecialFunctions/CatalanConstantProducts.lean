/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Leibniz
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

@[expose] public section

section

namespace MetaMathlibExt

/-! # Infinite product formulas for Catalan's constant
-/

/-- Single factor of the first two products. -/
private noncomputable def catF (n : ℕ) : ℝ :=
  (1 - 2 / (2 * (n : ℝ) + 1)) ^ ((n : ℤ) * (-1 : ℤ) ^ n)

private noncomputable def catP (m : ℕ) : ℝ := ∏ n ∈ Finset.Icc 1 (2 * m), catF n

private noncomputable def catQ (m : ℕ) : ℝ := ∏ n ∈ Finset.Icc 1 (2 * m + 1), catF n

private lemma catBase_odd (m : ℕ) :
    (1 : ℝ) - 2 / (4 * (m : ℝ) + 3) = (4 * (m : ℝ) + 1) / (4 * (m : ℝ) + 3) := by
  have hne : (4 : ℝ) * (m : ℝ) + 3 ≠ 0 := by positivity
  field_simp
  ring

private lemma catBase_even (m : ℕ) :
    (1 : ℝ) - 2 / (4 * (m : ℝ) + 5) = (4 * (m : ℝ) + 3) / (4 * (m : ℝ) + 5) := by
  have hne : (4 : ℝ) * (m : ℝ) + 5 ≠ 0 := by positivity
  field_simp
  ring

private lemma catBase_odd3 (m : ℕ) :
    (1 : ℝ) - 2 / (4 * (m : ℝ) + 7) = (4 * (m : ℝ) + 5) / (4 * (m : ℝ) + 7) := by
  have hne : (4 : ℝ) * (m : ℝ) + 7 ≠ 0 := by positivity
  field_simp
  ring

private lemma catF_succ_odd (m : ℕ) :
    catF (2 * m + 1) = ((4 * (m : ℝ) + 3) / (4 * (m : ℝ) + 1)) ^ (2 * m + 1) := by
  have hodd : Odd (2 * m + 1) := ⟨m, rfl⟩
  have hcast : (2 : ℝ) * ((2 * m + 1 : ℕ) : ℝ) + 1 = 4 * (m : ℝ) + 3 := by
    push_cast
    ring
  unfold catF
  rw [hodd.neg_one_pow, mul_neg_one, zpow_neg, zpow_natCast, hcast,
    catBase_odd, div_pow, div_pow, inv_div]

private lemma catF_succ_even (m : ℕ) :
    catF (2 * m + 2) = ((4 * (m : ℝ) + 3) / (4 * (m : ℝ) + 5)) ^ (2 * m + 2) := by
  have heven : Even (2 * m + 2) := ⟨m + 1, by ring⟩
  have hcast : (2 : ℝ) * ((2 * m + 2 : ℕ) : ℝ) + 1 = 4 * (m : ℝ) + 5 := by
    push_cast
    ring
  unfold catF
  rw [heven.neg_one_pow, mul_one, zpow_natCast, hcast, catBase_even]

private lemma catF_succ_odd3 (m : ℕ) :
    catF (2 * m + 3) = ((4 * (m : ℝ) + 7) / (4 * (m : ℝ) + 5)) ^ (2 * m + 3) := by
  have hodd : Odd (2 * m + 3) := ⟨m + 1, by ring⟩
  have hcast : (2 : ℝ) * ((2 * m + 3 : ℕ) : ℝ) + 1 = 4 * (m : ℝ) + 7 := by
    push_cast
    ring
  unfold catF
  rw [hodd.neg_one_pow, mul_neg_one, zpow_neg, zpow_natCast, hcast,
    catBase_odd3, div_pow, div_pow, inv_div]

/-- The second product is the first times the boundary factor. -/
private lemma catQ_eq (m : ℕ) :
    catQ m = catP m * (((4 * (m : ℝ) + 3) / (4 * (m : ℝ) + 1)) ^ (2 * m + 1)) := by
  have h := Finset.prod_Icc_succ_top (a := 1) (b := 2 * m) (f := catF) (by omega)
  rw [show (2 * m) + 1 = 2 * m + 1 from rfl] at h
  unfold catQ catP
  rw [h, catF_succ_odd]

private lemma cat_g0 : Filter.Tendsto (fun m : ℕ => (2 : ℝ) / ((4 : ℝ) * m + 1))
    Filter.atTop (nhds 0) := by
  have hup : Filter.Tendsto (fun m : ℕ => 2 * (1 / ((m : ℝ) + 1)))
      Filter.atTop (nhds 0) := by
    have h := Filter.Tendsto.mul (tendsto_const_nhds (x := (2 : ℝ)))
      tendsto_one_div_add_atTop_nhds_zero_nat
    rwa [mul_zero] at h
  refine squeeze_zero' (Filter.Eventually.of_forall fun m => by positivity) ?_ hup
  filter_upwards with m
  have h1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have h3 : (m : ℝ) + 1 ≤ 4 * (m : ℝ) + 1 := by
    have hnn : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
    linarith
  have h4 : (1 : ℝ) / (4 * (m : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
    one_div_le_one_div_of_le h1 h3
  have e1 : (2 : ℝ) / (4 * (m : ℝ) + 1) = 2 * (1 / (4 * (m : ℝ) + 1)) := by
    rw [mul_one_div]
  rw [e1]
  exact mul_le_mul_of_nonneg_left h4 (by norm_num)

private lemma cat_mg_half : Filter.Tendsto (fun m : ℕ => (m : ℝ) * (2 / ((4 : ℝ) * m + 1)))
    Filter.atTop (nhds (1 / 2)) := by
  have heq : (fun m : ℕ => (m : ℝ) * (2 / ((4 : ℝ) * m + 1))) =ᶠ[Filter.atTop]
      (fun m : ℕ => (2 : ℝ) / (4 + 1 / (m : ℝ))) := by
    filter_upwards [Filter.eventually_gt_atTop 0] with m hm
    have hmc : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h41 : (4 : ℝ) * (m : ℝ) + 1 ≠ 0 := by positivity
    have h43 : (4 : ℝ) + 1 / (m : ℝ) ≠ 0 := by positivity
    field_simp
  refine Filter.Tendsto.congr' heq.symm ?_
  have hden : Filter.Tendsto (fun m : ℕ => (4 : ℝ) + 1 / (m : ℝ))
      Filter.atTop (nhds 4) := by
    have h := (tendsto_const_nhds (x := (4 : ℝ))).add
      tendsto_one_div_atTop_nhds_zero_nat
    simpa using h
  have h := (tendsto_const_nhds (x := (2 : ℝ))).div hden (by norm_num)
  rwa [show (2 : ℝ) / 4 = 1 / 2 from by norm_num] at h

private lemma cat_pow_half : Filter.Tendsto
    (fun m : ℕ => (1 + 2 / ((4 : ℝ) * m + 1)) ^ m)
    Filter.atTop (nhds (Real.exp (1 / 2))) :=
  Real.tendsto_one_add_pow_exp_of_tendsto cat_mg_half

private lemma cat_one_g : Filter.Tendsto (fun m : ℕ => (1 : ℝ) + 2 / ((4 : ℝ) * m + 1))
    Filter.atTop (nhds 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).add cat_g0
  simpa using h

private lemma catRatio_lim : Filter.Tendsto
    (fun m : ℕ => ((4 * (m : ℝ) + 3) / (4 * (m : ℝ) + 1)) ^ (2 * m + 1))
    Filter.atTop (nhds (Real.exp 1)) := by
  have hF : Filter.Tendsto
      (fun m : ℕ => ((1 + 2 / ((4 : ℝ) * m + 1)) ^ m) ^ 2
        * (1 + 2 / ((4 : ℝ) * m + 1)))
      Filter.atTop (nhds ((Real.exp (1 / 2)) ^ 2 * 1)) :=
    (cat_pow_half.pow 2).mul cat_one_g
  have hexp1 : (Real.exp (1 / 2 : ℝ)) ^ 2 * 1 = Real.exp 1 := by
    rw [sq, ← Real.exp_add, mul_one,
      show (1 / 2 : ℝ) + 1 / 2 = 1 from by norm_num]
  rw [hexp1] at hF
  refine Filter.Tendsto.congr (fun m => ?_) hF
  have hb : (4 * (m : ℝ) + 3) / (4 * (m : ℝ) + 1)
      = 1 + 2 / ((4 : ℝ) * m + 1) := by
    have h41 : (4 : ℝ) * (m : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  rw [hb, ← pow_mul, ← pow_succ, show m * 2 + 1 = 2 * m + 1 from by ring]

/-- Third product (boundary-factor form). -/
private noncomputable def catR (m : ℕ) : ℝ :=
  ((∏ k ∈ Finset.range m, (4 * (k : ℝ) + 3) ^ (4 * k + 3)) /
    (∏ k ∈ Finset.range m, (4 * (k : ℝ) + 1) ^ (4 * k + 1))) ^ 2 *
  (4 * (m : ℝ) + 3) ^ (2 * m + 1) / (4 * (m : ℝ) + 1) ^ (6 * m + 1)

/-- The three new factors combine into the boundary-factor ratio. -/
private lemma key (m : ℕ) : catF (2 * m + 1) * (catF (2 * m + 2)) ^ 2 * catF (2 * m + 3)
    = (4 * (m : ℝ) + 3) ^ (6 * m + 5) * (4 * (m : ℝ) + 7) ^ (2 * m + 3) /
      ((4 * (m : ℝ) + 1) ^ (2 * m + 1) * (4 * (m : ℝ) + 5) ^ (6 * m + 7)) := by
  rw [catF_succ_odd, catF_succ_even, catF_succ_odd3]
  simp only [div_pow]
  have h1 : (0 : ℝ) < 4 * (m : ℝ) + 1 := by positivity
  have h3 : (0 : ℝ) < 4 * (m : ℝ) + 3 := by positivity
  have h5 : (0 : ℝ) < 4 * (m : ℝ) + 5 := by positivity
  have h7 : (0 : ℝ) < 4 * (m : ℝ) + 7 := by positivity
  have n1 : (4 : ℝ) * (m : ℝ) + 1 ≠ 0 := ne_of_gt h1
  have n3 : (4 : ℝ) * (m : ℝ) + 3 ≠ 0 := ne_of_gt h3
  have n5 : (4 : ℝ) * (m : ℝ) + 5 ≠ 0 := ne_of_gt h5
  have n7 : (4 : ℝ) * (m : ℝ) + 7 ≠ 0 := ne_of_gt h7
  field_simp
  ring

private lemma catPm_step (m : ℕ) :
    catP (m + 1) = catP m * catF (2 * m + 1) * catF (2 * m + 2) := by
  have h := Finset.prod_Icc_succ_top (a := 1) (b := 2 * m + 1) (f := catF) (by omega)
  rw [show (2 * m + 1) + 1 = 2 * m + 2 from by omega] at h
  have h2 := Finset.prod_Icc_succ_top (a := 1) (b := 2 * m) (f := catF) (by omega)
  unfold catP
  rw [show 2 * (m + 1) = 2 * m + 2 from by ring, h, h2]

private lemma catQm_step (m : ℕ) :
    catQ (m + 1) = catQ m * catF (2 * m + 2) * catF (2 * m + 3) := by
  have h1 := Finset.prod_Icc_succ_top (a := 1) (b := 2 * m + 2) (f := catF) (by omega)
  rw [show (2 * m + 2) + 1 = 2 * m + 3 from by omega] at h1
  have h2 := Finset.prod_Icc_succ_top (a := 1) (b := 2 * m + 1) (f := catF) (by omega)
  rw [show (2 * m + 1) + 1 = 2 * m + 2 from by omega] at h2
  unfold catQ
  rw [show 2 * (m + 1) + 1 = 2 * m + 3 from by ring, h1, h2]

private lemma catPQ_step (m : ℕ) : catP (m + 1) * catQ (m + 1)
    = (catP m * catQ m) *
      ((4 * (m : ℝ) + 3) ^ (6 * m + 5) * (4 * (m : ℝ) + 7) ^ (2 * m + 3) /
        ((4 * (m : ℝ) + 1) ^ (2 * m + 1) * (4 * (m : ℝ) + 5) ^ (6 * m + 7))) := by
  have hrw : catP (m + 1) * catQ (m + 1)
      = (catP m * catQ m) *
        (catF (2 * m + 1) * (catF (2 * m + 2)) ^ 2 * catF (2 * m + 3)) := by
    rw [catPm_step, catQm_step]
    ring
  rw [hrw, key]

private lemma catR_step (m : ℕ) : catR (m + 1)
    = catR m *
      ((4 * (m : ℝ) + 3) ^ (6 * m + 5) * (4 * (m : ℝ) + 7) ^ (2 * m + 3) /
        ((4 * (m : ℝ) + 1) ^ (2 * m + 1) * (4 * (m : ℝ) + 5) ^ (6 * m + 7))) := by
  have hA : (∏ k ∈ Finset.range m, (4 * (k : ℝ) + 3) ^ (4 * k + 3)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro k _
    exact pow_ne_zero _ (by positivity)
  have hB : (∏ k ∈ Finset.range m, (4 * (k : ℝ) + 1) ^ (4 * k + 1)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro k _
    exact pow_ne_zero _ (by positivity)
  have h1 : (0 : ℝ) < 4 * (m : ℝ) + 1 := by positivity
  have h3 : (0 : ℝ) < 4 * (m : ℝ) + 3 := by positivity
  have h5 : (0 : ℝ) < 4 * (m : ℝ) + 5 := by positivity
  have h7 : (0 : ℝ) < 4 * (m : ℝ) + 7 := by positivity
  have n1 : (4 : ℝ) * (m : ℝ) + 1 ≠ 0 := ne_of_gt h1
  have n3 : (4 : ℝ) * (m : ℝ) + 3 ≠ 0 := ne_of_gt h3
  have n5 : (4 : ℝ) * (m : ℝ) + 5 ≠ 0 := ne_of_gt h5
  have n7 : (4 : ℝ) * (m : ℝ) + 7 ≠ 0 := ne_of_gt h7
  unfold catR
  rw [Finset.prod_range_succ, Finset.prod_range_succ, Nat.cast_add, Nat.cast_one]
  rw [show 2 * (m + 1) + 1 = 2 * m + 3 from by ring,
    show 6 * (m + 1) + 1 = 6 * m + 7 from by ring,
    show (4 : ℝ) * (↑m + 1) + 3 = 4 * ↑m + 7 from by ring,
    show (4 : ℝ) * (↑m + 1) + 1 = 4 * ↑m + 5 from by ring]
  field_simp
  ring

/-- The third product equals the product of the first two, exactly. -/
private lemma catR_eq (m : ℕ) : catR m = catP m * catQ m := by
  induction m with
  | zero =>
    unfold catR catP catQ catF
    simp
    norm_num
  | succ m ih =>
    rw [catR_step, catPQ_step, ih]

/-- The second limit follows from the first plus the boundary factor. -/
private lemma catQ_of_catP (G : ℝ)
    (hP : Filter.Tendsto catP Filter.atTop
      (nhds (Real.exp (2 * G / Real.pi - 1 / 2)))) :
    Filter.Tendsto catQ Filter.atTop
      (nhds (Real.exp (2 * G / Real.pi + 1 / 2))) := by
  have hQ : catQ = fun m =>
      catP m * (((4 * (m : ℝ) + 3) / (4 * (m : ℝ) + 1)) ^ (2 * m + 1)) :=
    funext fun m => catQ_eq m
  rw [hQ]
  have hlim := hP.mul catRatio_lim
  have hexp : Real.exp (2 * G / Real.pi - 1 / 2) * Real.exp 1
      = Real.exp (2 * G / Real.pi + 1 / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rwa [hexp] at hlim

/-- The third limit follows from the first two. -/
private lemma catR_of_catPQ (G : ℝ)
    (hP : Filter.Tendsto catP Filter.atTop
      (nhds (Real.exp (2 * G / Real.pi - 1 / 2))))
    (hQ : Filter.Tendsto catQ Filter.atTop
      (nhds (Real.exp (2 * G / Real.pi + 1 / 2)))) :
    Filter.Tendsto catR Filter.atTop (nhds (Real.exp (4 * G / Real.pi))) := by
  have hR : catR = fun m => catP m * catQ m := funext fun m => catR_eq m
  rw [hR]
  have hlim := hP.mul hQ
  have hexp : Real.exp (2 * G / Real.pi - 1 / 2) *
      Real.exp (2 * G / Real.pi + 1 / 2) = Real.exp (4 * G / Real.pi) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rwa [hexp] at hlim

/-- Positivity of each base factor for `n ≥ 1`. -/
private lemma catBase_pos (n : ℕ) (hn : 1 ≤ n) :
    (0 : ℝ) < 1 - 2 / (2 * (n : ℝ) + 1) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : (0 : ℝ) < 2 * (n : ℝ) + 1 := by linarith
  have hnum : (0 : ℝ) < 2 * (n : ℝ) - 1 := by linarith
  have heq : (1 : ℝ) - 2 / (2 * (n : ℝ) + 1)
      = (2 * (n : ℝ) - 1) / (2 * (n : ℝ) + 1) := by
    field_simp
    ring
  rw [heq]
  exact div_pos hnum hden

/-- Positivity of each factor. -/
private lemma catF_pos (n : ℕ) (hn : 1 ≤ n) : 0 < catF n := by
  unfold catF
  exact zpow_pos (catBase_pos n hn) _

/-- Positivity of the first product. -/
private lemma catP_pos (m : ℕ) : 0 < catP m := by
  unfold catP
  apply Finset.prod_pos
  intro n hn
  simp only [Finset.mem_Icc] at hn
  exact catF_pos n hn.1

/-- Log of the first product as a finite sum. -/
private lemma catP_log (m : ℕ) : Real.log (catP m) =
    ∑ n ∈ Finset.Icc 1 (2 * m),
      (((n : ℤ) * (-1 : ℤ) ^ n : ℤ) : ℝ) * Real.log (1 - 2 / (2 * (n : ℝ) + 1)) := by
  unfold catP catF
  rw [Real.log_prod]
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mem_Icc] at hn
    rw [Real.log_zpow]
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    exact ne_of_gt (catF_pos n hn.1)

/-- First limit from the log-sum limit via continuity of `exp`. -/
private lemma catP_of_log (G : ℝ)
    (hlog : Filter.Tendsto (fun m : ℕ => Real.log (catP m))
      Filter.atTop (nhds (2 * G / Real.pi - 1 / 2))) :
    Filter.Tendsto catP Filter.atTop (nhds (Real.exp (2 * G / Real.pi - 1 / 2))) := by
  have hexp : Filter.Tendsto (fun m : ℕ => Real.exp (Real.log (catP m)))
      Filter.atTop (nhds (Real.exp (2 * G / Real.pi - 1 / 2))) :=
    hlog.rexp
  refine Filter.Tendsto.congr (fun m => ?_) hexp
  rw [Real.exp_log (catP_pos m)]

/-- Derivative of the log-difference antiderivative. -/
private lemma catInt_hasDerivAt (a u : ℝ) (ha : 2 ≤ a)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    HasDerivAt (fun v : ℝ => Real.log (a + v) - Real.log (a - v))
      (1 / (a + u) + 1 / (a - u)) u := by
  have hpos1 : (0 : ℝ) < a + u := by linarith
  have hpos2 : (0 : ℝ) < a - u := by linarith
  have hne1 : a + u ≠ 0 := ne_of_gt hpos1
  have hne2 : a - u ≠ 0 := ne_of_gt hpos2
  have h1 : HasDerivAt (fun v : ℝ => a + v) 1 u := by
    have h := (hasDerivAt_id (x := u)).const_add a
    simpa only [id_eq] using h
  have h2 : HasDerivAt (fun v : ℝ => a - v) (-1) u := by
    have h := (hasDerivAt_id (x := u)).const_sub a
    simpa only [id_eq] using h
  have hl1 : HasDerivAt (fun v : ℝ => Real.log (a + v)) (1 / (a + u)) u :=
    h1.log hne1
  have hl2 : HasDerivAt (fun v : ℝ => Real.log (a - v)) ((-1) / (a - u)) u :=
    h2.log hne2
  have hsub := hl1.sub hl2
  refine hsub.congr_deriv ?_
  have heq : ((-1 : ℝ) / (a - u)) = -(1 / (a - u)) := by
    rw [neg_div]
  rw [heq, sub_neg_eq_add]

/-- Integral of `a^2/(a^2-u^2)` over `[0,1]`. -/
private lemma catInt_integral (a : ℝ) (ha : 2 ≤ a) :
    (∫ u in (0 : ℝ)..1, a ^ 2 / (a ^ 2 - u ^ 2)) =
      (a / 2) * Real.log ((a + 1) / (a - 1)) := by
  have huIcc : Set.uIcc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 :=
    Set.uIcc_of_le (by norm_num)
  have hcont : ContinuousOn (fun u : ℝ => a ^ 2 / (a ^ 2 - u ^ 2))
      (Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.div continuousOn_const ?_ ?_
    · exact (continuousOn_const.sub (ContinuousOn.pow continuousOn_id 2))
    · intro u hu
      simp only [Set.mem_Icc] at hu
      have hub : u ^ 2 ≤ 1 := by
        have habs : |u| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
        calc u ^ 2 = |u| ^ 2 := by rw [sq_abs]
          _ ≤ 1 ^ 2 := by
              exact pow_le_pow_left₀ (abs_nonneg _) habs 2
          _ = 1 := one_pow 2
      have ha2 : (2 : ℝ) ≤ a ^ 2 := by
        calc (2 : ℝ) ≤ a := ha
          _ ≤ a ^ 2 := by
              have h1 : (1 : ℝ) ≤ a := by linarith
              calc a = a * 1 := by rw [mul_one]
                _ ≤ a * a := by
                    apply mul_le_mul_of_nonneg_left h1 (by linarith)
                _ = a ^ 2 := by rw [pow_two]
      linarith
  have hint : IntervalIntegrable (fun u : ℝ => a ^ 2 / (a ^ 2 - u ^ 2))
      MeasureTheory.volume (0 : ℝ) 1 :=
    hcont.intervalIntegrable_of_Icc (by norm_num)
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) (1 : ℝ),
      HasDerivAt (fun v : ℝ => (a / 2) * (Real.log (a + v) - Real.log (a - v)))
        (a ^ 2 / (a ^ 2 - u ^ 2)) u := by
    intro u hu
    rw [huIcc, Set.mem_Icc] at hu
    have hbase := catInt_hasDerivAt a u ha hu.1 hu.2
    have hmul := hbase.const_mul (a / 2)
    refine hmul.congr_deriv ?_
    have hpos1 : (0 : ℝ) < a + u := by linarith
    have hpos2 : (0 : ℝ) < a - u := by linarith
    have hne1 : a + u ≠ 0 := ne_of_gt hpos1
    have hne2 : a - u ≠ 0 := ne_of_gt hpos2
    have hne3 : a ^ 2 - u ^ 2 ≠ 0 := by
      have : a ^ 2 - u ^ 2 = (a + u) * (a - u) := by ring
      rw [this]
      exact mul_ne_zero hne1 hne2
    field_simp
    ring
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hftc]
  have h0 : (a / 2) * (Real.log (a + (0 : ℝ)) - Real.log (a - (0 : ℝ))) = 0 := by
    simp only [add_zero, sub_zero, sub_self, mul_zero]
  rw [h0, sub_zero]
  have hlog : Real.log (a + (1 : ℝ)) - Real.log (a - (1 : ℝ))
      = Real.log ((a + 1) / (a - 1)) := by
    rw [Real.log_div (by linarith) (by linarith)]
  rw [hlog]

/-- Finite alternating integrand whose integral is the log-sum. -/
private noncomputable def catFint (N : ℕ) (u : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (-1 : ℝ) ^ (n + 1) * (u ^ 2 / ((2 * (n : ℝ)) ^ 2 - u ^ 2))

/-- Even alternating unit sums vanish. -/
private lemma catAlt_sum_zero (m : ℕ) :
    ∑ n ∈ Finset.Icc 1 (2 * m), (-1 : ℝ) ^ (n + 1) = 0 := by
  induction m with
  | zero =>
    simp only [mul_zero]
    rw [Finset.Icc_eq_empty_of_lt (by norm_num : (0 : ℕ) < 1)]
    simp only [Finset.sum_empty]
  | succ m ih =>
    have h1 := Finset.sum_Icc_succ_top (a := 1) (b := 2 * m + 1)
      (f := fun n : ℕ => (-1 : ℝ) ^ (n + 1)) (by omega)
    have h2 := Finset.sum_Icc_succ_top (a := 1) (b := 2 * m)
      (f := fun n : ℕ => (-1 : ℝ) ^ (n + 1)) (by omega)
    have heq : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
    rw [heq, h1, h2, ih]
    have eTop2 : (-1 : ℝ) ^ (((2 * m + 1)) + 1) = 1 := by
      have hexp : ((2 * m + 1 : ℕ)) + 1 = 2 * (m + 1) := by ring
      rw [hexp, pow_mul]
      norm_num
    have eTop1 : (-1 : ℝ) ^ (((2 * m + 1 + 1 : ℕ)) + 1) = -1 := by
      have hexp : ((2 * m + 1 + 1 : ℕ)) + 1 = 2 * (m + 1) + 1 := by ring
      rw [hexp, pow_succ, pow_mul]
      norm_num
    rw [eTop2, eTop1]
    norm_num

/-- Each log term as an integral. -/
private lemma catTerm_eq_integral (n : ℕ) (hn : 1 ≤ n) :
    ((((n : ℤ) * (-1 : ℤ) ^ n : ℤ)) : ℝ) * Real.log (1 - 2 / (2 * (n : ℝ) + 1)) =
      (-1 : ℝ) ^ (n + 1) * (∫ u in (0 : ℝ)..1,
        ((2 * (n : ℝ)) ^ 2 / ((2 * (n : ℝ)) ^ 2 - u ^ 2))) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hcast : ((((n : ℤ) * (-1 : ℤ) ^ n : ℤ)) : ℝ) = (n : ℝ) * (-1 : ℝ) ^ n := by
    push_cast
    ring
  have hbase : (1 : ℝ) - 2 / (2 * (n : ℝ) + 1)
      = (2 * (n : ℝ) - 1) / (2 * (n : ℝ) + 1) := by
    have hne : (2 : ℝ) * (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  have hpos1 : (0 : ℝ) < 2 * (n : ℝ) - 1 := by linarith
  have hpos2 : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have hlog : Real.log (1 - 2 / (2 * (n : ℝ) + 1))
      = -Real.log ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) - 1)) := by
    rw [hbase, Real.log_div (ne_of_gt hpos1) (ne_of_gt hpos2),
      Real.log_div (ne_of_gt hpos2) (ne_of_gt hpos1)]
    ring
  have ha : (2 : ℝ) ≤ 2 * (n : ℝ) := by linarith
  have hint := catInt_integral (2 * (n : ℝ)) ha
  have harg : ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) - 1))
      = ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) - 1)) := rfl
  rw [hcast, hlog, hint]
  have hpow : (-1 : ℝ) ^ (n + 1) = (-1 : ℝ) ^ n * (-1) := pow_succ _ _
  rw [hpow]
  ring

/-- Log-sum as an integral of the finite alternating sum. -/
private lemma catP_log_eq_integral (m : ℕ) :
    Real.log (catP m) = ∫ u in (0 : ℝ)..1, catFint (2 * m) u := by
  rw [catP_log]
  have hterm : ∀ n ∈ Finset.Icc 1 (2 * m),
      ((((n : ℤ) * (-1 : ℤ) ^ n : ℤ)) : ℝ) * Real.log (1 - 2 / (2 * (n : ℝ) + 1)) =
        ∫ u in (0 : ℝ)..1,
          (-1 : ℝ) ^ (n + 1) * (((2 * (n : ℝ)) ^ 2 / ((2 * (n : ℝ)) ^ 2 - u ^ 2))) := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    rw [catTerm_eq_integral n hn.1, intervalIntegral.integral_const_mul]
  rw [Finset.sum_congr rfl hterm]
  rw [← intervalIntegral.integral_finsetSum]
  · apply intervalIntegral.integral_congr
    intro u hu
    have huIcc : Set.uIcc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 :=
      Set.uIcc_of_le (by norm_num)
    rw [huIcc, Set.mem_Icc] at hu
    dsimp only []
    unfold catFint
    have hsplit : ∀ n ∈ Finset.Icc 1 (2 * m),
        (-1 : ℝ) ^ (n + 1) * (((2 * (n : ℝ)) ^ 2 / ((2 * (n : ℝ)) ^ 2 - u ^ 2))) =
          (-1 : ℝ) ^ (n + 1) +
            (-1 : ℝ) ^ (n + 1) * (u ^ 2 / ((2 * (n : ℝ)) ^ 2 - u ^ 2)) := by
      intro n hn
      simp only [Finset.mem_Icc] at hn
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
      have hub : u ^ 2 ≤ 1 := by
        have habs : |u| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
        calc u ^ 2 = |u| ^ 2 := by rw [sq_abs]
          _ ≤ 1 ^ 2 := by
              exact pow_le_pow_left₀ (abs_nonneg _) habs 2
          _ = 1 := one_pow 2
      have ha2 : (4 : ℝ) ≤ ((2 * (n : ℝ)) ^ 2) := by
        have h2n : (2 : ℝ) ≤ 2 * (n : ℝ) := by linarith
        calc (4 : ℝ) = 2 ^ 2 := by norm_num
          _ ≤ (2 * (n : ℝ)) ^ 2 := by
              exact pow_le_pow_left₀ (by norm_num) h2n 2
      have hne : ((2 * (n : ℝ)) ^ 2 - u ^ 2) ≠ 0 := by linarith
      have hdiv : ((2 * (n : ℝ)) ^ 2 / (((2 * (n : ℝ)) ^ 2 - u ^ 2)))
          = 1 + u ^ 2 / (((2 * (n : ℝ)) ^ 2 - u ^ 2)) := by
        rw [div_eq_iff hne]
        have hcancel : (u ^ 2 / (((2 * (n : ℝ)) ^ 2 - u ^ 2))) * (((2 * (n : ℝ)) ^ 2 - u ^ 2))
            = u ^ 2 :=
          div_mul_cancel₀ _ hne
        have hmul : (1 + u ^ 2 / (((2 * (n : ℝ)) ^ 2 - u ^ 2))) * (((2 * (n : ℝ)) ^ 2 - u ^ 2))
            = (((2 * (n : ℝ)) ^ 2 - u ^ 2)) + u ^ 2 := by
          rw [add_mul, one_mul, hcancel]
        rw [hmul]
        ring
      calc (-1 : ℝ) ^ (n + 1) * (((2 * (n : ℝ)) ^ 2 / ((2 * (n : ℝ)) ^ 2 - u ^ 2)))
          = (-1 : ℝ) ^ (n + 1) * (1 + u ^ 2 / ((2 * (n : ℝ)) ^ 2 - u ^ 2)) := by
            rw [hdiv]
        _ = (-1 : ℝ) ^ (n + 1) + (-1 : ℝ) ^ (n + 1) * (u ^ 2 / ((2 * (n : ℝ)) ^ 2 - u ^ 2)) := by
            ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, catAlt_sum_zero m]
    simp only [zero_add]
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    have hcont : ContinuousOn
        (fun u : ℝ => (-1 : ℝ) ^ (n + 1) * (((2 * (n : ℝ)) ^ 2 / ((2 * (n : ℝ)) ^ 2 - u ^ 2))))
        (Set.Icc (0 : ℝ) 1) := by
      apply ContinuousOn.const_mul ?_
      apply ContinuousOn.div continuousOn_const ?_ ?_
      · exact (continuousOn_const.sub (ContinuousOn.pow continuousOn_id 2))
      · intro u hu
        simp only [Set.mem_Icc] at hu
        have hub : u ^ 2 ≤ 1 := by
          have habs : |u| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
          calc u ^ 2 = |u| ^ 2 := by rw [sq_abs]
            _ ≤ 1 ^ 2 := by
                exact pow_le_pow_left₀ (abs_nonneg _) habs 2
            _ = 1 := one_pow 2
        have ha2 : (4 : ℝ) ≤ ((2 * (n : ℝ)) ^ 2) := by
          have h2n : (2 : ℝ) ≤ 2 * (n : ℝ) := by linarith
          calc (4 : ℝ) = 2 ^ 2 := by norm_num
            _ ≤ (2 * (n : ℝ)) ^ 2 := by
                exact pow_le_pow_left₀ (by norm_num) h2n 2
        linarith
    exact hcont.intervalIntegrable_of_Icc (by norm_num)

/-- Cot difference gives cosecant. -/
private lemma catCsc_cot_diff (v : ℂ) (hv : Complex.sin v ≠ 0) :
    Complex.cot v - Complex.cot (2 * v) = 1 / Complex.sin (2 * v) := by
  unfold Complex.cot
  have hsin2 : Complex.sin (2 * v) = 2 * Complex.sin v * Complex.cos v := by
    rw [Complex.sin_two_mul]
  have hcos2 : Complex.cos (2 * v) = 2 * Complex.cos v ^ 2 - 1 := by
    rw [Complex.cos_two_mul]
  rw [hsin2, hcos2]
  field_simp
  ring

/-- Real points in `(0,1)` avoid the integers in `ℂ`. -/
private lemma catMem_integerComplement (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    (x : ℂ) ∈ Complex.integerComplement := by
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨n, hn⟩
  have hre : ((n : ℂ).re) = (((x : ℝ) : ℂ).re) := by rw [hn]
  simp only [Complex.intCast_re, Complex.ofReal_re] at hre
  have h0 : (0 : ℤ) < n := by
    have hpos : (0 : ℝ) < (n : ℝ) := by rw [hre]; exact hx0
    exact_mod_cast hpos
  have h1 : n < (1 : ℤ) := by
    have hlt : (n : ℝ) < (1 : ℝ) := by rw [hre]; exact hx1
    exact_mod_cast hlt
  omega

/-- Cosecant as cot difference, scaled by `π`. -/
private lemma catCsc_pi_eq (z : ℂ) (hz2 : z / 2 ∈ Complex.integerComplement) :
    ((Real.pi : ℝ) : ℂ) * Complex.cot (((Real.pi : ℝ) : ℂ) * (z / 2))
      - ((Real.pi : ℝ) : ℂ) * Complex.cot (((Real.pi : ℝ) : ℂ) * z)
      = ((Real.pi : ℝ) : ℂ) / Complex.sin (((Real.pi : ℝ) : ℂ) * z) := by
  have hsin : Complex.sin (((Real.pi : ℝ) : ℂ) * (z / 2)) ≠ 0 :=
    sin_pi_mul_ne_zero hz2
  have hdiff := catCsc_cot_diff (((Real.pi : ℝ) : ℂ) * (z / 2)) hsin
  have h2v : 2 * (((Real.pi : ℝ) : ℂ) * (z / 2)) = ((Real.pi : ℝ) : ℂ) * z := by
    ring
  rw [h2v] at hdiff
  have hmul := congrArg (fun w : ℂ => ((Real.pi : ℝ) : ℂ) * w) hdiff
  simp only [mul_sub, mul_one_div] at hmul
  exact hmul

/-- Cosecant minus pole as a difference of cot series. -/
private lemma catCsc_sub_eq (z : ℂ) (hz : z ∈ Complex.integerComplement)
    (hz2 : z / 2 ∈ Complex.integerComplement) :
    ((Real.pi : ℝ) : ℂ) / Complex.sin (((Real.pi : ℝ) : ℂ) * z) - 1 / z =
      ∑' n : ℕ, (cotTerm (z / 2) n - cotTerm z n) := by
  have hz0 : z ≠ 0 := Complex.integerComplement.ne_zero hz
  have hpi := catCsc_pi_eq z hz2
  have hcot_z : ((Real.pi : ℝ) : ℂ) * Complex.cot (((Real.pi : ℝ) : ℂ) * z) - 1 / z =
      ∑' n : ℕ, cotTerm z n :=
    cot_series_rep' hz
  have hcot_z2 : ((Real.pi : ℝ) : ℂ) * Complex.cot (((Real.pi : ℝ) : ℂ) * (z / 2))
      - 1 / (z / 2) =
      ∑' n : ℕ, cotTerm (z / 2) n :=
    cot_series_rep' hz2
  have hdiv : (1 : ℂ) / (z / 2) = 2 / z := by
    field_simp
  have hb : Summable (fun n : ℕ => cotTerm (z / 2) n) :=
    summable_cotTerm hz2
  have ha : Summable (fun n : ℕ => cotTerm z n) :=
    summable_cotTerm hz
  have hsub : ∑' n : ℕ, (cotTerm (z / 2) n - cotTerm z n)
      = (∑' n : ℕ, cotTerm (z / 2) n) - ∑' n : ℕ, cotTerm z n :=
    (hb.hasSum.sub ha.hasSum).tsum_eq
  rw [hsub, ← hcot_z2, ← hcot_z, hdiv, ← hpi]
  ring

/-- Halved cot terms double the even cot terms. -/
private lemma catCot_half_eq (z : ℂ) (n : ℕ) :
    cotTerm (z / 2) n = 2 * cotTerm z (2 * n + 1) := by
  unfold cotTerm
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat]
  have heq1 : z / 2 - (((n : ℂ) + 1)) = (z - 2 * (((n : ℂ) + 1))) / 2 := by
    ring
  have heq2 : z / 2 + (((n : ℂ) + 1)) = (z + 2 * (((n : ℂ) + 1))) / 2 := by
    ring
  have hexp : 2 * (((n : ℂ) + 1)) = (2 * (n : ℂ) + 1) + 1 := by
    ring
  rw [heq1, heq2, one_div_div, one_div_div, hexp]
  ring

/-- Difference series equals alternating cot series. -/
private lemma catCsc_even_odd (z : ℂ) (hz : z ∈ Complex.integerComplement)
    (hz2 : z / 2 ∈ Complex.integerComplement) :
    ∑' n : ℕ, (cotTerm (z / 2) n - cotTerm z n)
      = ∑' n : ℕ, (-1 : ℂ) ^ (n + 1) * cotTerm z n := by
  have hA : Summable (fun n : ℕ => cotTerm z n) := summable_cotTerm hz
  have hB : Summable (fun n : ℕ => cotTerm (z / 2) n) := summable_cotTerm hz2
  have hinj_even : Function.Injective (fun k : ℕ => 2 * k) := by
    intro a b h
    dsimp only [] at h
    omega
  have hinj_odd : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b h
    dsimp only [] at h
    omega
  have hA_even : Summable (fun k : ℕ => cotTerm z (2 * k)) :=
    hA.comp_injective hinj_even
  have hA_odd : Summable (fun k : ℕ => cotTerm z (2 * k + 1)) :=
    hA.comp_injective hinj_odd
  have hB_eq : (fun n : ℕ => cotTerm (z / 2) n)
      = (fun n : ℕ => 2 * cotTerm z (2 * n + 1)) := by
    funext n
    exact catCot_half_eq z n
  have hB_tsum : (∑' n : ℕ, cotTerm (z / 2) n)
      = 2 * ∑' k : ℕ, cotTerm z (2 * k + 1) := by
    rw [hB_eq, tsum_mul_left]
  have hA_split : (∑' n : ℕ, cotTerm z n)
      = (∑' k : ℕ, cotTerm z (2 * k)) + ∑' k : ℕ, cotTerm z (2 * k + 1) := by
    rw [tsum_even_add_odd (f := fun n : ℕ => cotTerm z n) hA_even hA_odd]
  have hpow_even : ∀ k : ℕ, (-1 : ℂ) ^ ((2 * k) + 1) = -1 := by
    intro k
    rw [pow_succ, pow_mul]
    norm_num
  have hpow_odd : ∀ k : ℕ, (-1 : ℂ) ^ (((2 * k + 1)) + 1) = 1 := by
    intro k
    have hexp : ((2 * k + 1 : ℕ)) + 1 = 2 * (k + 1) := by ring
    rw [hexp, pow_mul]
    norm_num
  have hf_even_eq : (fun k : ℕ => (-1 : ℂ) ^ (((2 * k)) + 1) * cotTerm z (2 * k))
      = (fun k : ℕ => -(cotTerm z (2 * k))) := by
    funext k
    rw [hpow_even k]
    ring
  have hf_odd_eq : (fun k : ℕ => (-1 : ℂ) ^ (((2 * k + 1)) + 1) * cotTerm z (2 * k + 1))
      = (fun k : ℕ => cotTerm z (2 * k + 1)) := by
    funext k
    rw [hpow_odd k, one_mul]
  have hf_even : Summable (fun k : ℕ => (-1 : ℂ) ^ (((2 * k)) + 1) * cotTerm z (2 * k)) := by
    rw [hf_even_eq]
    exact hA_even.neg
  have hf_odd : Summable (fun k : ℕ => (-1 : ℂ) ^ (((2 * k + 1)) + 1) * cotTerm z (2 * k + 1)) := by
    rw [hf_odd_eq]
    exact hA_odd
  have hf : Summable (fun n : ℕ => (-1 : ℂ) ^ (n + 1) * cotTerm z n) :=
    Summable.even_add_odd (f := fun n : ℕ => (-1 : ℂ) ^ (n + 1) * cotTerm z n)
      hf_even hf_odd
  have hf_split : (∑' n : ℕ, (-1 : ℂ) ^ (n + 1) * cotTerm z n)
      = (∑' k : ℕ, (-1 : ℂ) ^ (((2 * k)) + 1) * cotTerm z (2 * k))
        + ∑' k : ℕ, (-1 : ℂ) ^ (((2 * k + 1)) + 1) * cotTerm z (2 * k + 1) := by
    rw [tsum_even_add_odd
      (f := fun n : ℕ => (-1 : ℂ) ^ (n + 1) * cotTerm z n) hf_even hf_odd]
  rw [hf_split, hf_even_eq, hf_odd_eq]
  have hneg : (∑' k : ℕ, -(cotTerm z (2 * k)))
      = -(∑' k : ℕ, cotTerm z (2 * k)) := tsum_neg
  rw [hneg]
  have hdiff : ∑' n : ℕ, (cotTerm (z / 2) n - cotTerm z n)
      = (∑' n : ℕ, cotTerm (z / 2) n) - ∑' n : ℕ, cotTerm z n :=
    (hB.hasSum.sub hA.hasSum).tsum_eq
  rw [hdiff, hB_tsum, hA_split]
  ring

/-- Alternating cot terms as alternating reciprocal differences. -/
private lemma catCotTerm_alt_eq (z : ℂ) (hz : z ∈ Complex.integerComplement)
    (n : ℕ) :
    (-1 : ℂ) ^ (n + 1) * cotTerm z n
      = 2 * z * (((-1 : ℂ) ^ n / ((((n + 1 : ℕ) : ℂ) ^ 2 - z ^ 2)))) := by
  unfold cotTerm
  simp only [Nat.cast_add, Nat.cast_one]
  have hsub : (z - (((n : ℂ) + 1))) ≠ 0 := by
    have h := Complex.integerComplement_add_ne_zero hz (-(((n : ℤ) + 1)))
    simpa only [sub_eq_add_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
      Int.cast_neg, Nat.cast_add, Nat.cast_one] using h
  have hadd : (z + (((n : ℂ) + 1))) ≠ 0 := by
    have h := Complex.integerComplement_add_ne_zero hz (((n : ℤ) + 1))
    simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one, Nat.cast_add,
      Nat.cast_one] using h
  have hpow : (z ^ 2 - (((n : ℂ) + 1) ^ 2)) ≠ 0 := by
    have h := Complex.integerComplement_pow_two_ne_pow_two hz (((n : ℤ) + 1))
    have heq : ((((n : ℤ) + 1) : ℤ) : ℂ) = (((n : ℂ) + 1)) := by
      simp only [Int.cast_add, Int.cast_natCast, Int.cast_one]
    rw [heq] at h
    exact sub_ne_zero.mpr h
  have hpow2 : ((((n : ℂ) + 1) ^ 2 - z ^ 2)) ≠ 0 := by
    have : ((((n : ℂ) + 1) ^ 2 - z ^ 2)) = -(z ^ 2 - (((n : ℂ) + 1) ^ 2)) := by
      ring
    rw [this]
    exact neg_ne_zero.mpr hpow
  have hpow_succ : (-1 : ℂ) ^ (n + 1) = (-1 : ℂ) ^ n * (-1) := pow_succ _ _
  rw [hpow_succ]
  field_simp
  ring

/-- Cosecant partial fractions with alternating signs. -/
private lemma catCsc_tsum (z : ℂ) (hz : z ∈ Complex.integerComplement)
    (hz2 : z / 2 ∈ Complex.integerComplement) (hz0 : z ≠ 0) :
    ∑' n : ℕ, ((-1 : ℂ) ^ n / ((((n + 1 : ℕ) : ℂ) ^ 2 - z ^ 2)))
      = ((((Real.pi : ℝ) : ℂ) / Complex.sin (((Real.pi : ℝ) : ℂ) * z) - 1 / z)
        / (2 * z)) := by
  have hsub := catCsc_sub_eq z hz hz2
  have heven := catCsc_even_odd z hz hz2
  have hA : Summable (fun n : ℕ => cotTerm z n) := summable_cotTerm hz
  have hinj_even : Function.Injective (fun k : ℕ => 2 * k) := by
    intro a b h
    dsimp only [] at h
    omega
  have hinj_odd : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b h
    dsimp only [] at h
    omega
  have hA_even : Summable (fun k : ℕ => cotTerm z (2 * k)) :=
    hA.comp_injective hinj_even
  have hA_odd : Summable (fun k : ℕ => cotTerm z (2 * k + 1)) :=
    hA.comp_injective hinj_odd
  have hpow_even : ∀ k : ℕ, (-1 : ℂ) ^ ((2 * k) + 1) = -1 := by
    intro k
    rw [pow_succ, pow_mul]
    norm_num
  have hpow_odd : ∀ k : ℕ, (-1 : ℂ) ^ (((2 * k + 1)) + 1) = 1 := by
    intro k
    have hexp : ((2 * k + 1 : ℕ)) + 1 = 2 * (k + 1) := by ring
    rw [hexp, pow_mul]
    norm_num
  have hf_even_eq : (fun k : ℕ => (-1 : ℂ) ^ (((2 * k)) + 1) * cotTerm z (2 * k))
      = (fun k : ℕ => -(cotTerm z (2 * k))) := by
    funext k
    rw [hpow_even k]
    ring
  have hf_odd_eq : (fun k : ℕ => (-1 : ℂ) ^ (((2 * k + 1)) + 1) * cotTerm z (2 * k + 1))
      = (fun k : ℕ => cotTerm z (2 * k + 1)) := by
    funext k
    rw [hpow_odd k, one_mul]
  have hf_even : Summable (fun k : ℕ => (-1 : ℂ) ^ (((2 * k)) + 1) * cotTerm z (2 * k)) := by
    rw [hf_even_eq]
    exact hA_even.neg
  have hf_odd : Summable (fun k : ℕ => (-1 : ℂ) ^ (((2 * k + 1)) + 1) * cotTerm z (2 * k + 1)) := by
    rw [hf_odd_eq]
    exact hA_odd
  have hg : Summable (fun n : ℕ => (-1 : ℂ) ^ (n + 1) * cotTerm z n) :=
    Summable.even_add_odd (f := fun n : ℕ => (-1 : ℂ) ^ (n + 1) * cotTerm z n)
      hf_even hf_odd
  have h2z : (2 : ℂ) * z ≠ 0 := mul_ne_zero (by norm_num) hz0
  have hfeq : (fun n : ℕ => (-1 : ℂ) ^ (n + 1) * cotTerm z n)
      = (fun n : ℕ => (2 * z) * (((-1 : ℂ) ^ n / ((((n + 1 : ℕ) : ℂ) ^ 2 - z ^ 2))))) := by
    funext n
    exact catCotTerm_alt_eq z hz n
  have hf : Summable (fun n : ℕ => (-1 : ℂ) ^ n / ((((n + 1 : ℕ) : ℂ) ^ 2 - z ^ 2))) := by
    have hdiv : Summable (fun n : ℕ => ((-1 : ℂ) ^ (n + 1) * cotTerm z n) / (2 * z)) :=
      hg.div_const (2 * z)
    have heq : (fun n : ℕ => ((-1 : ℂ) ^ (n + 1) * cotTerm z n) / (2 * z))
        = (fun n : ℕ => (-1 : ℂ) ^ n / ((((n + 1 : ℕ) : ℂ) ^ 2 - z ^ 2))) := by
      funext n
      rw [catCotTerm_alt_eq z hz n]
      field_simp
    rw [heq] at hdiv
    exact hdiv
  have hmul : (∑' n : ℕ, (-1 : ℂ) ^ (n + 1) * cotTerm z n)
      = (2 * z) * ∑' n : ℕ, ((-1 : ℂ) ^ n / ((((n + 1 : ℕ) : ℂ) ^ 2 - z ^ 2))) := by
    rw [hfeq, tsum_mul_left]
  have htrans : (((Real.pi : ℝ) : ℂ) / Complex.sin (((Real.pi : ℝ) : ℂ) * z) - 1 / z)
      = (2 * z) * ∑' n : ℕ, ((-1 : ℂ) ^ n / ((((n + 1 : ℕ) : ℂ) ^ 2 - z ^ 2))) :=
    hsub.trans (heven.trans hmul)
  have hdiv : ((((Real.pi : ℝ) : ℂ) / Complex.sin (((Real.pi : ℝ) : ℂ) * z) - 1 / z)
      / (2 * z))
      = ∑' n : ℕ, ((-1 : ℂ) ^ n / ((((n + 1 : ℕ) : ℂ) ^ 2 - z ^ 2))) := by
    rw [htrans, mul_div_cancel_left₀ _ h2z]
  exact hdiv.symm

/-- Real cosecant partial fractions. -/
private lemma catCsc_real_tsum (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) :
    ∑' n : ℕ, ((-1 : ℝ) ^ n / ((((n + 1 : ℕ) : ℝ) ^ 2 - (u / 2) ^ 2)))
      = ((Real.pi / Real.sin (Real.pi * (u / 2)) - 1 / (u / 2)) / (2 * (u / 2))) := by
  have hz0 : (0 : ℝ) < u / 2 := by linarith
  have hz1 : u / 2 < 1 := by linarith
  have hz : ((u / 2 : ℝ) : ℂ) ∈ Complex.integerComplement :=
    catMem_integerComplement (u / 2) hz0 hz1
  have hz2mem : (((u / 2 : ℝ) / 2 : ℝ) : ℂ) ∈ Complex.integerComplement := by
    apply catMem_integerComplement ((u / 2) / 2)
    · linarith
    · linarith
  have heq2 : (((u / 2 : ℝ) : ℂ) / 2) = ((((u / 2 : ℝ) / 2 : ℝ)) : ℂ) := by
    push_cast
    ring
  have hz2 : ((u / 2 : ℝ) : ℂ) / 2 ∈ Complex.integerComplement := by
    rw [heq2]
    exact hz2mem
  have hz0' : ((u / 2 : ℝ) : ℂ) ≠ 0 := by
    have hne : (u / 2 : ℝ) ≠ 0 := ne_of_gt hz0
    exact_mod_cast hne
  have hcomplex := catCsc_tsum ((u / 2 : ℝ) : ℂ) hz hz2 hz0'
  have hLHS : (∑' n : ℕ, (-1 : ℂ) ^ n / ((((n + 1 : ℕ) : ℂ) ^ 2 - ((u / 2 : ℝ) : ℂ) ^ 2)))
      = Complex.ofReal (∑' n : ℕ, (-1 : ℝ) ^ n / ((((n + 1 : ℕ) : ℝ) ^ 2 - (u / 2) ^ 2))) := by
    have hterm : ∀ n : ℕ, (-1 : ℂ) ^ n / ((((n + 1 : ℕ) : ℂ) ^ 2 - ((u / 2 : ℝ) : ℂ) ^ 2))
        = Complex.ofReal (((-1 : ℝ) ^ n / ((((n + 1 : ℕ) : ℝ) ^ 2 - (u / 2) ^ 2)))) := by
      intro n
      push_cast
      ring
    calc (∑' n : ℕ, (-1 : ℂ) ^ n / ((((n + 1 : ℕ) : ℂ) ^ 2 - ((u / 2 : ℝ) : ℂ) ^ 2)))
        = ∑' n : ℕ, Complex.ofReal (((-1 : ℝ) ^ n / ((((n + 1 : ℕ) : ℝ) ^ 2 - (u / 2) ^ 2)))) :=
          tsum_congr hterm
      _ = Complex.ofReal (∑' n : ℕ, (-1 : ℝ) ^ n / ((((n + 1 : ℕ) : ℝ) ^ 2 - (u / 2) ^ 2))) :=
          (RCLike.ofReal_tsum ℂ
            (fun n : ℕ => (-1 : ℝ) ^ n / ((((n + 1 : ℕ) : ℝ) ^ 2 - (u / 2) ^ 2)))).symm
  have hRHS : ((((Real.pi : ℝ) : ℂ) / Complex.sin (((Real.pi : ℝ) : ℂ) * ((u / 2 : ℝ) : ℂ))
      - 1 / ((u / 2 : ℝ) : ℂ)) / (2 * ((u / 2 : ℝ) : ℂ)))
      = Complex.ofReal (((Real.pi / Real.sin (Real.pi * (u / 2)) - 1 / (u / 2))
        / (2 * (u / 2)))) := by
    push_cast
    ring
  rw [hLHS] at hcomplex
  rw [hRHS] at hcomplex
  exact Complex.ofReal_injective hcomplex

/-- Pointwise limit of the finite alternating integrands. -/
private noncomputable def catFlim (u : ℝ) : ℝ :=
  if u = 0 then 0 else (Real.pi * u / (4 * Real.sin (Real.pi * u / 2)) - 1 / 2)

/-- Finite sums as range partial sums. -/
private lemma catFint_eq_range (N : ℕ) (u : ℝ) :
    catFint N u
      = ∑ k ∈ Finset.range N,
        (-1 : ℝ) ^ k * (u ^ 2 / ((4 * (((k + 1 : ℕ) : ℝ) ^ 2) - u ^ 2))) := by
  unfold catFint
  have hIcc : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico, Nat.lt_succ_iff]
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro k hk
  have hpow : (-1 : ℝ) ^ ((1 + k) + 1) = (-1 : ℝ) ^ k := by
    have hexp : (1 + k) + 1 = k + 2 := by ring
    rw [hexp, pow_add]
    norm_num
  have hcast : (((1 + k : ℕ) : ℝ)) = (((k + 1 : ℕ) : ℝ)) := by
    push_cast
    ring
  rw [hpow, hcast]
  ring

private noncomputable def ccp_term (u : ℝ) (k : ℕ) : ℝ :=
  u ^ 2 / (4 * (((k + 1 : ℕ) : ℝ) ^ 2) - u ^ 2)

private lemma ccp_term_den_pos (u : ℝ) (k : ℕ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 < 4 * (((k + 1 : ℕ) : ℝ) ^ 2) - u ^ 2 := by
  have hub : u ^ 2 ≤ 1 := by
    have habs : |u| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    calc
      u ^ 2 = |u| ^ 2 := by rw [sq_abs]
      _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ = 1 := one_pow 2
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_add_left 1 k
  have hk2 : (1 : ℝ) ≤ (((k + 1 : ℕ) : ℝ) ^ 2) := by
    calc
      (1 : ℝ) = 1 ^ 2 := by norm_num
      _ ≤ (((k + 1 : ℕ) : ℝ) ^ 2) := pow_le_pow_left₀ (by norm_num) hk 2
  linarith

private lemma ccp_term_nonneg (u : ℝ) (k : ℕ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ ccp_term u k := by
  unfold ccp_term
  exact div_nonneg (sq_nonneg u) (ccp_term_den_pos u k hu0 hu1).le

private lemma ccp_term_antitone (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Antitone (ccp_term u) := by
  intro k l hkl
  have hcast : ((k + 1 : ℕ) : ℝ) ≤ ((l + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_right hkl 1
  have hsquare : (((k + 1 : ℕ) : ℝ) ^ 2) ≤ (((l + 1 : ℕ) : ℝ) ^ 2) :=
    pow_le_pow_left₀ (by positivity) hcast 2
  unfold ccp_term
  apply div_le_div_of_nonneg_left (sq_nonneg u) (ccp_term_den_pos u k hu0 hu1)
  linarith

private noncomputable def ccp_alt_sum (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * a k

private lemma ccp_alt_sum_add_pair (a : ℕ → ℝ) (m : ℕ) :
    ccp_alt_sum a (2 * (m + 1)) =
      ccp_alt_sum a (2 * m) + a (2 * m) - a (2 * m + 1) := by
  have heven : (-1 : ℝ) ^ (2 * m) = 1 := by
    rw [pow_mul]
    norm_num
  have hodd : (-1 : ℝ) ^ (2 * m + 1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  unfold ccp_alt_sum
  rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, heven, hodd]
  ring

private lemma ccp_alt_sum_even_bounds (a : ℕ → ℝ) (ha : Antitone a) (m : ℕ) :
    0 ≤ ccp_alt_sum a (2 * m) ∧
      ccp_alt_sum a (2 * m) + a (2 * m) ≤ a 0 := by
  induction m with
  | zero =>
      simp [ccp_alt_sum]
  | succ m ih =>
      have hpair : a (2 * m + 1) ≤ a (2 * m) := ha (by omega)
      have hnext : a (2 * (m + 1)) ≤ a (2 * m + 1) := ha (by omega)
      constructor
      · rw [ccp_alt_sum_add_pair]
        linarith [ih.1]
      · rw [ccp_alt_sum_add_pair]
        linarith [ih.2]

private lemma ccp_alt_sum_bounds (a : ℕ → ℝ) (ha0 : ∀ k, 0 ≤ a k)
    (ha : Antitone a) (N : ℕ) :
    0 ≤ ccp_alt_sum a N ∧ ccp_alt_sum a N ≤ a 0 := by
  rcases N.even_or_odd' with ⟨m, hm | hm⟩
  · subst N
    have h := ccp_alt_sum_even_bounds a ha m
    constructor
    · exact h.1
    · linarith [ha0 (2 * m)]
  · subst N
    have h := ccp_alt_sum_even_bounds a ha m
    have heven : (-1 : ℝ) ^ (2 * m) = 1 := by
      rw [pow_mul]
      norm_num
    have hsum : ccp_alt_sum a (2 * m + 1) =
        ccp_alt_sum a (2 * m) + a (2 * m) := by
      unfold ccp_alt_sum
      rw [Finset.sum_range_succ, heven, one_mul]
    rw [hsum]
    exact ⟨add_nonneg h.1 (ha0 (2 * m)), h.2⟩

private lemma ccp_catFint_eq_alt_sum (N : ℕ) (u : ℝ) :
    catFint N u = ccp_alt_sum (ccp_term u) N := by
  rw [catFint_eq_range]
  unfold ccp_alt_sum ccp_term
  rfl

private lemma ccp_term_zero_le_one (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ccp_term u 0 ≤ 1 := by
  have hub : u ^ 2 ≤ 1 := by
    have habs : |u| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    calc
      u ^ 2 = |u| ^ 2 := by rw [sq_abs]
      _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ = 1 := one_pow 2
  have hden : 0 < (4 : ℝ) - u ^ 2 := by linarith
  rw [ccp_term]
  norm_num only [zero_add, Nat.cast_one, one_pow, mul_one]
  exact (div_le_one hden).2 (by linarith)

private lemma ccp_catFint_norm_le_one (N : ℕ) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖catFint N u‖ ≤ 1 := by
  have hbounds := ccp_alt_sum_bounds (ccp_term u)
    (fun k => ccp_term_nonneg u k hu0 hu1) (ccp_term_antitone u hu0 hu1) N
  rw [← ccp_catFint_eq_alt_sum] at hbounds
  rw [Real.norm_eq_abs, abs_of_nonneg hbounds.1]
  exact hbounds.2.trans (ccp_term_zero_le_one u hu0 hu1)

/-- Summability of alternating terms for fixed `u`. -/
private lemma catFint_summable (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Summable (fun k : ℕ =>
      (-1 : ℝ) ^ k * (u ^ 2 / ((4 * (((k + 1 : ℕ) : ℝ) ^ 2) - u ^ 2)))) := by
  have hbound : ∀ k : ℕ,
      ‖(-1 : ℝ) ^ k * (u ^ 2 / ((4 * (((k + 1 : ℕ) : ℝ) ^ 2) - u ^ 2)))‖
        ≤ 1 / (3 * (((k + 1 : ℕ) : ℝ) ^ 2)) := by
    intro k
    have hub : u ^ 2 ≤ 1 := by
      have habs : |u| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      calc u ^ 2 = |u| ^ 2 := by rw [sq_abs]
        _ ≤ 1 ^ 2 := by
            exact pow_le_pow_left₀ (abs_nonneg _) habs 2
        _ = 1 := one_pow 2
    have hden : (3 : ℝ) * (((k + 1 : ℕ) : ℝ) ^ 2)
        ≤ 4 * (((k + 1 : ℕ) : ℝ) ^ 2) - u ^ 2 := by
      have hm : (1 : ℝ) ≤ (((k + 1 : ℕ) : ℝ) ^ 2) := by
        have h1 : (1 : ℝ) ≤ (((k + 1 : ℕ) : ℝ)) := by
          have : (1 : ℕ) ≤ k + 1 := Nat.le_add_left 1 k
          exact_mod_cast this
        calc (1 : ℝ) = 1 ^ 2 := by norm_num
          _ ≤ (((k + 1 : ℕ) : ℝ) ^ 2) := by
              exact pow_le_pow_left₀ (by norm_num) h1 2
      linarith
    have hpos : (0 : ℝ) < 4 * (((k + 1 : ℕ) : ℝ) ^ 2) - u ^ 2 := by
      have hm : (1 : ℝ) ≤ (((k + 1 : ℕ) : ℝ) ^ 2) := by
        have h1 : (1 : ℝ) ≤ (((k + 1 : ℕ) : ℝ)) := by
          have : (1 : ℕ) ≤ k + 1 := Nat.le_add_left 1 k
          exact_mod_cast this
        calc (1 : ℝ) = 1 ^ 2 := by norm_num
          _ ≤ (((k + 1 : ℕ) : ℝ) ^ 2) := by
              exact pow_le_pow_left₀ (by norm_num) h1 2
      linarith [hden, hm]
    have hnonneg : (0 : ℝ) ≤ u ^ 2 / ((4 * (((k + 1 : ℕ) : ℝ) ^ 2) - u ^ 2)) := by
      apply div_nonneg (sq_nonneg _) (le_of_lt hpos)
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs,
      abs_of_nonneg hnonneg]
    rw [div_le_div_iff₀ hpos (by positivity)]
    have h1 : u ^ 2 * (3 * (((k + 1 : ℕ) : ℝ) ^ 2))
        ≤ 1 * (4 * (((k + 1 : ℕ) : ℝ) ^ 2) - u ^ 2) := by
      nlinarith [hub, hden, sq_nonneg u]
    linarith [h1]
  have hsumm : Summable (fun k : ℕ => 1 / (3 * (((k + 1 : ℕ) : ℝ) ^ 2))) := by
    have hbase : Summable (fun k : ℕ => 1 / ((((k + 1 : ℕ) : ℝ) ^ 2))) := by
      have h1 : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ 2)) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num)
      exact (summable_nat_add_iff 1).mpr h1
    have heq : (fun k : ℕ => 1 / (3 * (((k + 1 : ℕ) : ℝ) ^ 2)))
        = (fun k : ℕ => (1 / 3 : ℝ) * (1 / ((((k + 1 : ℕ) : ℝ) ^ 2)))) := by
      funext k
      rw [← one_div_mul_one_div]
    rw [heq]
    exact hbase.mul_left (1 / 3)
  exact Summable.of_norm_bounded hsumm hbound

/-- Doubling tends to infinity. -/
private lemma catTwoMul_tendsto :
    Filter.Tendsto (fun m : ℕ => 2 * m) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  exact ⟨b, fun m hm => by omega⟩

/-- Finite integrands vanish at zero. -/
private lemma catFint_zero (N : ℕ) : catFint N 0 = 0 := by
  unfold catFint
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
    mul_zero, Finset.sum_const_zero]

/-- Infinite alternating sum equals the cosecant limit. -/
private lemma catTsum_eq_flim (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) :
    (∑' k : ℕ, (-1 : ℝ) ^ k * (u ^ 2 / (4 * ((((k + 1 : ℕ)) : ℝ) ^ 2) - u ^ 2)))
      = catFlim u := by
  have hu0' : 0 ≤ u := le_of_lt hu0
  have hne_u : u ≠ 0 := ne_of_gt hu0
  have hub : u ^ 2 ≤ 1 := by
    have habs : |u| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    calc u ^ 2 = |u| ^ 2 := by rw [sq_abs]
      _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ = 1 := one_pow 2
  have hsin : 0 < Real.sin (Real.pi * (u / 2)) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · have hpi : 0 < Real.pi := Real.pi_pos
      have h2 : (0 : ℝ) < u / 2 := by linarith
      exact mul_pos hpi h2
    · have hpi : 0 < Real.pi := Real.pi_pos
      have h2 : u / 2 < 1 := by linarith
      calc Real.pi * (u / 2) < Real.pi * 1 := by
            apply mul_lt_mul_of_pos_left h2 hpi
        _ = Real.pi := mul_one _
  have hsin_ne : Real.sin (Real.pi * (u / 2)) ≠ 0 := ne_of_gt hsin
  have hf : Summable (fun k : ℕ =>
      (-1 : ℝ) ^ k * (u ^ 2 / (4 * ((((k + 1 : ℕ)) : ℝ) ^ 2) - u ^ 2))) :=
    catFint_summable u hu0' hu1
  have hc : u ^ 2 / 4 ≠ 0 := by positivity
  have hfg : (fun k : ℕ => (-1 : ℝ) ^ k * (u ^ 2 /
      (4 * ((((k + 1 : ℕ)) : ℝ) ^ 2) - u ^ 2)))
      = (fun k : ℕ => (u ^ 2 / 4) *
        (((-1 : ℝ) ^ k / (((((k + 1 : ℕ)) : ℝ) ^ 2 - (u / 2) ^ 2))))) := by
    funext k
    set A : ℝ := ((((k + 1 : ℕ)) : ℝ) ^ 2) with hA
    have hm : (1 : ℝ) ≤ A := by
      rw [hA]
      have h1 : (1 : ℝ) ≤ ((((k + 1 : ℕ)) : ℝ)) := by
        have : (1 : ℕ) ≤ k + 1 := Nat.le_add_left 1 k
        exact_mod_cast this
      calc (1 : ℝ) = 1 ^ 2 := by norm_num
        _ ≤ ((((k + 1 : ℕ)) : ℝ) ^ 2) := pow_le_pow_left₀ (by norm_num) h1 2
    have hpos : (0 : ℝ) < 4 * A - u ^ 2 := by rw [hA] at hm ⊢; linarith
    have hpos2 : (0 : ℝ) < A - (u / 2) ^ 2 := by
      have : A - (u / 2) ^ 2 = (4 * A - u ^ 2) / 4 := by ring
      rw [this]
      linarith
    have n1 : 4 * A - u ^ 2 ≠ 0 := ne_of_gt hpos
    have n2 : A - (u / 2) ^ 2 ≠ 0 := ne_of_gt hpos2
    have hX : u ^ 2 / (4 * A - u ^ 2) = (u ^ 2 / 4) / (A - (u / 2) ^ 2) := by
      rw [div_eq_div_iff n1 n2]
      ring
    calc (-1 : ℝ) ^ k * (u ^ 2 / (4 * A - u ^ 2))
        = (-1 : ℝ) ^ k * ((u ^ 2 / 4) / (A - (u / 2) ^ 2)) := by rw [hX]
      _ = (u ^ 2 / 4) * ((-1 : ℝ) ^ k / (A - (u / 2) ^ 2)) := by ring
  have hg : Summable (fun k : ℕ =>
      (-1 : ℝ) ^ k / (((((k + 1 : ℕ)) : ℝ) ^ 2 - (u / 2) ^ 2))) := by
    have hmul := hf.mul_left (4 / u ^ 2)
    have heq : (fun k : ℕ => (4 / u ^ 2) * ((-1 : ℝ) ^ k *
        (u ^ 2 / (4 * ((((k + 1 : ℕ)) : ℝ) ^ 2) - u ^ 2))))
        = (fun k : ℕ =>
          (-1 : ℝ) ^ k / (((((k + 1 : ℕ)) : ℝ) ^ 2 - (u / 2) ^ 2))) := by
      funext k
      set A : ℝ := ((((k + 1 : ℕ)) : ℝ) ^ 2) with hA
      have hm : (1 : ℝ) ≤ A := by
        rw [hA]
        have h1 : (1 : ℝ) ≤ ((((k + 1 : ℕ)) : ℝ)) := by
          have : (1 : ℕ) ≤ k + 1 := Nat.le_add_left 1 k
          exact_mod_cast this
        calc (1 : ℝ) = 1 ^ 2 := by norm_num
          _ ≤ ((((k + 1 : ℕ)) : ℝ) ^ 2) := pow_le_pow_left₀ (by norm_num) h1 2
      have hpos : (0 : ℝ) < 4 * A - u ^ 2 := by rw [hA] at hm ⊢; linarith
      have hpos2 : (0 : ℝ) < A - (u / 2) ^ 2 := by
        have : A - (u / 2) ^ 2 = (4 * A - u ^ 2) / 4 := by ring
        rw [this]
        linarith
      have n1 : 4 * A - u ^ 2 ≠ 0 := ne_of_gt hpos
      have n2 : A - (u / 2) ^ 2 ≠ 0 := ne_of_gt hpos2
      have hu2 : u ^ 2 ≠ 0 := pow_ne_zero 2 hne_u
      have hX : u ^ 2 / (4 * A - u ^ 2) = (u ^ 2 / 4) / (A - (u / 2) ^ 2) := by
        rw [div_eq_div_iff n1 n2]
        ring
      have hcancel : (4 / u ^ 2) * (u ^ 2 / 4) = 1 := by
        field_simp
      calc (4 / u ^ 2) * ((-1 : ℝ) ^ k * (u ^ 2 / (4 * A - u ^ 2)))
          = (-1 : ℝ) ^ k * ((4 / u ^ 2) * (u ^ 2 / (4 * A - u ^ 2))) := by ring
        _ = (-1 : ℝ) ^ k * ((4 / u ^ 2) * ((u ^ 2 / 4) / (A - (u / 2) ^ 2))) := by rw [hX]
        _ = (-1 : ℝ) ^ k * (((4 / u ^ 2) * (u ^ 2 / 4)) / (A - (u / 2) ^ 2)) := by ring
        _ = (-1 : ℝ) ^ k / (A - (u / 2) ^ 2) := by rw [hcancel, mul_one_div]
    rw [heq] at hmul
    exact hmul
  have htsum := catCsc_real_tsum u hu0 hu1
  have hmul : (∑' k : ℕ, (-1 : ℝ) ^ k * (u ^ 2 / (4 * ((((k + 1 : ℕ)) : ℝ) ^ 2) - u ^ 2)))
      = (u ^ 2 / 4) * ∑' k : ℕ, ((-1 : ℝ) ^ k / (((((k + 1 : ℕ)) : ℝ) ^ 2 - (u / 2) ^ 2))) := by
    rw [hfg, tsum_mul_left]
  rw [hmul, htsum]
  have hflim : catFlim u = Real.pi * u / (4 * Real.sin (Real.pi * u / 2)) - 1 / 2 := by
    unfold catFlim
    simp only [hne_u, ite_false]
  rw [hflim]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hu2 : (u / 2 : ℝ) ≠ 0 := by linarith
  have h2u : (2 : ℝ) * (u / 2) ≠ 0 := by linarith
  field_simp
  ring

/-- Finite integrands converge pointwise to the cosecant limit. -/
private lemma catFint_tendsto (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Filter.Tendsto (fun m : ℕ => catFint (2 * m) u) Filter.atTop
      (nhds (catFlim u)) := by
  by_cases hu : u = 0
  · subst hu
    simp only [catFint_zero]
    have hflim : catFlim 0 = 0 := by
      unfold catFlim
      simp
    rw [hflim]
    exact tendsto_const_nhds
  · have hu0' : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
    have hf := catFint_summable u hu0 hu1
    have hlim : Filter.Tendsto
        (fun N : ℕ => ∑ k ∈ Finset.range N,
          (-1 : ℝ) ^ k * (u ^ 2 / (4 * ((((k + 1 : ℕ)) : ℝ) ^ 2) - u ^ 2)))
        Filter.atTop
        (nhds (∑' k : ℕ, (-1 : ℝ) ^ k *
          (u ^ 2 / (4 * ((((k + 1 : ℕ)) : ℝ) ^ 2) - u ^ 2)))) :=
      hf.hasSum.tendsto_sum_nat
    have hcomp := hlim.comp catTwoMul_tendsto
    rw [catTsum_eq_flim u hu0' hu1] at hcomp
    refine Filter.Tendsto.congr (fun m => ?_) hcomp
    rw [catFint_eq_range]
    rfl

private lemma ccp_catFint_integral_tendsto :
    Filter.Tendsto (fun m : ℕ => ∫ u in (0 : ℝ)..1, catFint (2 * m) u)
      Filter.atTop (nhds (∫ u in (0 : ℝ)..1, catFlim u)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 1)
  · refine Filter.Eventually.of_forall fun m => ?_
    have hmeas : Measurable (fun u : ℝ => catFint (2 * m) u) := by
      unfold catFint
      fun_prop
    exact hmeas.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun m => ?_
    filter_upwards [] with u
    intro hu
    rw [Set.uIoc_of_le (by norm_num), Set.mem_Ioc] at hu
    exact ccp_catFint_norm_le_one (2 * m) u hu.1.le hu.2
  · exact intervalIntegrable_const
  · filter_upwards [] with u
    intro hu
    rw [Set.uIoc_of_le (by norm_num), Set.mem_Ioc] at hu
    exact catFint_tendsto u hu.1.le hu.2

private noncomputable def ccp_atan_term (t : ℝ) (n : ℕ) : ℝ :=
  t ^ (2 * n) / (2 * (n : ℝ) + 1)

private noncomputable def ccp_atan_partial (N : ℕ) (t : ℝ) : ℝ :=
  ccp_alt_sum (ccp_atan_term t) N

private lemma ccp_atan_term_nonneg (t : ℝ) (n : ℕ) (ht : 0 ≤ t) :
    0 ≤ ccp_atan_term t n := by
  unfold ccp_atan_term
  positivity

private lemma ccp_atan_term_antitone (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Antitone (ccp_atan_term t) := by
  intro k l hkl
  have hexp : 2 * k ≤ 2 * l := by omega
  have hpow : t ^ (2 * l) ≤ t ^ (2 * k) :=
    pow_le_pow_of_le_one ht0 ht1 hexp
  have hden : (2 : ℝ) * (k : ℝ) + 1 ≤ 2 * (l : ℝ) + 1 := by
    exact_mod_cast (show 2 * k + 1 ≤ 2 * l + 1 by omega)
  unfold ccp_atan_term
  calc
    t ^ (2 * l) / (2 * (l : ℝ) + 1) ≤
        t ^ (2 * l) / (2 * (k : ℝ) + 1) :=
      div_le_div_of_nonneg_left (pow_nonneg ht0 _) (by positivity) hden
    _ ≤ t ^ (2 * k) / (2 * (k : ℝ) + 1) :=
      div_le_div_of_nonneg_right hpow (by positivity)

private lemma ccp_atan_partial_norm_le_one (N : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖ccp_atan_partial N t‖ ≤ 1 := by
  have hbounds := ccp_alt_sum_bounds (ccp_atan_term t)
    (fun n => ccp_atan_term_nonneg t n ht0) (ccp_atan_term_antitone t ht0 ht1) N
  rw [ccp_atan_partial, Real.norm_eq_abs, abs_of_nonneg hbounds.1]
  simpa [ccp_atan_term] using hbounds.2

private lemma ccp_atan_partial_tendsto (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    Filter.Tendsto (fun N : ℕ => ccp_atan_partial N t) Filter.atTop
      (nhds (Real.arctan t / t)) := by
  have hnorm : ‖t‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos ht0]
    exact ht1
  have hsum := (Real.hasSum_arctan hnorm).div_const t
  have hterm : (fun n : ℕ =>
      ((-1 : ℝ) ^ n * t ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)) / t) =
      (fun n : ℕ => (-1 : ℝ) ^ n * ccp_atan_term t n) := by
    funext n
    unfold ccp_atan_term
    rw [pow_succ]
    field_simp
    push_cast
    rfl
  rw [hterm] at hsum
  simpa [ccp_atan_partial, ccp_alt_sum] using hsum.tendsto_sum_nat

private lemma ccp_atan_integral_tendsto :
    Filter.Tendsto (fun N : ℕ => ∫ t in (0 : ℝ)..1, ccp_atan_partial N t)
      Filter.atTop (nhds (∫ t in (0 : ℝ)..1, Real.arctan t / t)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 1)
  · refine Filter.Eventually.of_forall fun N => ?_
    have hmeas : Measurable (fun t : ℝ => ccp_atan_partial N t) := by
      unfold ccp_atan_partial ccp_alt_sum ccp_atan_term
      fun_prop
    exact hmeas.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun N => ?_
    filter_upwards [] with t
    intro ht
    rw [Set.uIoc_of_le (by norm_num), Set.mem_Ioc] at ht
    exact ccp_atan_partial_norm_le_one N t ht.1.le ht.2
  · exact intervalIntegrable_const
  · filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (1 : ℝ)] with t ht1
    intro ht
    rw [Set.uIoc_of_le (by norm_num), Set.mem_Ioc] at ht
    exact ccp_atan_partial_tendsto t ht.1 (lt_of_le_of_ne ht.2 ht1)

private lemma ccp_atan_term_integral (n : ℕ) :
    (∫ t in (0 : ℝ)..1, (-1 : ℝ) ^ n * ccp_atan_term t n) =
      (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2 := by
  unfold ccp_atan_term
  have heq : (fun t : ℝ => (-1 : ℝ) ^ n * (t ^ (2 * n) / (2 * (n : ℝ) + 1))) =
      (fun t : ℝ => ((-1 : ℝ) ^ n * t ^ (2 * n)) / (2 * (n : ℝ) + 1)) := by
    funext t
    ring
  rw [heq, intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
    integral_pow]
  norm_num
  field_simp

private lemma ccp_atan_partial_integral (N : ℕ) :
    (∫ t in (0 : ℝ)..1, ccp_atan_partial N t) =
      ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2 := by
  unfold ccp_atan_partial ccp_alt_sum
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n hn
    exact ccp_atan_term_integral n
  · intro n hn
    have hcont : Continuous (fun t : ℝ => (-1 : ℝ) ^ n * ccp_atan_term t n) := by
      unfold ccp_atan_term
      fun_prop
    exact hcont.intervalIntegrable 0 1

private lemma ccp_atan_integral_eq (G : ℝ)
    (hG : HasSum (fun n : ℕ => (-1 : ℝ) ^ n / ((2 * (n : ℝ) + 1) ^ 2)) G) :
    (∫ t in (0 : ℝ)..1, Real.arctan t / t) = G := by
  have hint : Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2)
      Filter.atTop (nhds (∫ t in (0 : ℝ)..1, Real.arctan t / t)) := by
    simpa only [ccp_atan_partial_integral] using ccp_atan_integral_tendsto
  exact tendsto_nhds_unique hint hG.tendsto_sum_nat

private lemma ccp_sinc_pos (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ Real.pi / 2) :
    0 < Real.sinc x := by
  by_cases hx : x = 0
  · simp [hx]
  · have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
    have hxpi : x < Real.pi := by linarith [Real.pi_pos]
    rw [Real.sinc_of_ne_zero hx]
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi hxpos hxpi) hxpos

private lemma ccp_continuousOn_inv_sinc :
    ContinuousOn (fun x : ℝ => (Real.sinc x)⁻¹) (Set.Icc 0 (Real.pi / 2)) := by
  apply Real.continuous_sinc.continuousOn.inv₀
  intro x hx
  exact (ccp_sinc_pos x hx.1 hx.2).ne'

private lemma ccp_catFlim_eq_inv_sinc (u : ℝ) :
    catFlim u = (1 / 2) * (Real.sinc (Real.pi * u / 2))⁻¹ - 1 / 2 := by
  by_cases hu : u = 0
  · subst u
    simp [catFlim]
  · have hx : Real.pi * u / 2 ≠ 0 :=
      div_ne_zero (mul_ne_zero Real.pi_ne_zero hu) (by norm_num)
    unfold catFlim
    simp only [hu, ite_false]
    rw [Real.sinc_of_ne_zero hx, inv_div]
    ring

private lemma ccp_inv_sinc_integral_scale :
    (∫ u in (0 : ℝ)..1, (Real.sinc (Real.pi * u / 2))⁻¹) =
      (2 / Real.pi) * ∫ x in (0 : ℝ)..Real.pi / 2, (Real.sinc x)⁻¹ := by
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun v : ℝ => Real.pi * v / 2) (Real.pi / 2) u := by
    intro u hu
    simpa only [div_eq_mul_inv, id_eq, one_mul, mul_assoc, mul_comm] using
      (hasDerivAt_id u).const_mul (Real.pi / 2)
  have hcont : ContinuousOn (fun _ : ℝ => Real.pi / 2) (Set.uIcc (0 : ℝ) 1) :=
    continuousOn_const
  have hg : ContinuousOn (fun x : ℝ => (Real.sinc x)⁻¹)
      ((fun u : ℝ => Real.pi * u / 2) '' Set.uIcc (0 : ℝ) 1) := by
    apply ccp_continuousOn_inv_sinc.mono
    rintro x ⟨u, hu, rfl⟩
    rw [Set.uIcc_of_le (by norm_num), Set.mem_Icc] at hu
    constructor <;> nlinarith [Real.pi_pos]
  have hsubst := intervalIntegral.integral_comp_mul_deriv'
    (a := (0 : ℝ)) (b := 1) (f := fun u : ℝ => Real.pi * u / 2)
    (f' := fun _ : ℝ => Real.pi / 2) (g := fun x : ℝ => (Real.sinc x)⁻¹)
    hderiv hcont hg
  have hsubst' :
      (∫ u in (0 : ℝ)..1, (Real.sinc (Real.pi * u / 2))⁻¹ * (Real.pi / 2)) =
        ∫ x in (0 : ℝ)..Real.pi / 2, (Real.sinc x)⁻¹ := by
    simpa [Function.comp_apply] using hsubst
  rw [intervalIntegral.integral_mul_const] at hsubst'
  calc
    (∫ u in (0 : ℝ)..1, (Real.sinc (Real.pi * u / 2))⁻¹) =
        (2 / Real.pi) *
          ((∫ u in (0 : ℝ)..1, (Real.sinc (Real.pi * u / 2))⁻¹) *
            (Real.pi / 2)) := by
      field_simp
    _ = (2 / Real.pi) * ∫ x in (0 : ℝ)..Real.pi / 2, (Real.sinc x)⁻¹ := by
      rw [hsubst']

private lemma ccp_inv_sinc_arctan_mul (t : ℝ) (ht : t ≠ 0) :
    (Real.sinc (2 * Real.arctan t))⁻¹ * (2 / (1 + t ^ 2)) =
      2 * (Real.arctan t / t) := by
  have hatan : Real.arctan t ≠ 0 := Real.arctan_eq_zero_iff.not.mpr ht
  have htwoatan : 2 * Real.arctan t ≠ 0 := mul_ne_zero (by norm_num) hatan
  have hsqrt : Real.sqrt (1 + t ^ 2) ≠ 0 := by positivity
  have hsquare : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 :=
    Real.sq_sqrt (by positivity)
  rw [Real.sinc_of_ne_zero htwoatan, inv_div, Real.sin_two_mul,
    Real.sin_arctan, Real.cos_arctan]
  field_simp
  nlinarith

private lemma ccp_inv_sinc_integral_arctan :
    (∫ x in (0 : ℝ)..Real.pi / 2, (Real.sinc x)⁻¹) =
      2 * ∫ t in (0 : ℝ)..1, Real.arctan t / t := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => 2 * Real.arctan s) (2 / (1 + t ^ 2)) t := by
    intro t ht
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using
      (Real.hasDerivAt_arctan t).const_mul 2
  have hcont : ContinuousOn (fun t : ℝ => 2 / (1 + t ^ 2))
      (Set.uIcc (0 : ℝ) 1) := by
    apply Continuous.continuousOn
    apply Continuous.div continuous_const
    · fun_prop
    · intro t
      positivity
  have hg : ContinuousOn (fun x : ℝ => (Real.sinc x)⁻¹)
      ((fun t : ℝ => 2 * Real.arctan t) '' Set.uIcc (0 : ℝ) 1) := by
    apply ccp_continuousOn_inv_sinc.mono
    rintro x ⟨t, ht, rfl⟩
    rw [Set.uIcc_of_le (by norm_num), Set.mem_Icc] at ht
    have hatan0 : 0 ≤ Real.arctan t := Real.arctan_nonneg.mpr ht.1
    have hatan1 : Real.arctan t ≤ Real.pi / 4 := by
      rw [← Real.arctan_one]
      exact Real.arctan_le_arctan_iff.mpr ht.2
    constructor <;> linarith
  have hsubst := intervalIntegral.integral_comp_mul_deriv'
    (a := (0 : ℝ)) (b := 1) (f := fun t : ℝ => 2 * Real.arctan t)
    (f' := fun t : ℝ => 2 / (1 + t ^ 2)) (g := fun x : ℝ => (Real.sinc x)⁻¹)
    hderiv hcont hg
  have hsubst' :
      (∫ t in (0 : ℝ)..1,
        (Real.sinc (2 * Real.arctan t))⁻¹ * (2 / (1 + t ^ 2))) =
        ∫ x in (0 : ℝ)..Real.pi / 2, (Real.sinc x)⁻¹ := by
    rw [Real.arctan_one] at hsubst
    have hend : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
    rw [hend] at hsubst
    simpa [Function.comp_apply] using hsubst
  have hcongr :
      (∫ t in (0 : ℝ)..1,
        (Real.sinc (2 * Real.arctan t))⁻¹ * (2 / (1 + t ^ 2))) =
        ∫ t in (0 : ℝ)..1, 2 * (Real.arctan t / t) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (0 : ℝ)] with t ht
    intro hmem
    exact ccp_inv_sinc_arctan_mul t ht
  calc
    (∫ x in (0 : ℝ)..Real.pi / 2, (Real.sinc x)⁻¹) =
        ∫ t in (0 : ℝ)..1,
          (Real.sinc (2 * Real.arctan t))⁻¹ * (2 / (1 + t ^ 2)) := hsubst'.symm
    _ = ∫ t in (0 : ℝ)..1, 2 * (Real.arctan t / t) := hcongr
    _ = 2 * ∫ t in (0 : ℝ)..1, Real.arctan t / t := by
      rw [intervalIntegral.integral_const_mul]

private lemma ccp_catFlim_integral_eq_inv_sinc :
    (∫ u in (0 : ℝ)..1, catFlim u) =
      (1 / 2) * (∫ u in (0 : ℝ)..1, (Real.sinc (Real.pi * u / 2))⁻¹) - 1 / 2 := by
  have hcont : ContinuousOn (fun u : ℝ => (Real.sinc (Real.pi * u / 2))⁻¹)
      (Set.Icc (0 : ℝ) 1) := by
    have hsinc : Continuous (fun u : ℝ => Real.sinc (Real.pi * u / 2)) := by
      fun_prop
    apply hsinc.continuousOn.inv₀
    intro u hu
    apply (ccp_sinc_pos (Real.pi * u / 2) ?_ ?_).ne'
    · have hpi : 0 < Real.pi := Real.pi_pos
      exact div_nonneg (mul_nonneg hpi.le hu.1) (by norm_num)
    · have hpi : 0 < Real.pi := Real.pi_pos
      nlinarith [hu.2]
  have hint : IntervalIntegrable (fun u : ℝ => (Real.sinc (Real.pi * u / 2))⁻¹)
      MeasureTheory.volume 0 1 := hcont.intervalIntegrable_of_Icc (by norm_num)
  calc
    (∫ u in (0 : ℝ)..1, catFlim u) =
        ∫ u in (0 : ℝ)..1, (1 / 2) * (Real.sinc (Real.pi * u / 2))⁻¹ - 1 / 2 := by
      apply intervalIntegral.integral_congr
      intro u hu
      exact ccp_catFlim_eq_inv_sinc u
    _ = (∫ u in (0 : ℝ)..1, (1 / 2) * (Real.sinc (Real.pi * u / 2))⁻¹) -
        ∫ _ in (0 : ℝ)..1, (1 / 2 : ℝ) := by
      rw [intervalIntegral.integral_sub (hint.const_mul (1 / 2)) intervalIntegrable_const]
    _ = (1 / 2) * (∫ u in (0 : ℝ)..1, (Real.sinc (Real.pi * u / 2))⁻¹) -
        1 / 2 := by
      rw [intervalIntegral.integral_const_mul]
      norm_num

private lemma ccp_catFlim_integral_eq (G : ℝ)
    (hG : HasSum (fun n : ℕ => (-1 : ℝ) ^ n / ((2 * (n : ℝ) + 1) ^ 2)) G) :
    (∫ u in (0 : ℝ)..1, catFlim u) = 2 * G / Real.pi - 1 / 2 := by
  rw [ccp_catFlim_integral_eq_inv_sinc, ccp_inv_sinc_integral_scale,
    ccp_inv_sinc_integral_arctan, ccp_atan_integral_eq G hG]
  field_simp

/--
**Infinite products for exponentials of Catalan's constant.** Let $G$ be the sum of the series
$\sum_{n \ge 0} (-1)^n / (2n+1)^2$ (Catalan's constant). Then, as $m \to \infty$,

$$
\prod_{n=1}^{2m} \left(1 - \frac{2}{2n+1}\right)^{n(-1)^n} \to e^{2G/\pi - 1/2},
$$

$$
\prod_{n=1}^{2m+1} \left(1 - \frac{2}{2n+1}\right)^{n(-1)^n} \to e^{2G/\pi + 1/2},
$$

and

$$
\left(\frac{\prod_{k=0}^{m-1} (4k+3)^{4k+3}}{\prod_{k=0}^{m-1} (4k+1)^{4k+1}}\right)^2
\frac{(4m+3)^{2m+1}}{(4m+1)^{6m+1}} \to e^{4G/\pi}.
$$

The products $\prod_{k=0}^{m-1} (4k+3)^{4k+3}$ and $\prod_{k=0}^{m-1} (4k+1)^{4k+1}$ are the
source's $3^3 \cdot 7^7 \cdots (4m-1)^{4m-1}$ and $1^1 \cdot 5^5 \cdots (4m-3)^{4m-3}$.

Proof: Following Kachi and Tzermias, Proposition (catalan), dominated convergence reduces the
product limit to the cosecant integral. The substitutions $x = \pi u/2$ and $x = 2 \arctan t$,
followed by the arctangent power series, evaluate it in terms of $G$.

Source: Yasuyuki Kachi and Pavlos Tzermias, "Infinite Products Involving
ζ(3) and Catalan's Constant," Journal of Integer Sequences 15 (2012),
Article 12.9.4, Proposition (label catalan), equations (labels catalani,
catalanii, catalaniii), lines 147–165,
https://cs.uwaterloo.ca/journals/JIS/VOL15/Tzermias/tzermias2.tex
-/
public theorem catalan_constant_product_formulas
    (G : ℝ) (hG : HasSum (fun n : ℕ => (-1 : ℝ) ^ n / ((2 * (n : ℝ) + 1) ^ 2)) G) :
    (Filter.Tendsto (fun m : ℕ => ∏ n ∈ Finset.Icc 1 (2 * m),
        (1 - 2 / (2 * (n : ℝ) + 1)) ^ ((n : ℤ) * (-1 : ℤ) ^ n))
      Filter.atTop (nhds (Real.exp (2 * G / Real.pi - 1 / 2)))) ∧
    (Filter.Tendsto (fun m : ℕ => ∏ n ∈ Finset.Icc 1 (2 * m + 1),
        (1 - 2 / (2 * (n : ℝ) + 1)) ^ ((n : ℤ) * (-1 : ℤ) ^ n))
      Filter.atTop (nhds (Real.exp (2 * G / Real.pi + 1 / 2)))) ∧
    Filter.Tendsto (fun m : ℕ =>
        ((∏ k ∈ Finset.range m, (4 * (k : ℝ) + 3) ^ (4 * k + 3)) /
          (∏ k ∈ Finset.range m, (4 * (k : ℝ) + 1) ^ (4 * k + 1))) ^ 2 *
        (4 * (m : ℝ) + 3) ^ (2 * m + 1) / (4 * (m : ℝ) + 1) ^ (6 * m + 1))
      Filter.atTop (nhds (Real.exp (4 * G / Real.pi))) := by
  have hlog : Filter.Tendsto (fun m : ℕ => Real.log (catP m))
      Filter.atTop (nhds (2 * G / Real.pi - 1 / 2)) := by
    have hint := ccp_catFint_integral_tendsto
    rw [ccp_catFlim_integral_eq G hG] at hint
    refine Filter.Tendsto.congr (fun m => ?_) hint
    exact (catP_log_eq_integral m).symm
  have hP : Filter.Tendsto catP Filter.atTop
      (nhds (Real.exp (2 * G / Real.pi - 1 / 2))) := catP_of_log G hlog
  refine ⟨?_, ?_, ?_⟩
  · exact hP
  · exact catQ_of_catP G hP
  · exact catR_of_catPQ G hP (catQ_of_catP G hP)

end MetaMathlibExt
end
