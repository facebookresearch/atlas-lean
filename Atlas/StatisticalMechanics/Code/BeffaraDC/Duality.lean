/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































import Mathlib
import Code.Foundations.ConfigSpace
import Code.FK.RandomCluster
import Code.FK.Tilt
import Code.BeffaraDC.SelfDualValue

open scoped BigOperators

namespace StatMech

namespace BeffaraDC







noncomputable def edgeProductCount (p : ℝ) (m o : ℕ) : ℝ :=
  p ^ o * (1 - p) ^ (m - o)

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in



theorem dlt_edgeProduct_eq_count (p : ℝ) (ω : ConfigSpace (Sym2 V)) :
    StatMech.FK.edgeProduct G p ω
      = edgeProductCount p G.edgeFinset.card (StatMech.FK.openCount G ω) := by
  unfold StatMech.FK.edgeProduct edgeProductCount StatMech.FK.openCount
  rw [Finset.prod_ite (f := fun _ => p) (g := fun _ => (1 - p))]
  simp only [Finset.prod_const]
  congr 1
  
  have hcard :=
    Finset.card_filter_add_card_filter_not (s := G.edgeFinset) (fun e => ω e = true)
  congr 1
  omega





theorem dlt_edgeProductCount_yates {p : ℝ} (hp1 : p < 1) (m o : ℕ) (hom : o ≤ m) :
    edgeProductCount p m o = (1 - p) ^ m * (p / (1 - p)) ^ o := by
  unfold edgeProductCount
  have h1p : (0 : ℝ) < 1 - p := by linarith
  have hmo : (1 - p) ^ m = (1 - p) ^ (m - o) * (1 - p) ^ o := by
    rw [← pow_add, Nat.sub_add_cancel hom]
  rw [hmo, div_pow]; field_simp





theorem dlt_dual_ratio_rel {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    (p / (1 - p)) * (dualParam p q / (1 - dualParam p q)) = q := by
  have hden : 0 < (1 - p) * q + p := by nlinarith
  have h1md : 1 - dualParam p q = p / ((1 - p) * q + p) := by
    unfold dualParam; field_simp; ring
  rw [h1md]; unfold dualParam
  have hpne : p ≠ 0 := ne_of_gt hp
  have h1pne : (1 : ℝ) - p ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  field_simp













theorem dlt_edgeProduct_duality {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (m o : ℕ) (hom : o ≤ m) :
    edgeProductCount p m o * q ^ m
      = (p / (1 - dualParam p q)) ^ m * q ^ o
          * edgeProductCount (dualParam p q) m (m - o) := by
  have hden : 0 < (1 - p) * q + p := by nlinarith
  have hps_pos : 0 < dualParam p q := by unfold dualParam; positivity
  have hps_lt : dualParam p q < 1 := by unfold dualParam; rw [div_lt_one hden]; nlinarith
  have h1p : (0 : ℝ) < 1 - p := by linarith
  have h1ps : (0 : ℝ) < 1 - dualParam p q := by linarith
  rw [dlt_edgeProductCount_yates hp1 m o hom,
      dlt_edgeProductCount_yates hps_lt m (m - o) (Nat.sub_le m o)]
  set s := dualParam p q with hs
  set a := p / (1 - p) with ha
  set b := s / (1 - s) with hb
  have hab : a * b = q := dlt_dual_ratio_rel hp hp1 hq
  have hpa : (1 - p) * a = p := by rw [ha]; field_simp
  have hqm : q ^ m = (a * b) ^ m := by rw [hab]
  have hqo : q ^ o = (a * b) ^ o := by rw [hab]
  rw [hqm, hqo, mul_pow a b m, mul_pow a b o]
  have hcollapse : (p / (1 - s)) ^ m * (1 - s) ^ m = p ^ m := by
    rw [← mul_pow]; congr 1; field_simp
  rw [show (p / (1 - s)) ^ m * (a ^ o * b ^ o) * ((1 - s) ^ m * b ^ (m - o))
        = ((p / (1 - s)) ^ m * (1 - s) ^ m) * (a ^ o * (b ^ o * b ^ (m - o))) by ring,
      hcollapse,
      show b ^ o * b ^ (m - o) = b ^ m by rw [← pow_add, Nat.add_sub_cancel' hom]]
  rw [show ((1 : ℝ) - p) ^ m * a ^ o * (a ^ m * b ^ m)
        = ((1 - p) * a) ^ m * (a ^ o * b ^ m) by rw [mul_pow]; ring, hpa]





theorem dlt_edgeProduct_duality_selfdual {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q) (hsd : dualParam p q = p) (m o : ℕ) (hom : o ≤ m) :
    edgeProductCount p m o * q ^ m
      = (p / (1 - p)) ^ m * q ^ o * edgeProductCount p m (m - o) := by
  have := dlt_edgeProduct_duality hp hp1 hq m o hom
  rwa [hsd] at this



variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]











theorem dlt_rn_sandwich (w w' : Ω → ℝ) (q : ℝ) (hq : 1 ≤ q) (c : ℕ)
    (hw'pos : ∀ ω, 0 < w' ω) (hwpos : ∀ ω, 0 < w ω)
    (hlb : ∀ ω, q ^ (-(c : ℤ)) * w' ω ≤ w ω)
    (hub : ∀ ω, w ω ≤ q ^ (c : ℤ) * w' ω) (A : Finset Ω) :
    (∑ ω ∈ A, w ω) / (∑ ω, w ω) ≤ q ^ (2 * c) * ((∑ ω ∈ A, w' ω) / (∑ ω, w' ω)) := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq
  have hqc : (0 : ℝ) < q ^ c := by positivity
  have hSwpos : 0 < ∑ ω, w ω := Finset.sum_pos (fun ω _ => hwpos ω) Finset.univ_nonempty
  have hSw'pos : 0 < ∑ ω, w' ω := Finset.sum_pos (fun ω _ => hw'pos ω) Finset.univ_nonempty
  have hnum : ∑ ω ∈ A, w ω ≤ q ^ c * ∑ ω ∈ A, w' ω := by
    rw [Finset.mul_sum]; refine Finset.sum_le_sum (fun ω _ => ?_)
    have := hub ω; rwa [zpow_natCast] at this
  have hden : ∑ ω, w' ω ≤ q ^ c * ∑ ω, w ω := by
    rw [Finset.mul_sum]; refine Finset.sum_le_sum (fun ω _ => ?_)
    have hl := hlb ω; rw [zpow_neg, zpow_natCast] at hl
    have := mul_le_mul_of_nonneg_left hl hqc.le
    rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hqc), one_mul] at this
  have hdpos : 0 < (∑ ω, w' ω) / q ^ c := div_pos hSw'pos hqc
  have hAnn : 0 ≤ ∑ ω ∈ A, w' ω := Finset.sum_nonneg (fun ω _ => (hw'pos ω).le)
  have key : (∑ ω ∈ A, w ω) / (∑ ω, w ω)
      ≤ (q ^ c * ∑ ω ∈ A, w' ω) / ((∑ ω, w' ω) / q ^ c) := by
    refine div_le_div₀ (by positivity) hnum hdpos ?_
    rw [div_le_iff₀ hqc]; linarith [hden]
  refine key.trans (le_of_eq ?_)
  rw [pow_mul]; field_simp; ring








theorem dlt_dichotomy_lower_bound {x y Q : ℝ} (hsum : x + y = 1) (hQ : 0 ≤ Q)
    (hyx : y ≤ Q * x) : 1 / (1 + Q) ≤ x := by
  have h1Q : 0 < 1 + Q := by linarith
  rw [div_le_iff₀ h1Q]
  nlinarith [hsum, hyx]





theorem dlt_self_duality_estimate {connectProb dualConnectProb q : ℝ}
    (hdichotomy : connectProb + dualConnectProb = 1)
    (hRN : dualConnectProb ≤ q ^ 2 * connectProb) :
    1 / (1 + q ^ 2) ≤ connectProb :=
  dlt_dichotomy_lower_bound hdichotomy (by positivity) hRN





theorem dlt_square_crossing_estimate {horizCross vertDualCross c : ℝ} (hc : 0 ≤ c)
    (hdichotomy : horizCross + vertDualCross = 1)
    (hsym : vertDualCross ≤ c * horizCross) :
    1 / (1 + c) ≤ horizCross :=
  dlt_dichotomy_lower_bound hdichotomy hc hsym




theorem dlt_square_crossing_const_pos {c : ℝ} (hc : 0 ≤ c) : 0 < 1 / (1 + c) := by
  have h : (0 : ℝ) < 1 + c := by linarith
  exact div_pos one_pos h



theorem dlt_self_duality_const_pos (q : ℝ) : 0 < 1 / (1 + q ^ 2) := by
  have h : (0 : ℝ) < 1 + q ^ 2 := by positivity
  exact div_pos one_pos h

end BeffaraDC

end StatMech
