/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexAntiferroelectricSeries

open Filter Topology
open scoped BigOperators

namespace StatMech.FrontierD

noncomputable section



def sixVertexDualGapPowerTerm (x : Real) (n : Nat) : Real :=
  4 * Real.log
    ((1 + x ^ (2 * n + 1)) / (1 - x ^ (2 * n + 1)))


def sixVertexDualGapPowerSeries (x : Real) : Real :=
  ∑' n : Nat, sixVertexDualGapPowerTerm x n

theorem two_mul_le_log_one_add_div_one_sub
    {t : Real} (ht0 : 0 <= t) (ht1 : t < 1) :
    2 * t <= Real.log ((1 + t) / (1 - t)) := by
  let y := 2 * t / (1 - t)
  have hden : 0 < 1 - t := sub_pos.mpr ht1
  have hy0 : 0 <= y := div_nonneg (mul_nonneg (by norm_num) ht0) hden.le
  have hratio : (1 + t) / (1 - t) = 1 + y := by
    dsimp [y]
    field_simp
    ring
  rw [hratio]
  calc
    2 * t = 2 * y / (y + 2) := by
      dsimp [y]
      field_simp
      ring
    _ <= Real.log (1 + y) := Real.le_log_one_add_of_nonneg hy0

theorem log_one_add_div_one_sub_le
    {t : Real} (ht0 : 0 <= t) (ht1 : t < 1) :
    Real.log ((1 + t) / (1 - t)) <= 2 * t / (1 - t) := by
  have hden : 0 < 1 - t := sub_pos.mpr ht1
  have hratio : 0 < (1 + t) / (1 - t) :=
    div_pos (by linarith) hden
  calc
    Real.log ((1 + t) / (1 - t)) <=
        (1 + t) / (1 - t) - 1 :=
      Real.log_le_sub_one_of_pos hratio
    _ = 2 * t / (1 - t) := by
      field_simp
      ring

theorem sixVertexDualGapPowerTerm_nonneg
    {x : Real} (hx0 : 0 <= x) (hx1 : x < 1) (n : Nat) :
    0 <= sixVertexDualGapPowerTerm x n := by
  unfold sixVertexDualGapPowerTerm
  have ht0 : 0 <= x ^ (2 * n + 1) := pow_nonneg hx0 _
  have ht1 : x ^ (2 * n + 1) < 1 := by
    exact pow_lt_one₀ hx0 hx1 (by omega)
  nlinarith [two_mul_le_log_one_add_div_one_sub ht0 ht1]

theorem sixVertexDualGapPowerTerm_le_geometric
    {x : Real} (hx0 : 0 <= x) (hx1 : x < 1) (n : Nat) :
    sixVertexDualGapPowerTerm x n <=
      (8 / (1 - x)) * x ^ (n + 1) := by
  let t := x ^ (2 * n + 1)
  have hxle : x <= 1 := hx1.le
  have ht0 : 0 <= t := pow_nonneg hx0 _
  have ht_le_x : t <= x := by
    dsimp [t]
    simpa using pow_le_pow_of_le_one hx0 hxle (show 1 <= 2 * n + 1 by omega)
  have ht_le_pow : t <= x ^ (n + 1) := by
    dsimp [t]
    exact pow_le_pow_of_le_one hx0 hxle (by omega)
  have hdenx : 0 < 1 - x := sub_pos.mpr hx1
  have hdent : 0 < 1 - t := sub_pos.mpr (lt_of_le_of_lt ht_le_x hx1)
  have hlog := log_one_add_div_one_sub_le ht0
    (lt_of_le_of_lt ht_le_x hx1)
  unfold sixVertexDualGapPowerTerm
  calc
    4 * Real.log ((1 + t) / (1 - t)) <=
        4 * (2 * t / (1 - t)) := by gcongr
    _ <= 8 * t / (1 - x) := by
      have hden : 1 - x <= 1 - t := by linarith
      rw [show 4 * (2 * t / (1 - t)) = 8 * t / (1 - t) by ring]
      exact div_le_div_of_nonneg_left
        (mul_nonneg (by norm_num) ht0) hdenx hden
    _ <= (8 / (1 - x)) * x ^ (n + 1) := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right
        (by nlinarith [ht_le_pow]) hdenx.le

theorem summable_sixVertexDualGapPowerTerm
    {x : Real} (hx0 : 0 <= x) (hx1 : x < 1) :
    Summable (sixVertexDualGapPowerTerm x) := by
  have hgeom : Summable (fun n : Nat =>
      (8 / (1 - x)) * x ^ (n + 1)) :=
    ((summable_geometric_of_lt_one hx0 hx1).comp_injective
      Nat.succ_injective).mul_left _
  exact Summable.of_nonneg_of_le
    (sixVertexDualGapPowerTerm_nonneg hx0 hx1)
    (sixVertexDualGapPowerTerm_le_geometric hx0 hx1) hgeom

theorem tsum_geometric_nat_succ {x : Real} (hx0 : 0 <= x) (hx1 : x < 1) :
    (∑' n : Nat, x ^ (n + 1)) = x / (1 - x) := by
  have habs : |x| < 1 := by simpa [abs_of_nonneg hx0]
  calc
    (∑' n : Nat, x ^ (n + 1)) = ∑' n : Nat, x * x ^ n := by
      apply tsum_congr
      intro n
      rw [pow_succ']
    _ = x * ∑' n : Nat, x ^ n := tsum_mul_left
    _ = x * (1 - x)⁻¹ := by rw [tsum_geometric_of_norm_lt_one habs]
    _ = x / (1 - x) := by rw [div_eq_mul_inv]

theorem sixVertexDualGapPowerSeries_lower
    {x : Real} (hx0 : 0 <= x) (hx1 : x < 1) :
    8 * x <= sixVertexDualGapPowerSeries x := by
  have hsummable := summable_sixVertexDualGapPowerTerm hx0 hx1
  have hterm : 8 * x <= sixVertexDualGapPowerTerm x 0 := by
    unfold sixVertexDualGapPowerTerm
    simp only [Nat.reduceMul, zero_add, pow_one]
    nlinarith [two_mul_le_log_one_add_div_one_sub hx0 hx1]
  exact hterm.trans (hsummable.le_tsum 0 fun n hn =>
    sixVertexDualGapPowerTerm_nonneg hx0 hx1 n)

theorem sixVertexDualGapPowerSeries_upper
    {x : Real} (hx0 : 0 <= x) (hx1 : x < 1) :
    sixVertexDualGapPowerSeries x <= 8 * x / (1 - x) ^ 2 := by
  let upper : Nat -> Real := fun n => (8 / (1 - x)) * x ^ (n + 1)
  have hterm := summable_sixVertexDualGapPowerTerm hx0 hx1
  have hupper : Summable upper :=
    ((summable_geometric_of_lt_one hx0 hx1).comp_injective
      Nat.succ_injective).mul_left _
  calc
    sixVertexDualGapPowerSeries x <= ∑' n : Nat, upper n :=
      hterm.tsum_le_tsum
        (sixVertexDualGapPowerTerm_le_geometric hx0 hx1) hupper
    _ = (8 / (1 - x)) * ∑' n : Nat, x ^ (n + 1) := by
      exact tsum_mul_left
    _ = (8 / (1 - x)) * (x / (1 - x)) := by
      rw [tsum_geometric_nat_succ hx0 hx1]
    _ = 8 * x / (1 - x) ^ 2 := by
      field_simp [ne_of_gt (sub_pos.mpr hx1)]



theorem sixVertexDualGapPowerSeries_div_tendsto_one :
    Tendsto (fun x : Real => sixVertexDualGapPowerSeries x / (8 * x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hupper : Tendsto (fun x : Real => 1 / (1 - x) ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have hc : ContinuousAt (fun x : Real => 1 / (1 - x) ^ 2) 0 := by
      exact continuousAt_const.div
        ((continuousAt_const.sub continuousAt_id).pow 2) (by norm_num)
    simpa using hc.tendsto
  apply Filter.Tendsto.squeeze' tendsto_const_nhds hupper
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : Real) < 1 by norm_num)).filter_mono
        inf_le_left] with x hxpos hx1
    have hx0 : 0 <= x := hxpos.le
    have hden : 0 < 8 * x := mul_pos (by norm_num) hxpos
    rw [le_div_iff₀ hden]
    simpa using sixVertexDualGapPowerSeries_lower hx0 hx1
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : Real) < 1 by norm_num)).filter_mono
        inf_le_left] with x hxpos hx1
    have hx0 : 0 <= x := hxpos.le
    have hden : 0 < 8 * x := mul_pos (by norm_num) hxpos
    rw [div_le_iff₀ hden]
    have hu := sixVertexDualGapPowerSeries_upper hx0 hx1
    have hxden : 0 < (1 - x) ^ 2 := sq_pos_of_pos (sub_pos.mpr hx1)
    calc
      sixVertexDualGapPowerSeries x <= 8 * x / (1 - x) ^ 2 := hu
      _ = 1 / (1 - x) ^ 2 * (8 * x) := by ring


def sixVertexDualGapRate (lam : Real) : Real :=
  sixVertexDualGapPowerSeries (Real.exp (-(Real.pi ^ 2) / (2 * lam)))



theorem sixVertexDualGapRate_div_tendsto_one :
    Tendsto (fun lam : Real =>
      sixVertexDualGapRate lam /
        (8 * Real.exp (-(Real.pi ^ 2) / (2 * lam))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  apply sixVertexDualGapPowerSeries_div_tendsto_one.comp
  have hdiv : Tendsto (fun lam : Real => -(Real.pi ^ 2) / (2 * lam))
      (nhdsWithin 0 (Set.Ioi 0)) atBot := by
      rw [Filter.tendsto_atBot]
      intro b
      have hpi : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
      filter_upwards [Ioo_mem_nhdsGT
        (show 0 < Real.pi ^ 2 / (2 * (|b| + 1)) by positivity)] with lam hlam
      have hlam0 : 0 < lam := hlam.1
      have hlamUpper : lam < Real.pi ^ 2 / (2 * (|b| + 1)) := hlam.2
      have hb : -(|b| + 1) < b := by
        nlinarith [neg_abs_le b]
      have hcore : 2 * lam * (|b| + 1) < Real.pi ^ 2 := by
        rw [lt_div_iff₀ (show 0 < 2 * (|b| + 1) by positivity)] at hlamUpper
        nlinarith
      rw [div_le_iff₀ (show 0 < 2 * lam by positivity)]
      have hbmul : -(|b| + 1) * (2 * lam) < b * (2 * lam) :=
        mul_lt_mul_of_pos_right hb (by positivity)
      have hnegcore : -Real.pi ^ 2 < -(|b| + 1) * (2 * lam) := by
        nlinarith
      exact (hnegcore.trans hbmul).le
  rw [nhdsWithin, Filter.tendsto_inf]
  constructor
  · exact Real.tendsto_exp_atBot.comp hdiv
  · rw [Filter.tendsto_principal]
    filter_upwards with lam
    exact Real.exp_pos _

end

end StatMech.FrontierD
