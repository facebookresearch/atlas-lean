/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































import Mathlib
import Code.Universality.HexBoundary
import Code.Universality.HexConnEndgame
import Code.Universality.HexBridgeRecon
import Code.Universality.HexSurgerySeams

namespace StatMech.Universality

open Filter Topology
open scoped Topology BigOperators










lemma hexZDiv_sqrt_gt_one : 1 < Real.sqrt (2 + Real.sqrt 2) := by
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  apply Real.sqrt_lt_sqrt (by norm_num)
  have : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith







lemma hexZDiv_chiSq_lt_one : hexChiE * hexChiE < 1 := by
  have h : hexChiE = 1 / Real.sqrt (2 + Real.sqrt 2) := rfl
  have hpos : 0 < Real.sqrt (2 + Real.sqrt 2) := hex_sqrt_pos
  rw [h, div_mul_div_comm, one_mul, div_lt_one (by positivity)]
  nlinarith [hexZDiv_sqrt_gt_one, hpos]












theorem hexZDiv_chi_bound_fails (g : ℕ) :
    ¬ (hexChiE ^ g ≤ hexChiE * hexChiE ^ (g + 1)) := by
  intro hle
  have hχpos : 0 < hexChiE := hexChiE_pos
  have hpos : 0 < hexChiE ^ g := by positivity
  
  have hrw : hexChiE * hexChiE ^ (g + 1) = (hexChiE * hexChiE) * hexChiE ^ g := by
    rw [pow_succ]; ring
  rw [hrw] at hle
  
  have : 1 ≤ hexChiE * hexChiE := by
    nlinarith [hle, hpos]
  linarith [hexZDiv_chiSq_lt_one]






















theorem hexZDiv_contour_limits (lam tau ups : ℕ → ℝ)
    (hbdry : ∀ h, hexBdryCl * lam h + hexBdryCt * tau h + ups h = 1)
    (hlamMono : Monotone lam) (hupsMono : Monotone ups)
    (hlamNN : ∀ h, 0 ≤ lam h) (hupsNN : ∀ h, 0 ≤ ups h) (htauNN : ∀ h, 0 ≤ tau h) :
    ∃ Llam Ltau Lups : ℝ,
      Tendsto lam atTop (𝓝 Llam) ∧
      Tendsto tau atTop (𝓝 Ltau) ∧
      Tendsto ups atTop (𝓝 Lups) ∧
      hexBdryCl * Llam + hexBdryCt * Ltau + Lups = 1 :=
  hexContour_limits lam tau ups hbdry hlamMono hupsMono hlamNN hupsNN htauNN

























theorem hexZDiv_branch (c lam tau ups : ℕ → ℝ)
    (hbdry : ∀ v, 1 ≤ v → hexCl * lam v + hexCt * tau v + ups v = 1)
    (hlamMono : ∀ v, 1 ≤ v → lam v ≤ lam (v + 1))
    (hυpos : ∀ v, 1 ≤ v → 0 < ups v)
    (hυnn : ∀ v, 0 ≤ ups v)
    (hτnn : ∀ v, 0 ≤ tau v)
    (Cut : ℕ → HexHighestCut hexChiE⁻¹)
    (hCutD : ∀ v, 1 ≤ v → (∑' d, (Cut v).wtγ d) = lam (v + 1) - lam v)
    (hCutB : ∀ v, 1 ≤ v → (∑' b, (Cut v).wtB b) = ups (v + 1))
    {Iτ : Type} (Eτ : HexContourEmb ℕ Iτ)
    (hEτ : Eτ.wtSAW = fun n => c n * hexChiE ^ n)
    (hτdiv : (∃ v, 1 ≤ v ∧ 0 < tau v) → ¬ Summable Eτ.wtContour)
    {Iυ : Type} (Eυ : HexColumnEmb ℕ Iυ)
    (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n)
    (hEυc : Eυ.fiberSum = ups) :
    ¬ Summable (fun n => c n * hexChiE ^ n) :=
  hexZ_chi_div_seams_closed c lam tau ups hbdry hlamMono hυpos hυnn hτnn
    Cut hCutD hCutB Eτ hEτ hτdiv Eυ hEυ hEυc
















theorem hexZDiv_branch_full (c : ℕ → ℝ)
    (lamW tauW upsW : ℕ → ℝ)
    (hbdryWidth : ∀ h, hexBdryCl * lamW h + hexBdryCt * tauW h + upsW h = 1)
    (hlamMonoW : Monotone lamW) (hupsMonoW : Monotone upsW)
    (hlamNNW : ∀ h, 0 ≤ lamW h) (hupsNNW : ∀ h, 0 ≤ upsW h) (htauNNW : ∀ h, 0 ≤ tauW h)
    (lam tau ups : ℕ → ℝ)
    (hbdryScale : ∀ v, 1 ≤ v → hexCl * lam v + hexCt * tau v + ups v = 1)
    (hlamMono : ∀ v, 1 ≤ v → lam v ≤ lam (v + 1))
    (hυpos : ∀ v, 1 ≤ v → 0 < ups v)
    (hυnn : ∀ v, 0 ≤ ups v)
    (hτnn : ∀ v, 0 ≤ tau v)
    (Cut : ℕ → HexHighestCut hexChiE⁻¹)
    (hCutD : ∀ v, 1 ≤ v → (∑' d, (Cut v).wtγ d) = lam (v + 1) - lam v)
    (hCutB : ∀ v, 1 ≤ v → (∑' b, (Cut v).wtB b) = ups (v + 1))
    {Iτ : Type} (Eτ : HexContourEmb ℕ Iτ)
    (hEτ : Eτ.wtSAW = fun n => c n * hexChiE ^ n)
    (hτdiv : (∃ v, 1 ≤ v ∧ 0 < tau v) → ¬ Summable Eτ.wtContour)
    {Iυ : Type} (Eυ : HexColumnEmb ℕ Iυ)
    (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n)
    (hEυc : Eυ.fiberSum = ups) :
    (∃ Llam Ltau Lups : ℝ,
        Tendsto lamW atTop (𝓝 Llam) ∧ Tendsto tauW atTop (𝓝 Ltau) ∧
        Tendsto upsW atTop (𝓝 Lups) ∧
        hexBdryCl * Llam + hexBdryCt * Ltau + Lups = 1)
      ∧ ¬ Summable (fun n => c n * hexChiE ^ n) :=
  ⟨hexZDiv_contour_limits lamW tauW upsW hbdryWidth hlamMonoW hupsMonoW
      hlamNNW hupsNNW htauNNW,
    hexZDiv_branch c lam tau ups hbdryScale hlamMono hυpos hυnn hτnn
      Cut hCutD hCutB Eτ hEτ hτdiv Eυ hEυ hEυc⟩

end StatMech.Universality
