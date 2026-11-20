/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.Z2GaugeCriticalCoupling
import Code.FrontierA.Z2GaugeDisorderGluing

open Filter Set Topology

namespace StatMech.FrontierA



theorem eventual_areaLaw_of_logDensity_tendsto
    (w : Nat → Real) (tau : Real)
    (hw : ∀ n, 0 < w n)
    (hlim : Tendsto (fun n : Nat =>
      -Real.log (w n) / ((n + 1 : Nat) : Real) ^ 2)
      atTop (nhds tau))
    (htau : 0 < tau) :
    ∀ᶠ n : Nat in atTop,
      w n ≤ Real.exp (-(tau / 2) * ((n + 1 : Nat) : Real) ^ 2) := by
  have hhalf : tau / 2 < tau := by linarith
  have hevent := hlim.eventually (Ioi_mem_nhds hhalf)
  filter_upwards [hevent] with n hn
  have harea : (0 : Real) < ((n + 1 : Nat) : Real) ^ 2 := by positivity
  have hscaled : (tau / 2) * ((n + 1 : Nat) : Real) ^ 2 <
      -Real.log (w n) := (lt_div_iff₀ harea).mp hn
  have hlog : Real.log (w n) <
      -(tau / 2) * ((n + 1 : Nat) : Real) ^ 2 := by linarith
  have hexp := (Real.exp_lt_exp.mpr hlog).le
  rw [Real.exp_log (hw n)] at hexp
  exact hexp



theorem eventual_perimeterLaw_of_negLog_le
    (w : Nat → Real) (C : Real)
    (hw : ∀ n, 0 < w n)
    (hcost : ∀ᶠ n : Nat in atTop,
      -Real.log (w n) ≤ C * ((n + 1 : Nat) : Real)) :
    ∀ᶠ n : Nat in atTop,
      Real.exp (-C * ((n + 1 : Nat) : Real)) ≤ w n := by
  filter_upwards [hcost] with n hn
  have hlog : -C * ((n + 1 : Nat) : Real) ≤ Real.log (w n) := by
    linarith
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (hw n)] at hexp
  exact hexp


noncomputable def cubicalSquareWilsonExpectation
    (beta : Real) (n : Nat) : Real :=
  gaugeWilsonExpectation
    (cubicalPlaquetteIncidence (a := n + 1) (b := n + 1) (c := n + 1))
    (fun _ : CubicalPlaquette (n + 1) (n + 1) (n + 1) => beta)
    (cubicalXYLoop (a := n + 1) (b := n + 1) (c := n + 1)
      (0 : Fin (n + 1 + 1)))

theorem cubicalSquareWilsonExpectation_pos
    {beta : Real} (hbeta : 0 < beta) (n : Nat) :
    0 < cubicalSquareWilsonExpectation beta n := by
  let L := n + 1
  have hL : 0 < L := by omega
  dsimp [cubicalSquareWilsonExpectation, L]
  exact (gaugeWilsonExpectation_pos_iff_exists_boundary
    cubicalPlaquetteIncidence (fun _ : CubicalPlaquette L L L => beta)
      (fun _ => hbeta) (cubicalXYLoop (0 : Fin (L + 1)))).mpr
    ⟨cubicalXYSheet (0 : Fin (L + 1)),
      cubicalXYSheet_hasWilsonBoundary (0 : Fin (L + 1))⟩

@[simp] theorem cubicalSquareWilsonFreeEnergy_eq_neg_log
    (beta : Real) (n : Nat) :
    cubicalSquareWilsonFreeEnergy beta n =
      -Real.log (cubicalSquareWilsonExpectation beta n) := rfl



theorem cubicalSquareWilson_eventually_areaLaw
    {beta tau : Real} (hbeta : 0 < beta)
    (hlim : Tendsto (cubicalSquareWilsonDensity beta) atTop (nhds tau))
    (htau : 0 < tau) :
    ∀ᶠ n : Nat in atTop,
      cubicalSquareWilsonExpectation beta n ≤
        Real.exp (-(tau / 2) * ((n + 1 : Nat) : Real) ^ 2) := by
  apply eventual_areaLaw_of_logDensity_tendsto
    (cubicalSquareWilsonExpectation beta) tau
    (cubicalSquareWilsonExpectation_pos hbeta)
  · have heq : (fun n : Nat =>
        -Real.log (cubicalSquareWilsonExpectation beta n) /
          ((n + 1 : Nat) : Real) ^ 2) =
        cubicalSquareWilsonDensity beta := by
      funext n
      rfl
    rw [heq]
    exact hlim
  · exact htau



theorem cubicalSquareWilson_eventually_perimeterLaw
    {beta C : Real} (hbeta : 0 < beta)
    (hcost : ∀ᶠ n : Nat in atTop,
      cubicalSquareWilsonFreeEnergy beta n ≤
        C * ((n + 1 : Nat) : Real)) :
    ∀ᶠ n : Nat in atTop,
      Real.exp (-C * ((n + 1 : Nat) : Real)) ≤
        cubicalSquareWilsonExpectation beta n := by
  apply eventual_perimeterLaw_of_negLog_le
    (cubicalSquareWilsonExpectation beta) C
    (cubicalSquareWilsonExpectation_pos hbeta)
  filter_upwards [hcost] with n hn
  simpa only [cubicalSquareWilsonFreeEnergy_eq_neg_log] using hn




theorem cubicalSquareWilson_rate_pos_iff_below_critical
    {betaGauge betaIsingC tau : Real}
    (hGauge : 0 < betaGauge) (hIsingC : 0 < betaIsingC)
    (isingSurfaceTension : Real → Real)
    (hidentify : tau =
      isingSurfaceTension (gaugeDualCoupling betaGauge))
    (hphase : 0 < isingSurfaceTension (gaugeDualCoupling betaGauge) ↔
      betaIsingC < gaugeDualCoupling betaGauge) :
    0 < tau ↔ betaGauge < gaugeCriticalCoupling betaIsingC := by
  rw [hidentify, hphase]
  exact lt_gaugeDualCoupling_iff_lt_gaugeCriticalCoupling hGauge hIsingC





theorem cubicalSquareWilson_areaLaw_of_dual_surfaceTension
    {betaGauge betaIsingC tau : Real}
    (hGauge : 0 < betaGauge) (hIsingC : 0 < betaIsingC)
    (isingSurfaceTension : Real → Real)
    (hlim : Tendsto (cubicalSquareWilsonDensity betaGauge) atTop (nhds tau))
    (hidentify : tau =
      isingSurfaceTension (gaugeDualCoupling betaGauge))
    (hphase : 0 < isingSurfaceTension (gaugeDualCoupling betaGauge) ↔
      betaIsingC < gaugeDualCoupling betaGauge)
    (hbelow : betaGauge < gaugeCriticalCoupling betaIsingC) :
    ∀ᶠ n : Nat in atTop,
      cubicalSquareWilsonExpectation betaGauge n ≤
        Real.exp (-(tau / 2) * ((n + 1 : Nat) : Real) ^ 2) := by
  apply cubicalSquareWilson_eventually_areaLaw hGauge hlim
  exact (cubicalSquareWilson_rate_pos_iff_below_critical
    hGauge hIsingC isingSurfaceTension hidentify hphase).2 hbelow

end StatMech.FrontierA
