/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.QuantumIsingSymbolAsymptotic
import Code.FrontierA.QuantumIsingAntiperiodicReduction











open Filter Set
open scoped Topology BigOperators

namespace StatMech.FrontierA

private theorem spectralRoot_eq_exp_arcosh {a : Real} (ha : 1 ≤ a) :
    quantumIsingSpectralRoot a = Real.exp (Real.arcosh a) := by
  rw [Real.exp_arcosh ha]
  rfl

private theorem cosh_sub_one_eq_two_sinh_half_sq (t : Real) :
    Real.cosh t - 1 = 2 * Real.sinh (t / 2) ^ 2 := by
  have hdouble := Real.cosh_two_mul (t / 2)
  have hcs := Real.cosh_sq_sub_sinh_sq (t / 2)
  rw [show 2 * (t / 2) = t by ring] at hdouble
  nlinarith

private theorem spectralRoot_inv_pow_eq_exp_neg_nat_mul
    {a : Real} (ha : 1 ≤ a) (n : Nat) :
    (quantumIsingSpectralRoot a)⁻¹ ^ n =
      Real.exp (-(n : Real) * Real.arcosh a) := by
  rw [spectralRoot_eq_exp_arcosh ha, ← Real.exp_neg,
    ← Real.exp_nat_mul]
  congr 1
  ring

private theorem rapidity_log_correction_eq_cosh (x : Real) :
    x + 2 * Real.log (1 + Real.exp (-x)) =
      2 * Real.log 2 + 2 * Real.log (Real.cosh (x / 2)) := by
  have hprodOne :
      Real.exp (-x / 2) * Real.exp (x / 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  have hprodNeg :
      Real.exp (-x / 2) * Real.exp (-(x / 2)) = Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hfactor :
      1 + Real.exp (-x) =
        2 * Real.exp (-x / 2) * Real.cosh (x / 2) := by
    rw [Real.cosh_eq]
    symm
    calc
      2 * Real.exp (-x / 2) *
          ((Real.exp (x / 2) + Real.exp (-(x / 2))) / 2) =
          Real.exp (-x / 2) * Real.exp (x / 2) +
            Real.exp (-x / 2) * Real.exp (-(x / 2)) := by ring
      _ = 1 + Real.exp (-x) := by rw [hprodOne, hprodNeg]
  have hlog : Real.log (1 + Real.exp (-x)) =
      Real.log 2 + Real.log (Real.exp (-x / 2)) +
        Real.log (Real.cosh (x / 2)) := by
    rw [hfactor,
      Real.log_mul
        (mul_ne_zero (by norm_num) (Real.exp_ne_zero _))
        (Real.cosh_pos _).ne',
      Real.log_mul (by norm_num) (Real.exp_ne_zero _)]
  rw [hlog, Real.log_exp]
  ring



theorem quantumIsingTrotter_arcosh_scaled_tendsto
    (beta h k : Real) (hbeta : 0 < beta)
    (hdisp : 0 < quantumIsingDispersion h k) :
    Tendsto
      (fun n : Nat => (n + 1 : Real) * Real.arcosh
        (quantumIsingTrotterReducedParameter beta h (n + 1) k))
      atTop
      (nhds (beta / 2 * quantumIsingDispersion h k)) := by
  let a : Nat -> Real := fun n =>
    quantumIsingTrotterReducedParameter beta h (n + 1) k
  let N : Nat -> Real := fun n => n + 1
  let epsilon := quantumIsingDispersion h k
  let c := beta ^ 2 / 8 * epsilon ^ 2
  have hc : 0 < c := by
    dsimp [c, epsilon]
    positivity
  have hscaled : Tendsto (fun n => N n ^ 2 * (a n - 1)) atTop (nhds c) := by
    simpa [a, N, c, epsilon] using
      quantumIsingTrotterReducedParameter_scaled_tendsto beta h k hbeta
  have hInv : Tendsto (fun n : Nat => 1 / N n ^ 2) atTop (nhds 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real)).pow 2
    convert h using 1
    · funext n
      dsimp [N]
      field_simp
    · norm_num
  have haSub : Tendsto (fun n => a n - 1) atTop (nhds 0) := by
    have hm := hInv.mul hscaled
    convert hm using 1
    · funext n
      have hN : N n ≠ 0 := by dsimp [N]; positivity
      field_simp [hN]
    · simp
  have ha : Tendsto a atTop (nhds 1) := by
    have hadd := (tendsto_const_nhds : Tendsto (fun _ : Nat => (1 : Real))
      atTop (nhds 1)).add haSub
    convert hadd using 1
    · funext n
      ring
    · norm_num
  have hscaledPos : ∀ᶠ n in atTop, 0 < N n ^ 2 * (a n - 1) :=
    (tendsto_order.1 hscaled).1 0 hc
  have haPos : ∀ᶠ n in atTop, 1 < a n := by
    filter_upwards [hscaledPos] with n hn
    have hN : 0 < N n ^ 2 := by dsimp [N]; positivity
    nlinarith
  have haIci : ∀ᶠ n in atTop, a n ∈ Ici (1 : Real) :=
    haPos.mono fun _ hn => hn.le
  have haWithin : Tendsto a atTop (𝓝[Ici 1] 1) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨ha, haIci⟩
  have hy : Tendsto (fun n => Real.arcosh (a n)) atTop (nhds 0) := by
    simpa using (Real.continuousOn_arcosh 1 (by simp)).tendsto.comp haWithin
  have hyPos : ∀ᶠ n in atTop, 0 < Real.arcosh (a n) :=
    haPos.mono fun _ hn => Real.arcosh_pos hn
  have hyHalfRight : Tendsto (fun n => Real.arcosh (a n) / 2)
      atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · simpa using hy.div_const 2
    · exact hyPos.mono fun _ hn => div_pos hn (by norm_num)
  have hsinhRatio := sinh_div_tendsto_one_right.comp hyHalfRight
  have hsinhRatioSq := hsinhRatio.pow 2
  have hsq : Tendsto
      (fun n => (N n * Real.arcosh (a n)) ^ 2)
      atTop (nhds (2 * c)) := by
    have htwo : Tendsto (fun _ : Nat => (2 : Real)) atTop (nhds 2) :=
      tendsto_const_nhds
    have hquotRaw := (htwo.mul hscaled).div hsinhRatioSq (by norm_num)
    have hquot : Tendsto
        ((fun n => 2 * (N n ^ 2 * (a n - 1))) /
          fun n => ((fun t => Real.sinh t / t)
            (Real.arcosh (a n) / 2)) ^ 2)
        atTop (nhds (2 * c)) := by
      simpa using hquotRaw
    apply hquot.congr'
    filter_upwards [haPos] with n han
    let y := Real.arcosh (a n)
    have hy0 : 0 < y := Real.arcosh_pos han
    have hcosh : Real.cosh y = a n := Real.cosh_arcosh han.le
    have hidentity := cosh_sub_one_eq_two_sinh_half_sq y
    rw [hcosh] at hidentity
    dsimp [y] at hidentity ⊢
    have hN : N n ≠ 0 := by dsimp [N]; positivity
    have hsinh0 : Real.sinh (Real.arcosh (a n) / 2) ≠ 0 :=
      (Real.sinh_pos_iff.mpr (div_pos hy0 (by norm_num))).ne'
    rw [hidentity]
    field_simp [hy0.ne', hN, hsinh0]
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have hNy : Tendsto (fun n => N n * Real.arcosh (a n))
      atTop (nhds (Real.sqrt (2 * c))) := by
    apply hsqrt.congr'
    filter_upwards [haPos] with n han
    change Real.sqrt ((N n * Real.arcosh (a n)) ^ 2) =
      N n * Real.arcosh (a n)
    rw [Real.sqrt_sq]
    exact mul_nonneg (by dsimp [N]; positivity)
      (Real.arcosh_nonneg han.le)
  have hsqrtValue : Real.sqrt (2 * c) = beta / 2 * epsilon := by
    have hb : 0 ≤ beta / 2 := (div_pos hbeta (by norm_num)).le
    have he : 0 ≤ epsilon := hdisp.le
    rw [show 2 * c = (beta / 2 * epsilon) ^ 2 by dsimp [c]; ring,
      Real.sqrt_sq (mul_nonneg hb he)]
  simpa [a, N, epsilon, hsqrtValue] using hNy

theorem eventually_one_lt_quantumIsingTrotterReducedParameter
    (beta h k : Real) (hbeta : 0 < beta)
    (hdisp : 0 < quantumIsingDispersion h k) :
    ∀ᶠ n in atTop,
      1 < quantumIsingTrotterReducedParameter beta h (n + 1) k := by
  let epsilon := quantumIsingDispersion h k
  let c := beta ^ 2 / 8 * epsilon ^ 2
  have hc : 0 < c := by
    dsimp [c, epsilon]
    positivity
  have hscaled := quantumIsingTrotterReducedParameter_scaled_tendsto
    beta h k hbeta
  have hpos : ∀ᶠ n : Nat in atTop,
      0 < (n + 1 : Real) ^ 2 *
        (quantumIsingTrotterReducedParameter beta h (n + 1) k - 1) :=
    (tendsto_order.1 hscaled).1 0 hc
  filter_upwards [hpos] with n hn
  have hN : 0 < (n + 1 : Real) ^ 2 := by positivity
  nlinarith



theorem quantumIsingAntiperiodicLogSum_tendsto_raw
    (beta h k : Real) (hbeta : 0 < beta)
    (hdisp : 0 < quantumIsingDispersion h k) :
    Tendsto
      (fun n : Nat =>
        (∑ j ∈ Finset.range (n + 1),
          Real.log
            (quantumIsingTrotterReducedParameter beta h (n + 1) k -
              Real.cos (quantumIsingAntiperiodicAngle (n + 1) j))) +
          (n + 1 : Real) * Real.log 2)
      atTop
      (nhds
        (beta / 2 * quantumIsingDispersion h k +
          2 * Real.log
            (1 + Real.exp
              (-(beta / 2 * quantumIsingDispersion h k))))) := by
  let x := beta / 2 * quantumIsingDispersion h k
  have hrapid := quantumIsingTrotter_arcosh_scaled_tendsto
    beta h k hbeta hdisp
  have hcorr : Tendsto
      (fun n : Nat => 2 * Real.log
        (1 + Real.exp
          (-((n + 1 : Real) * Real.arcosh
            (quantumIsingTrotterReducedParameter beta h (n + 1) k)))))
      atTop (nhds (2 * Real.log (1 + Real.exp (-x)))) := by
    have hc : ContinuousAt
        (fun z : Real => 2 * Real.log (1 + Real.exp (-z))) x := by
      fun_prop (disch := positivity)
    exact hc.tendsto.comp hrapid
  have hsum := hrapid.add hcorr
  have ha := eventually_one_lt_quantumIsingTrotterReducedParameter
    beta h k hbeta hdisp
  apply hsum.congr'
  filter_upwards [ha] with n han
  have hexact :=
    sum_log_quantumIsingTrotterReducedParameter_sub_cos
      beta h k (n + 1) (Nat.succ_ne_zero n) han
  rw [hexact,
    spectralRoot_inv_pow_eq_exp_neg_nat_mul han.le (n + 1)]
  norm_num [Nat.cast_add, Nat.cast_one]
  ring




theorem quantumIsingAntiperiodicLogSum_tendsto
    (beta h k : Real) (hbeta : 0 < beta)
    (hdisp : 0 < quantumIsingDispersion h k) :
    Tendsto
      (fun n : Nat =>
        (∑ j ∈ Finset.range (n + 1),
          Real.log
            (quantumIsingTrotterReducedParameter beta h (n + 1) k -
              Real.cos (quantumIsingAntiperiodicAngle (n + 1) j))) +
          (n + 1 : Real) * Real.log 2)
      atTop
      (nhds (2 * Real.log 2 + 2 * quantumIsingModeLog beta h k)) := by
  have hraw := quantumIsingAntiperiodicLogSum_tendsto_raw
    beta h k hbeta hdisp
  convert hraw using 1
  unfold quantumIsingModeLog
  rw [rapidity_log_correction_eq_cosh]
  congr 3
  ring

end StatMech.FrontierA
