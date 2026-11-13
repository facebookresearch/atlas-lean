/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.RiemannPeriodic










open scoped BigOperators
open MeasureTheory

namespace StatMech.FrontierA



noncomputable def quantumIsingDispersion (h k : ℝ) : ℝ :=
  Real.sqrt (1 + 4 * h ^ 2 + 4 * h * Real.cos k)


noncomputable def quantumIsingModeLog (beta h k : ℝ) : ℝ :=
  Real.log (Real.cosh (beta / 4 * quantumIsingDispersion h k))



noncomputable def quantumIsingFreeEnergyValue (beta h : ℝ) : ℝ :=
  -Real.log 2 / beta -
    (1 / (2 * Real.pi * beta)) *
      ∫ k in (-Real.pi)..Real.pi, quantumIsingModeLog beta h k



noncomputable def quantumIsingBogoliubovFreeEnergy
    (beta h : ℝ) (L : ℕ) : ℝ :=
  -Real.log 2 / beta -
    (1 / (beta * L)) *
      ∑ j ∈ Finset.range L,
        quantumIsingModeLog beta h (2 * Real.pi * j / L)

private theorem quantumIsing_radicand_eq_sq_add_sq (h k : ℝ) :
    1 + 4 * h ^ 2 + 4 * h * Real.cos k =
      (2 * h + Real.cos k) ^ 2 + Real.sin k ^ 2 := by
  nlinarith [Real.sin_sq_add_cos_sq k]

theorem quantumIsing_radicand_nonneg (h k : ℝ) :
    0 ≤ 1 + 4 * h ^ 2 + 4 * h * Real.cos k := by
  rw [quantumIsing_radicand_eq_sq_add_sq]
  positivity

theorem continuous_quantumIsingDispersion (h : ℝ) :
    Continuous (quantumIsingDispersion h) := by
  unfold quantumIsingDispersion
  fun_prop

theorem continuous_quantumIsingModeLog (beta h : ℝ) :
    Continuous (quantumIsingModeLog beta h) := by
  unfold quantumIsingModeLog
  apply Continuous.log
  · exact Real.continuous_cosh.comp
      (continuous_const.mul (continuous_quantumIsingDispersion h))
  · intro k
    exact (Real.cosh_pos _).ne'

theorem periodic_quantumIsingDispersion (h : ℝ) :
    Function.Periodic (quantumIsingDispersion h) (2 * Real.pi) := by
  intro k
  simp [quantumIsingDispersion, Real.cos_add_two_pi]

theorem periodic_quantumIsingModeLog (beta h : ℝ) :
    Function.Periodic (quantumIsingModeLog beta h) (2 * Real.pi) := by
  intro k
  simp [quantumIsingModeLog, quantumIsingDispersion,
    Real.cos_add_two_pi]



theorem quantumIsingDispersion_neg_eq_shift (h k : ℝ) :
    quantumIsingDispersion (-h) k =
      quantumIsingDispersion h (k + Real.pi) := by
  unfold quantumIsingDispersion
  rw [Real.cos_add_pi]
  congr 1
  ring

theorem quantumIsingModeLog_neg_eq_shift (beta h k : ℝ) :
    quantumIsingModeLog beta (-h) k =
      quantumIsingModeLog beta h (k + Real.pi) := by
  unfold quantumIsingModeLog
  rw [quantumIsingDispersion_neg_eq_shift]

theorem integral_quantumIsingModeLog_shift (beta h : ℝ) :
    (∫ k in (0 : ℝ)..(2 * Real.pi), quantumIsingModeLog beta h k) =
      ∫ k in (-Real.pi)..Real.pi, quantumIsingModeLog beta h k := by
  have hshift :=
    (periodic_quantumIsingModeLog beta h).intervalIntegral_add_eq 0 (-Real.pi)
  convert hshift using 1 <;> ring



theorem integral_quantumIsingModeLog_neg (beta h : ℝ) :
    (∫ k in (-Real.pi)..Real.pi, quantumIsingModeLog beta (-h) k) =
      ∫ k in (-Real.pi)..Real.pi, quantumIsingModeLog beta h k := by
  calc
    (∫ k in (-Real.pi)..Real.pi, quantumIsingModeLog beta (-h) k) =
        ∫ k in (-Real.pi)..Real.pi,
          quantumIsingModeLog beta h (k + Real.pi) := by
      apply intervalIntegral.integral_congr
      intro k _
      exact quantumIsingModeLog_neg_eq_shift beta h k
    _ = ∫ k in (0 : ℝ)..(2 * Real.pi),
          quantumIsingModeLog beta h k := by
      rw [intervalIntegral.integral_comp_add_right]
      congr 1 <;> ring
    _ = _ := integral_quantumIsingModeLog_shift beta h


theorem quantumIsingFreeEnergyValue_neg (beta h : ℝ) :
    quantumIsingFreeEnergyValue beta (-h) =
      quantumIsingFreeEnergyValue beta h := by
  unfold quantumIsingFreeEnergyValue
  rw [integral_quantumIsingModeLog_neg]


theorem quantumIsingModeLog_average_tendsto (beta h : ℝ) :
    Filter.Tendsto
      (fun L : ℕ =>
        (1 / (L : ℝ)) * ∑ j ∈ Finset.range L,
          quantumIsingModeLog beta h (2 * Real.pi * j / L))
      Filter.atTop
      (nhds ((1 / (2 * Real.pi)) *
        ∫ k in (-Real.pi)..Real.pi, quantumIsingModeLog beta h k)) := by
  have hriemann := StatMech.Onsager.ons_riemann_periodic
    (quantumIsingModeLog beta h)
    (continuous_quantumIsingModeLog beta h)
    (periodic_quantumIsingModeLog beta h)
  have hscaled := (tendsto_const_nhds.mul hriemann :
    Filter.Tendsto
      (fun L : ℕ =>
        (1 / (2 * Real.pi)) *
          ((2 * Real.pi / L) * ∑ j ∈ Finset.range L,
            quantumIsingModeLog beta h (2 * Real.pi * j / L)))
      Filter.atTop
      (nhds ((1 / (2 * Real.pi)) *
        ∫ k in (0 : ℝ)..(2 * Real.pi), quantumIsingModeLog beta h k)))
  rw [integral_quantumIsingModeLog_shift beta h] at hscaled
  convert hscaled using 1
  funext L
  by_cases hL : L = 0
  · simp [hL]
  · field_simp [hL, Real.pi_ne_zero]


theorem quantumIsingBogoliubovFreeEnergy_tendsto
    (beta h : ℝ) :
    Filter.Tendsto
      (quantumIsingBogoliubovFreeEnergy beta h)
      Filter.atTop
      (nhds (quantumIsingFreeEnergyValue beta h)) := by
  have havg := quantumIsingModeLog_average_tendsto beta h
  have hmul := (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℕ => (1 / beta : ℝ)) Filter.atTop
        (nhds (1 / beta))).mul havg
  have hsub := (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℕ => (-Real.log 2 / beta : ℝ))
        Filter.atTop (nhds (-Real.log 2 / beta))).sub hmul
  convert hsub using 1
  · funext L
    simp only [quantumIsingBogoliubovFreeEnergy, div_eq_mul_inv]
    ring
  · simp only [quantumIsingFreeEnergyValue, div_eq_mul_inv]
    field_simp [Real.pi_ne_zero]

end StatMech.FrontierA
