/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.QuantumIsingUniformMode
import Code.FrontierA.QuantumIsingSectorProductComparison
import Code.FrontierA.QuantumIsingNormalizedPartitionSandwich
import Code.FrontierA.QuantumIsingSpatialSeam









open Filter
open scoped Topology

namespace StatMech.FrontierA

noncomputable def quantumIsingNormalizedDiagonalLogDensity
    (beta h : Real) (n : Nat) : Real :=
  Real.log (quantumIsingNormalizedDiagonalPartition beta h (n + 3)) /
    (n + 3 : Real)

theorem quantumIsingElevenSectorHalfLogDensity_tendsto
    (beta h : Real) (hbeta : 0 < beta) (hh : 0 < h) :
    Tendsto (fun n : Nat ↦ (1 / 2 : Real) *
        quantumIsingElevenSectorLogDensity beta h n) atTop
      (nhds ((1 / 2 : Real) * ((1 / (2 * Real.pi)) *
        ∫ k in (-Real.pi)..Real.pi,
          (2 * Real.log 2 + 2 * quantumIsingModeLog beta h k)))) :=
  tendsto_const_nhds.mul
    (quantumIsingElevenSectorLogDensity_tendsto beta h hbeta hh)

theorem quantumIsingNormalizedDiagonalLogDensity_tendsto
    (beta h : Real) (hbeta : 0 < beta) (hh : 0 < h) :
    Tendsto (quantumIsingNormalizedDiagonalLogDensity beta h) atTop
      (nhds ((1 / 2 : Real) * ((1 / (2 * Real.pi)) *
        ∫ k in (-Real.pi)..Real.pi,
          (2 * Real.log 2 + 2 * quantumIsingModeLog beta h k)))) := by
  let lower : Nat → Real := fun n ↦
    (1 / 2 : Real) * quantumIsingElevenSectorLogDensity beta h n
  let upper : Nat → Real := fun n ↦ lower n + Real.log 2 / (n + 3 : Real)
  have hlower : Tendsto lower atTop
      (nhds ((1 / 2 : Real) * ((1 / (2 * Real.pi)) *
        ∫ k in (-Real.pi)..Real.pi,
          (2 * Real.log 2 + 2 * quantumIsingModeLog beta h k)))) := by
    exact quantumIsingElevenSectorHalfLogDensity_tendsto beta h hbeta hh
  have hcorr : Tendsto (fun n : Nat ↦ Real.log 2 / (n + 3 : Real))
      atTop (nhds 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)).comp
      (tendsto_add_atTop_nat 3)
    convert h using 1
    funext n
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_ofNat]
  have hupper : Tendsto upper atTop
      (nhds ((1 / 2 : Real) * ((1 / (2 * Real.pi)) *
        ∫ k in (-Real.pi)..Real.pi,
          (2 * Real.log 2 + 2 * quantumIsingModeLog beta h k)))) := by
    simpa only [upper, add_zero] using hlower.add hcorr
  have hxlim : Tendsto (fun L : Nat ↦ beta * h / (2 * (L : Real)))
      atTop (nhds 0) := by
    have hlim := tendsto_const_div_atTop_nhds_zero_nat (beta * h / 2)
    convert hlim using 1
    funext L
    ring
  have hxlt : ∀ᶠ L : Nat in atTop, beta * h / (2 * (L : Real)) < 1 :=
    (tendsto_order.1 hxlim).2 1 (by norm_num)
  have hxltShift := (tendsto_add_atTop_nat 3).eventually hxlt
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [hxltShift] with n hx1
    let L := n + 3
    letI : Fact (2 < L) := ⟨by dsimp only [L]; omega⟩
    have hx : 0 < beta * h / (2 * (L : Real)) := by positivity
    have hs := quantumIsingNormalizedDiagonalPartition_log_sandwich
      beta h L hbeta hx hx1
    have hmax := arfSectorNormMax_quantumIsingNormalizedSpinSector_eq_eleven
      beta h L hbeta hh hx hx1
    rw [hmax] at hs
    dsimp only [lower, quantumIsingElevenSectorLogDensity,
      quantumIsingNormalizedDiagonalLogDensity, L]
    have hden : 0 < (n + 3 : Real) := by positivity
    calc
      (1 / 2 : Real) *
          (2 * Real.log
            ‖quantumIsingNormalizedSpinSector beta h (n + 3) 1 1‖ /
              (n + 3 : Real)) =
          Real.log ‖quantumIsingNormalizedSpinSector beta h (n + 3) 1 1‖ /
            (n + 3 : Real) := by ring
      _ ≤ Real.log (quantumIsingNormalizedDiagonalPartition beta h (n + 3)) /
          (n + 3 : Real) := div_le_div_of_nonneg_right hs.1 hden.le
  · filter_upwards [hxltShift] with n hx1
    let L := n + 3
    letI : Fact (2 < L) := ⟨by dsimp only [L]; omega⟩
    have hx : 0 < beta * h / (2 * (L : Real)) := by positivity
    have hs := quantumIsingNormalizedDiagonalPartition_log_sandwich
      beta h L hbeta hx hx1
    have hmax := arfSectorNormMax_quantumIsingNormalizedSpinSector_eq_eleven
      beta h L hbeta hh hx hx1
    rw [hmax] at hs
    dsimp only [upper, lower, quantumIsingElevenSectorLogDensity,
      quantumIsingNormalizedDiagonalLogDensity, L]
    have hden : 0 < (n + 3 : Real) := by positivity
    calc
      Real.log (quantumIsingNormalizedDiagonalPartition beta h (n + 3)) /
          (n + 3 : Real) ≤
        (Real.log ‖quantumIsingNormalizedSpinSector beta h (n + 3) 1 1‖ +
          Real.log 2) / (n + 3 : Real) :=
        div_le_div_of_nonneg_right hs.2 hden.le
      _ = (1 / 2 : Real) *
          (2 * Real.log
            ‖quantumIsingNormalizedSpinSector beta h (n + 3) 1 1‖ /
              (n + 3 : Real)) +
            Real.log 2 / (n + 3 : Real) := by ring

theorem quantumIsingNormalizedDiagonalPartition_eq_pathPartition
    (beta h : Real) (L : Nat)
    (hpos : 0 < beta * h / (2 * L)) :
    quantumIsingNormalizedDiagonalPartition beta h L =
      quantumIsingTrotterPathPartition beta h L L := by
  rw [quantumIsingTrotterPathPartition_eq_classical beta h L L hpos,
    quantumIsingTrotterNormalization_eq_pow]
  rfl

theorem quantumIsingPeriodicTrotterAction_eq_log_pathPartition
    (beta h : Real) (n L : Nat) (hL : L ≠ 0) :
    quantumIsingPeriodicTrotterAction beta h n L =
      -Real.log (quantumIsingTrotterPathPartition beta h n L) / beta := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hL
  rfl

noncomputable def quantumIsingCofinalPeriodicTrotterFreeEnergy
    (beta h : Real) (n : Nat) : Real :=
  quantumIsingPeriodicTrotterAction beta h (n + 3) (n + 3) /
    (n + 3 : Real)

theorem quantumIsingCofinalPeriodicTrotterFreeEnergy_eq_logDensity
    (beta h : Real) (n : Nat) (hbeta : 0 < beta) (hh : 0 < h) :
    quantumIsingCofinalPeriodicTrotterFreeEnergy beta h n =
      -quantumIsingNormalizedDiagonalLogDensity beta h n / beta := by
  let L := n + 3
  have hL : L ≠ 0 := by dsimp only [L]; omega
  have hpos : 0 < beta * h / (2 * (L : Real)) := by positivity
  unfold quantumIsingCofinalPeriodicTrotterFreeEnergy
  rw [quantumIsingPeriodicTrotterAction_eq_log_pathPartition beta h L L hL,
    ← quantumIsingNormalizedDiagonalPartition_eq_pathPartition beta h L hpos]
  unfold quantumIsingNormalizedDiagonalLogDensity
  dsimp only [L]
  ring

theorem quantumIsingCofinalPeriodicTrotterFreeEnergy_tendsto
    (beta h : Real) (hbeta : 0 < beta) (hh : 0 < h) :
    Tendsto (quantumIsingCofinalPeriodicTrotterFreeEnergy beta h) atTop
      (nhds (-((1 / 2 : Real) * ((1 / (2 * Real.pi)) *
        ∫ k in (-Real.pi)..Real.pi,
          (2 * Real.log 2 + 2 * quantumIsingModeLog beta h k))) / beta)) := by
  have htend := (quantumIsingNormalizedDiagonalLogDensity_tendsto
    beta h hbeta hh).neg.div_const beta
  apply htend.congr'
  filter_upwards with n
  exact (quantumIsingCofinalPeriodicTrotterFreeEnergy_eq_logDensity
    beta h n hbeta hh).symm

theorem quantumIsingCofinalTrotterThermodynamicFreeEnergy_tendsto_raw
    (beta h : Real) (hbeta : 0 < beta) (hh : 0 < h) :
    Tendsto (fun n : Nat ↦
      quantumIsingTrotterThermodynamicFreeEnergy beta h (n + 3)) atTop
      (nhds (-((1 / 2 : Real) * ((1 / (2 * Real.pi)) *
        ∫ k in (-Real.pi)..Real.pi,
          (2 * Real.log 2 + 2 * quantumIsingModeLog beta h k))) / beta)) := by
  have hfinite := quantumIsingCofinalPeriodicTrotterFreeEnergy_tendsto
    beta h hbeta hh
  have herr : Tendsto (fun n : Nat ↦ 1 / (2 * (n + 3 : Real)))
      atTop (nhds 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (1 / 2 : Real)).comp
      (tendsto_add_atTop_nat 3)
    convert h using 1
    funext n
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_ofNat]
    field_simp
  have hdiffAbs : Tendsto (fun n : Nat ↦
      |quantumIsingTrotterThermodynamicFreeEnergy beta h (n + 3) -
        quantumIsingCofinalPeriodicTrotterFreeEnergy beta h n|)
      atTop (nhds 0) := by
    apply squeeze_zero (fun n ↦ abs_nonneg _) (fun n ↦ ?_) herr
    unfold quantumIsingCofinalPeriodicTrotterFreeEnergy
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (quantumIsingPeriodicTrotterFreeEnergy_uniform_bound
        beta h (n + 3) (by omega) hbeta (mul_pos hbeta hh) (L := n + 3)
          (by omega))
  have hdiff : Tendsto (fun n : Nat ↦
      quantumIsingTrotterThermodynamicFreeEnergy beta h (n + 3) -
        quantumIsingCofinalPeriodicTrotterFreeEnergy beta h n)
      atTop (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [sub_zero, Real.norm_eq_abs] using hdiffAbs
  convert hfinite.add hdiff using 1
  · funext n
    ring
  · ring

theorem quantumIsing_half_modeIntegral_eq_logPressure (beta h : Real) :
    (1 / 2 : Real) * ((1 / (2 * Real.pi)) *
      ∫ k in (-Real.pi)..Real.pi,
        (2 * Real.log 2 + 2 * quantumIsingModeLog beta h k)) =
      Real.log 2 + (1 / (2 * Real.pi)) *
        ∫ k in (-Real.pi)..Real.pi, quantumIsingModeLog beta h k := by
  have hmode : IntervalIntegrable (quantumIsingModeLog beta h)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (continuous_quantumIsingModeLog beta h).intervalIntegrable _ _
  rw [intervalIntegral.integral_add intervalIntegral.intervalIntegrable_const
    (hmode.const_mul 2), intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul]
  norm_num only [smul_eq_mul]
  field_simp [Real.pi_ne_zero]
  ring



theorem quantumIsingCofinalTrotterThermodynamicFreeEnergy_tendsto
    (beta h : Real) (hbeta : 0 < beta) (hh : 0 < h) :
    Tendsto (fun n : Nat ↦
      quantumIsingTrotterThermodynamicFreeEnergy beta h (n + 3)) atTop
      (nhds (quantumIsingFreeEnergyValue beta h)) := by
  have h := quantumIsingCofinalTrotterThermodynamicFreeEnergy_tendsto_raw
    beta h hbeta hh
  convert h using 1
  unfold quantumIsingFreeEnergyValue
  rw [quantumIsing_half_modeIntegral_eq_logPressure]
  ring

end StatMech.FrontierA
