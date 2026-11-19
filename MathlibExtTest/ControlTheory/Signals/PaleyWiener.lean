/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.ControlTheory.Signals.PaleyWiener

open MeasureTheory intervalIntegral
open ControlTheory

-- Boundary: the zero profile has zero representative, at any band and time.
example : PW.rep 3 0 7 = 0 := by
  simp [PW.rep]

-- Boundary: the zero profile is square integrable, so its representative is
-- continuous by `PW.rep_continuous`.
example : Continuous (PW.rep 5 0) := PW.rep_continuous MemLp.zero

-- Boundary: zero width gives the zero representative for every profile.
example {g : ℝ → ℂ} (t : ℝ) : PW.rep 0 g t = 0 := by
  simp [PW.rep]

-- Boundary: the representative is an oriented interval integral, so a
-- negative width negates the value (`∫ ν in 1..-1, 1 = -2`).
example : PW.rep (-1) (fun _ => (1 : ℂ)) 0 = -2 := by
  have h : PW.rep (-1) (fun _ => (1 : ℂ)) 0
      = ∫ _ν in (1 : ℝ)..(-1), (1 : ℂ) := by
    simp [PW.rep]
  rw [h, intervalIntegral.integral_const]
  norm_num

-- Happy path: the constant profile `1` on the band `[-1, 1]` at time `0`
-- returns the band width `2`.
example : PW.rep 1 (fun _ => (1 : ℂ)) 0 = 2 := by
  have h : PW.rep 1 (fun _ => (1 : ℂ)) 0
      = ∫ _ν in (-1 : ℝ)..1, (1 : ℂ) := by
    simp [PW.rep]
  rw [h, intervalIntegral.integral_const]
  norm_num

-- Linearity seen by a consumer: the sum of two constant profiles integrates
-- to twice the single-profile value.
example : PW.rep 1 ((fun _ => (1 : ℂ)) + (fun _ => (1 : ℂ))) 0 = 4 := by
  rw [PW.rep_add intervalIntegrable_const intervalIntegrable_const]
  have h : PW.rep 1 (fun _ => (1 : ℂ)) 0 = 2 := by
    have hh : PW.rep 1 (fun _ => (1 : ℂ)) 0
        = ∫ _ν in (-1 : ℝ)..1, (1 : ℂ) := by
      simp [PW.rep]
    rw [hh, intervalIntegral.integral_const]
    norm_num
  rw [h]
  norm_num

-- Boundary: a profile vanishing on the band has zero representative, however
-- it behaves outside the band.
example {g : ℝ → ℂ} (hg : ∀ ν ∈ Set.Icc (-1 : ℝ) 1, g ν = 0) (t : ℝ) :
    PW.rep 1 g t = 0 := by
  have h : (∫ ν in (-1 : ℝ)..1, g ν * Complex.exp (2 * Real.pi * Complex.I * ν * t))
      = ∫ _ν in (-1 : ℝ)..1, (0 : ℂ) := by
    apply intervalIntegral.integral_congr
    intro ν hν
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hν
    simp [hg ν hν]
  rw [PW.rep, h]
  simp

-- Bound applied to a nonzero in-class profile: the indicator of `[-1, 1]`
-- with value `1` is square integrable, so `PW.norm_rep_le` bounds its
-- representative at time `0` by `2`.
example :
    ‖PW.rep 1 ((Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℂ))) 0‖ ≤ 2 := by
  have hMe : NullMeasurableSet (Set.Icc (-1 : ℝ) 1) (volume : Measure ℝ) :=
    measurableSet_Icc.nullMeasurableSet
  have hMem : MemLp ((Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℂ))) 2 volume :=
    memLp_indicator_const 2 hMe (1 : ℂ) (.inr (by simp [Real.volume_Icc]))
  have hbound := PW.norm_rep_le (B := 1) (g := (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℂ))) (by norm_num) hMem 0
  have hnorm : (eLpNorm ((Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℂ))) 2 volume).toReal
      = Real.sqrt 2 := by
    rw [eLpNorm_indicator_const hMe (by norm_num) (by norm_num)]
    simp only [Real.volume_Icc, enorm_one, one_mul, ← ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 - -1), Real.sqrt_eq_rpow]
    norm_num
  rw [hnorm, mul_one] at hbound
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  calc ‖PW.rep 1 ((Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℂ))) 0‖
      ≤ Real.sqrt 2 * Real.sqrt 2 := hbound
    _ = 2 := h2

-- The zero extension agrees with the profile on the band and vanishes off it.
example : PW.bandExt 1 (fun _ => (3 : ℂ)) (1 / 2) = 3 := by
  have hmem : (1 / 2 : ℝ) ∈ Set.Icc (-1) 1 := ⟨by norm_num, by norm_num⟩
  exact Set.indicator_of_mem hmem _

example : PW.bandExt 1 (fun _ => (3 : ℂ)) 2 = 0 := by
  have hmem : (2 : ℝ) ∉ Set.Icc (-1) 1 := by norm_num [Set.mem_Icc]
  exact Set.indicator_of_notMem hmem _

-- Sample-coefficient identity at the boundary `2 * B * T = 1`: the constant
-- profile has zeroth coefficient `1`.
example :
    fourierCoeffOn (show (-(1 / (2 * (1 : ℝ))) : ℝ) < 1 / (2 * (1 : ℝ)) by norm_num)
        (PW.bandExt (1 / 2) (fun _ => (1 : ℂ))) 0 = 1 := by
  have h := PW.fourierCoeff_eq_sample (B := 1 / 2) (T := 1) (by norm_num) (by norm_num)
    (by norm_num) (intervalIntegrable_const (c := (1 : ℂ))) 0
  rw [h]
  norm_num [PW.rep, intervalIntegral.integral_const]

-- The sign convention is the sample at `-n * T`: for the non-even profile
-- `ν ↦ ν`, the first coefficient is the representative at `-1`, not at `1`.
example :
    fourierCoeffOn (show (-(1 / (2 * (1 : ℝ))) : ℝ) < 1 / (2 * (1 : ℝ)) by norm_num)
        (PW.bandExt (1 / 2) (fun ν => (ν : ℂ))) 1
      = (1 : ℂ) * PW.rep (1 / 2) (fun ν => (ν : ℂ)) (-1) := by
  have hg : IntervalIntegrable (fun ν => (ν : ℂ)) volume (-(1 / 2)) (1 / 2) :=
    Complex.continuous_ofReal.intervalIntegrable _ _
  simpa using PW.fourierCoeff_eq_sample (B := 1 / 2) (T := 1) (by norm_num) (by norm_num)
    (by norm_num) hg 1

-- Changing a profile off the band changes neither the zero extension nor the
-- representative samples.
example {g h : ℝ → ℂ} (hgh : Set.EqOn g h (Set.Icc (-1 : ℝ) 1)) :
    PW.bandExt 1 g = PW.bandExt 1 h := by
  funext ν
  by_cases hν : ν ∈ Set.Icc (-1 : ℝ) 1
  · simp [PW.bandExt, Set.indicator_of_mem hν, hgh hν]
  · simp [PW.bandExt, Set.indicator_of_notMem hν]

#print axioms PW.rep_add
#print axioms PW.rep_smul
#print axioms PW.rep_continuous
#print axioms PW.norm_rep_le
#print axioms PW.fourierCoeff_eq_sample
