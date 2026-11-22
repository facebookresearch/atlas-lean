/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.GraduallyVariedFlow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Gradually varied flow checks

Consumers of `PhyslibExt.EarthScience.GraduallyVariedFlow` at the shared
data `n = S0 = b = yn = 1` with discharge the rectangular Manning
discharge at the normal depth: one strict sign per mild and steep zone,
a derivative witness, the normal-depth zero, and the totalized value at a
vanishing denominator.

## i. Overview

These are elaboration and boundary checks, not new results. For gravity
`g = 1`, the critical depth is below the normal depth (mild); for
`g = Q ^ 2 / 8` at the same discharge, the critical depth is `2`, above
the normal depth (steep).

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Mild and steep zone signs
- B. Derivative, normal-depth, and critical-depth controls

## iv. References

- `PhyslibExt.EarthScience.GraduallyVariedFlow`
-/

/-- Shared discharge positivity at the witness data. -/
private lemma witness_discharge_pos :
    0 < EarthScience.rectangularDischarge (Real.sqrt 1 / 1) 1 1 := by
  unfold EarthScience.rectangularDischarge
  apply mul_pos (mul_pos (by norm_num [Real.sqrt_one]) (mul_pos one_pos one_pos))
  apply Real.rpow_pos_of_pos
  apply div_pos (mul_pos one_pos one_pos)
  norm_num

/-- The shared witness discharge is below `1`. -/
private lemma witness_discharge_lt_one :
    EarthScience.rectangularDischarge (Real.sqrt 1 / 1) 1 1 < 1 := by
  unfold EarthScience.rectangularDischarge
  norm_num
  exact Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num)

/-- Mild ordering at the witness data: critical depth below `1`. -/
private lemma witness_critical_mild :
    EarthScience.rectangularCriticalDepth
        (EarthScience.rectangularDischarge (Real.sqrt 1 / 1) 1 1 / 1) 1 < 1 := by
  unfold EarthScience.rectangularCriticalDepth
  have h0 := witness_discharge_pos
  have h1 := witness_discharge_lt_one
  apply Real.rpow_lt_one (div_nonneg (sq_nonneg _) zero_le_one) _ (by norm_num)
  have hsq : (EarthScience.rectangularDischarge (Real.sqrt 1 / 1) 1 1 / 1) ^ 2 / 1
      = EarthScience.rectangularDischarge (Real.sqrt 1 / 1) 1 1 *
        EarthScience.rectangularDischarge (Real.sqrt 1 / 1) 1 1 := by ring
  rw [hsq]
  nlinarith

/-- Critical-depth positivity at the witness data. -/
private lemma witness_critical_pos :
    0 < EarthScience.rectangularCriticalDepth
      (EarthScience.rectangularDischarge (Real.sqrt 1 / 1) 1 1 / 1) 1 := by
  unfold EarthScience.rectangularCriticalDepth
  exact Real.rpow_pos_of_pos
    (div_pos (pow_pos (div_pos witness_discharge_pos one_pos) 2) one_pos) _

/-- Mild zones: signs `(+, -, +)` above, between, and below the depths. -/
example :
    0 < EarthScience.gvfSlope 1 1 1
        (EarthScience.rectangularDischarge (Real.sqrt 1 / 1) 1 1) 1 2 ∧
      EarthScience.gvfSlope 1 1 1
        (EarthScience.rectangularDischarge (Real.sqrt 1 / 1) 1 1) 1
        ((EarthScience.rectangularCriticalDepth
          (EarthScience.rectangularDischarge (Real.sqrt 1 / 1) 1 1 / 1) 1 + 1) / 2) < 0 ∧
      0 < EarthScience.gvfSlope 1 1 1
        (EarthScience.rectangularDischarge (Real.sqrt 1 / 1) 1 1) 1
        (EarthScience.rectangularCriticalDepth
          (EarthScience.rectangularDischarge (Real.sqrt 1 / 1) 1 1 / 1) 1 / 2) := by
  have hm := EarthScience.gvfSlope_mild one_pos one_pos one_pos one_pos one_pos
    rfl witness_critical_mild
  have hc := witness_critical_pos
  exact ⟨hm.1 2 (by norm_num),
    hm.2.1 _ (by linarith [witness_critical_mild]) (by linarith [witness_critical_mild]),
    hm.2.2 _ (by linarith) (by linarith)⟩

/-- Steep ordering at the witness data: critical depth is `2`. -/
private lemma witness_critical_steep :
    EarthScience.rectangularCriticalDepth
        (EarthScience.rectangularDischarge (Real.sqrt 1 / 1) 1 1 / 1)
        (EarthScience.rectangularDischarge (Real.sqrt 1 / 1) 1 1 ^ 2 / 8) = 2 := by
  unfold EarthScience.rectangularCriticalDepth
  have h0 : EarthScience.rectangularDischarge (Real.sqrt 1 / 1) 1 1 ≠ 0 :=
    witness_discharge_pos.ne'
  have hs : Real.sqrt 1 / 1 = 1 := by norm_num [Real.sqrt_one]
  have h0' : EarthScience.rectangularDischarge 1 1 1 ≠ 0 := by
    simpa [hs] using h0
  have h8 : (EarthScience.rectangularDischarge (Real.sqrt 1 / 1) 1 1 / 1) ^ 2 /
        (EarthScience.rectangularDischarge (Real.sqrt 1 / 1) 1 1 ^ 2 / 8)
      = (2 : ℝ) ^ (3 : ℕ) := by
    field_simp [h0']
    norm_num
  rw [h8, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- Steep zones: signs `(+, -, +)` above, between, and below the depths. -/
example :
    0 < EarthScience.gvfSlope 1 1 1
        (EarthScience.rectangularDischarge (Real.sqrt 1 / 1) 1 1)
        (EarthScience.rectangularDischarge (Real.sqrt 1 / 1) 1 1 ^ 2 / 8) 3 ∧
      EarthScience.gvfSlope 1 1 1
        (EarthScience.rectangularDischarge (Real.sqrt 1 / 1) 1 1)
        (EarthScience.rectangularDischarge (Real.sqrt 1 / 1) 1 1 ^ 2 / 8) (3 / 2) < 0 ∧
      0 < EarthScience.gvfSlope 1 1 1
        (EarthScience.rectangularDischarge (Real.sqrt 1 / 1) 1 1)
        (EarthScience.rectangularDischarge (Real.sqrt 1 / 1) 1 1 ^ 2 / 8) (1 / 2) := by
  have hg : (0 : ℝ) < EarthScience.rectangularDischarge (Real.sqrt 1 / 1) 1 1 ^ 2 / 8 := by
    have h0 := witness_discharge_pos
    positivity
  have hs := EarthScience.gvfSlope_steep one_pos one_pos one_pos hg one_pos rfl
    (by rw [witness_critical_steep]; norm_num)
  rw [witness_critical_steep] at hs
  exact ⟨hs.1 3 (by norm_num), hs.2.1 _ (by norm_num) (by norm_num),
    hs.2.2 _ (by norm_num) (by norm_num)⟩

/-- Derivative witness: a linear profile through depth `2` with the
declared slope has derivative sign `1`. -/
example : SignType.sign
    (deriv (fun t : ℝ => 2 + EarthScience.gvfSlope 1 1 1
      (EarthScience.rectangularDischarge (Real.sqrt 1 / 1) 1 1) 1 2 * t) 0) = 1 := by
  have hmild : EarthScience.rectangularCriticalDepth
      (EarthScience.rectangularDischarge 1 1 1) 1 < 1 := by
    have hs : Real.sqrt 1 / 1 = 1 := by norm_num [Real.sqrt_one]
    simpa [hs] using witness_critical_mild
  have hY : HasDerivAt
      (fun t : ℝ => 2 + EarthScience.gvfSlope 1 1 1
        (EarthScience.rectangularDischarge (Real.sqrt 1 / 1) 1 1) 1 2 * t)
      (EarthScience.gvfSlope 1 1 1
        (EarthScience.rectangularDischarge (Real.sqrt 1 / 1) 1 1) 1
        ((fun t : ℝ => 2 + EarthScience.gvfSlope 1 1 1
          (EarthScience.rectangularDischarge (Real.sqrt 1 / 1) 1 1) 1 2 * t) 0)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul
      (EarthScience.gvfSlope 1 1 1
        (EarthScience.rectangularDischarge (Real.sqrt 1 / 1) 1 1) 1 2)).const_add 2
  have h := EarthScience.sign_deriv_of_gvf one_pos one_pos one_pos one_pos one_pos
    rfl hY (by norm_num) (by simp; linarith [hmild])
  rw [h]
  simp
  rw [sign_pos (by linarith [hmild] :
    (0 : ℝ) < 2 - EarthScience.rectangularCriticalDepth
      (EarthScience.rectangularDischarge 1 1 1) 1)]

/-- At the normal depth, the slope sign is `0`. -/
example : SignType.sign (EarthScience.gvfSlope 1 1 1
    (EarthScience.rectangularDischarge (Real.sqrt 1 / 1) 1 1) 1 1) = 0 := by
  rw [EarthScience.gvfSlope_normalDepth one_pos one_pos one_pos one_pos one_pos rfl
    (ne_of_gt witness_critical_mild)]
  simp

/-- Negative control at a vanishing denominator: totalized division gives
the junk slope `0`, which the physical results exclude. -/
example {n S0 b Q g y : ℝ} (h : 1 - (Q / b) ^ 2 / (g * y ^ 3) = 0) :
    EarthScience.gvfSlope n S0 b Q g y = 0 := by
  simp [EarthScience.gvfSlope, h]
