/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Physical failure events: critical crack length in an LEFM model

## i. Overview

This file starts the physical-failure-event layer: deterministic material
failure thresholds stated as explicit model inputs, whose algebraic
consequences are proved and can later be composed with lifetime and
reliability models. The first model is the standard linear-elastic
fracture mechanics (LEFM) mode-I stress intensity
`K_I(a) = Y * σ * √(π * a)` for a constant geometry factor `Y`, peak
tensile stress `σ`, and crack length `a ≥ 0`, together with the critical
crack length at which `K_I` reaches the fracture toughness `K_IC`.

The stress-intensity formula is an adopted model input with a
small-scale-yielding validity regime. Nothing here validates the model
empirically, and `σ` is a peak tensile stress, not a fatigue stress range.

## ii. Key results

- `Reliability.criticalCrackLength_pos`: the critical crack length is
  positive for positive toughness, geometry factor, and stress.
- `Reliability.modeIStressIntensity_criticalCrackLength`: `K_I` equals
  `K_IC` exactly at the critical crack length.
- `Reliability.modeIStressIntensity_lt_iff_lt_criticalCrackLength`:
  subcriticality `K_I(a) < K_IC` is equivalent to `a < a_c`.
- `Reliability.crackFailure_iff_criticalCrackLength_le`: the
  equality-inclusive failure event is equivalent to `a_c ≤ a`.

## iii. Table of contents

- A. Mode-I stress intensity and the critical crack length

## iv. References

- N. E. Dowling, *Mechanical Behavior of Materials: Engineering Methods
  for Deformation, Fracture, and Fatigue*, 4th ed., Pearson (2013): the
  mode-I stress intensity model and the critical-crack condition
  `K_I = K_IC` used here.

## A. Mode-I stress intensity and the critical crack length

-/

@[expose] public section

namespace Reliability

/-- Mode-I stress intensity factor in the adopted linear-elastic fracture
mechanics (LEFM) model `K_I(a) = Y * σ * √(π * a)`, where `Y` is a constant
geometry factor, `σ` is the peak tensile stress, and `a` is the crack length.
This formula is a model input with a small-scale-yielding validity regime;
the theorems below are its algebraic consequences, not an experimental
validation of the model. The formula is intended for `0 ≤ a`. -/
noncomputable def modeIStressIntensity (Y σ a : ℝ) : ℝ :=
  Y * σ * Real.sqrt (Real.pi * a)

/-- Critical crack length `a_c = (K_IC / (Y * σ)) ^ 2 / π` in the same LEFM
model: the crack length at which `modeIStressIntensity` reaches the fracture
toughness `K_IC`. -/
noncomputable def criticalCrackLength (KIC Y σ : ℝ) : ℝ :=
  (KIC / (Y * σ)) ^ 2 / Real.pi

/-- Equality-inclusive crack failure in this model: the mode-I stress
intensity demand reaches the fracture toughness. -/
def crackFailure (KIC Y σ a : ℝ) : Prop :=
  KIC ≤ modeIStressIntensity Y σ a

theorem modeIStressIntensity_zero (Y σ : ℝ) :
    modeIStressIntensity Y σ 0 = 0 := by
  simp [modeIStressIntensity]

theorem criticalCrackLength_pos {KIC Y σ : ℝ} (hKIC : 0 < KIC) (hY : 0 < Y)
    (hσ : 0 < σ) :
    0 < criticalCrackLength KIC Y σ := by
  unfold criticalCrackLength
  exact div_pos (pow_pos (div_pos hKIC (mul_pos hY hσ)) 2) Real.pi_pos

theorem modeIStressIntensity_criticalCrackLength {KIC Y σ : ℝ}
    (hKIC : 0 < KIC) (hY : 0 < Y) (hσ : 0 < σ) :
    modeIStressIntensity Y σ (criticalCrackLength KIC Y σ) = KIC := by
  have hYσ : 0 < Y * σ := mul_pos hY hσ
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hYσ' : Y * σ ≠ 0 := ne_of_gt hYσ
  have hK : 0 < KIC / (Y * σ) := div_pos hKIC hYσ
  unfold modeIStressIntensity criticalCrackLength
  rw [mul_comm Real.pi _, div_mul_cancel₀ _ hπ, Real.sqrt_sq (le_of_lt hK),
    mul_comm (Y * σ) _, div_mul_cancel₀ _ hYσ']

theorem modeIStressIntensity_lt_iff_lt_criticalCrackLength {KIC Y σ a : ℝ}
    (hKIC : 0 < KIC) (hY : 0 < Y) (hσ : 0 < σ) (ha : 0 ≤ a) :
    modeIStressIntensity Y σ a < KIC ↔ a < criticalCrackLength KIC Y σ := by
  have hYσ : 0 < Y * σ := mul_pos hY hσ
  have hK : 0 < KIC / (Y * σ) := div_pos hKIC hYσ
  unfold modeIStressIntensity criticalCrackLength
  rw [mul_comm (Y * σ) _, ← lt_div_iff₀ hYσ,
    Real.sqrt_lt (mul_nonneg (le_of_lt Real.pi_pos) ha) (le_of_lt hK),
    mul_comm Real.pi a, lt_div_iff₀ Real.pi_pos]

theorem crackFailure_iff_criticalCrackLength_le {KIC Y σ a : ℝ}
    (hKIC : 0 < KIC) (hY : 0 < Y) (hσ : 0 < σ) (ha : 0 ≤ a) :
    crackFailure KIC Y σ a ↔ criticalCrackLength KIC Y σ ≤ a := by
  unfold crackFailure
  rw [← not_lt, ← not_lt,
    modeIStressIntensity_lt_iff_lt_criticalCrackLength hKIC hY hσ ha]

end Reliability
