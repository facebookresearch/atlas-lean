/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Sabine reverberation decay

## i. Overview

In the Sabine diffuse-field model, the acoustic energy in a room of
volume `V` with equivalent absorption area `A_abs` and sound speed
`c` decays exponentially with rate `k = c * A_abs / (4 * V)`
(`sabineEnergy E0 k t = E0 * exp (-k * t)`). The reverberation time
`T60`, at which the energy has fallen by 60 dB (a factor `10 ^ 6`
in energy), is `24 * log 10 * V / (c * A_abs)`, independent of the
initial energy `E0`. The 60 dB threshold uses the energy (10 log)
convention.

## ii. Key results

- `Acoustics.sabineRate_pos`, `Acoustics.sabineT60_pos`:
  positivity of the decay rate and of `T60`.
- `Acoustics.sabine_energy_at_T60`: the energy at `T60` is
  `E0 / 10 ^ 6`.
- `Acoustics.sabine_ratio_at_T60`: the 60 dB energy ratio,
  independent of `E0`.
- `Acoustics.sabine_T60_unique`: `T60` is the unique nonnegative
  threshold time.

## iii. Table of contents

- A. Sabine rate, reverberation time, and the 60 dB threshold

## iv. References

- W. C. Sabine, *Collected Papers on Acoustics*, 1922
  (reverberation time of a diffuse room).
-/

@[expose] public section

namespace Acoustics

/-! ## A. Sabine rate, reverberation time, and the 60 dB threshold -/

/-- Energy decay rate in the Sabine model. Physically meaningful
for `0 < V`, `0 < c`, `0 < A_abs`; outside that domain the formula
uses Lean's totalized division. -/
noncomputable def sabineRate (V c A_abs : ℝ) : ℝ := c * A_abs / (4 * V)

/-- Reverberation time `T60` in the Sabine model. Physically
meaningful for `0 < V`, `0 < c`, `0 < A_abs`; outside that domain
the formula uses Lean's totalized division. -/
noncomputable def sabineT60 (V c A_abs : ℝ) : ℝ :=
  24 * Real.log 10 * V / (c * A_abs)

/-- Sabine energy decay: initial energy `E0` decaying at rate
`k`, `E0 * exp (-k * t)`. Defined locally in the acoustics API so
that downstream users do not acquire an unrelated kinetics
dependency. -/
noncomputable def sabineEnergy (E0 k t : ℝ) : ℝ :=
  E0 * Real.exp (-k * t)

/-- The Sabine decay rate is positive. -/
lemma sabineRate_pos {V c A_abs : ℝ} (hV : 0 < V) (hc : 0 < c)
    (hA : 0 < A_abs) : 0 < sabineRate V c A_abs := by
  unfold sabineRate
  positivity

/-- The reverberation time `T60` is positive. -/
lemma sabineT60_pos {V c A_abs : ℝ} (hV : 0 < V) (hc : 0 < c)
    (hA : 0 < A_abs) : 0 < sabineT60 V c A_abs := by
  have hlog : 0 < Real.log 10 := Real.log_pos (by norm_num)
  unfold sabineT60
  positivity

/-- The exponential decay factor at `T60` equals `1 / 10 ^ 6`. -/
theorem sabine_exp_at_T60 {V c A_abs : ℝ} (hV : 0 < V) (hc : 0 < c)
    (hA : 0 < A_abs) :
    Real.exp (-(sabineRate V c A_abs) * sabineT60 V c A_abs) = 1 / 10 ^ 6 := by
  have hVne : V ≠ 0 := ne_of_gt hV
  have hcne : c ≠ 0 := ne_of_gt hc
  have hAne : A_abs ≠ 0 := ne_of_gt hA
  have hkt : sabineRate V c A_abs * sabineT60 V c A_abs = 6 * Real.log 10 := by
    unfold sabineRate sabineT60
    have h4V : (4 : ℝ) * V ≠ 0 := mul_ne_zero (by norm_num) hVne
    have hcA : c * A_abs ≠ 0 := mul_ne_zero hcne hAne
    field_simp
    ring
  have harg : -(sabineRate V c A_abs) * sabineT60 V c A_abs = -(6 * Real.log 10) := by
    rw [← hkt]
    ring
  rw [harg, Real.exp_neg]
  have hexp6 : Real.exp (6 * Real.log 10) = (10 : ℝ) ^ 6 := by
    have hcast : (6 : ℝ) = ((6 : ℕ) : ℝ) := by norm_num
    rw [hcast, Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [hexp6, one_div]

/-- At `T60` the Sabine energy has fallen to `E0 / 10 ^ 6`. -/
theorem sabine_energy_at_T60 {E0 V c A_abs : ℝ} (hV : 0 < V)
    (hc : 0 < c) (hA : 0 < A_abs) :
    sabineEnergy E0 (sabineRate V c A_abs) (sabineT60 V c A_abs)
      = E0 / 10 ^ 6 := by
  unfold sabineEnergy
  rw [sabine_exp_at_T60 hV hc hA]
  ring

/-- The 60 dB energy ratio at `T60` is `1 / 10 ^ 6`, independent
of the initial energy. -/
lemma sabine_ratio_at_T60 {E0 V c A_abs : ℝ} (hE0 : E0 ≠ 0)
    (hV : 0 < V) (hc : 0 < c) (hA : 0 < A_abs) :
    sabineEnergy E0 (sabineRate V c A_abs) (sabineT60 V c A_abs) / E0
      = 1 / 10 ^ 6 := by
  have h106 : ((10 : ℝ) ^ 6) ≠ 0 := by norm_num
  rw [sabine_energy_at_T60 hV hc hA]
  field_simp

/-- `T60` is the unique nonnegative time at which the Sabine
energy equals `E0 / 10 ^ 6`. -/
lemma sabine_T60_unique {E0 V c A_abs t : ℝ} (hE0 : 0 < E0)
    (hV : 0 < V) (hc : 0 < c) (hA : 0 < A_abs) (ht : 0 ≤ t)
    (h : sabineEnergy E0 (sabineRate V c A_abs) t = E0 / 10 ^ 6) :
    t = sabineT60 V c A_abs := by
  have ht' := ht
  have hE0ne : E0 ≠ 0 := ne_of_gt hE0
  have hk_pos : 0 < sabineRate V c A_abs := sabineRate_pos hV hc hA
  have hkne : -(sabineRate V c A_abs) ≠ 0 := neg_ne_zero.mpr (ne_of_gt hk_pos)
  unfold sabineEnergy at h
  have hE : Real.exp (-(sabineRate V c A_abs) * t) = 1 / 10 ^ 6 := by
    have h' : E0 * Real.exp (-(sabineRate V c A_abs) * t) = E0 * (1 / 10 ^ 6) := by
      rw [h]
      ring
    exact mul_left_cancel₀ hE0ne h'
  have hT : Real.exp (-(sabineRate V c A_abs) * sabineT60 V c A_abs) = 1 / 10 ^ 6 :=
    sabine_exp_at_T60 hV hc hA
  have hinj := Real.exp_strictMono.injective (hE.trans hT.symm)
  exact mul_left_cancel₀ hkne hinj

end Acoustics
