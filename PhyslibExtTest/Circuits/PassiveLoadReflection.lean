/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.PassiveLoadReflection
import Mathlib.Tactic.NormNum

@[expose] public section

open PhyslibExt.Circuits.LineWaveTermination
open PhyslibExt.Circuits.PassiveLoadReflection
open PhyslibExt.Circuits.RMSAveragePower

namespace PhyslibExtTest.Circuits.PassiveLoadReflection

/-- A resistive load `3` on a unit line is passive: the literal ratio has
norm at most `1`. -/
example : ‖((3 : ℂ) - ((1 : ℝ) : ℂ)) / ((3 : ℂ) + ((1 : ℝ) : ℂ))‖ ≤ 1 :=
  (norm_reflection_le_one_iff 3 1 (by norm_num) (by norm_num)).mpr (by norm_num)

/-- The same load is strictly inside the unit disk. -/
example : ‖reflectionCoefficient 3 1‖ < 1 :=
  (norm_reflectionCoefficient_lt_one_iff 3 1 (by norm_num) (by norm_num)).mpr
    (by norm_num)

/-- Its real coefficient is `1 / 2`, below `1` in absolute value. -/
example : resistiveReflection 3 1 = 1 / 2 := by
  unfold resistiveReflection
  norm_num

example : |resistiveReflection 3 1| < 1 :=
  abs_resistiveReflection_lt_one_of_pos 3 1 (by norm_num) (by norm_num)

/-- A pure reactance `2 i` on a unit line reflects with norm exactly `1`. -/
example : ‖reflectionCoefficient (Complex.I * ((2 : ℝ) : ℂ)) 1‖ = 1 :=
  norm_reflectionCoefficient_pure_reactance 2 1 (by norm_num)

/-- A negative resistance `-1/2` on a unit line reflects with norm above
`1`, in both the complex and the resistive forms. -/
example : 1 < ‖reflectionCoefficient ((-1 / 2 : ℝ) : ℂ) 1‖ :=
  (one_lt_norm_reflectionCoefficient_iff _ 1 (by norm_num)
    (by rw [← Complex.ofReal_add]; norm_num)).mpr (by simp; norm_num)

example : 1 < |resistiveReflection (-1 / 2) 1| :=
  one_lt_abs_resistiveReflection_of_neg (-1 / 2) 1 (by norm_num) (by norm_num)
    (by norm_num)

/-- The load `-1/2` is not passive: the passivity bound fails. -/
example : ¬ ‖reflectionCoefficient ((-1 / 2 : ℝ) : ℂ) 1‖ ≤ 1 := by
  rw [norm_reflectionCoefficient_le_one_iff _ 1 (by norm_num)
    (by rw [← Complex.ofReal_add]; norm_num)]
  simp
  norm_num

/-- Excluded load `ZL = -1` on a unit line: the norm bound holds and the
real part is negative, so the unguarded criterion is false there. -/
example : ‖reflectionCoefficient (-((1 : ℝ) : ℂ)) 1‖ ≤ 1 ∧
    (-((1 : ℝ) : ℂ)).re < 0 :=
  reflection_criterion_fails_at_excluded_load 1 (by norm_num)

example : ¬ (‖reflectionCoefficient (-((1 : ℝ) : ℂ)) 1‖ ≤ 1 →
    0 ≤ (-((1 : ℝ) : ℂ)).re) := by
  intro h
  obtain ⟨hle, hneg⟩ := reflection_criterion_fails_at_excluded_load 1 (by norm_num)
  exact absurd (h hle) (not_le.mpr hneg)

/-- Matched and short-circuit loads on a unit line. -/
example : reflectionCoefficient ((1 : ℝ) : ℂ) 1 = 0 :=
  reflectionCoefficient_matched 1 (by norm_num)

example : reflectionCoefficient 0 1 = -1 :=
  reflectionCoefficient_short 1 (by norm_num)

/-- Power balance at the load `1 + i` on a unit line: `1 - |Gamma| ^ 2`
equals `4 / 5`. -/
example : 1 - ‖reflectionCoefficient (1 + Complex.I) 1‖ ^ 2 = 4 / 5 := by
  have hsum : (1 + Complex.I) + ((1 : ℝ) : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  rw [one_sub_norm_sq_reflectionCoefficient _ 1 hsum, ← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply]
  norm_num

/-- Wave form, passive: incident amplitude `2`, reflected amplitude `1`,
load `3`, load voltage `3` and current `1` on a unit line. -/
example : ‖(1 : ℂ)‖ ≤ ‖(2 : ℂ)‖ :=
  (norm_reflected_le_norm_incident_iff 3 1 2 1 3 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)).mpr (by norm_num)

/-- Wave form, active: incident amplitude `1`, reflected amplitude `-3`,
load `-1/2`, load voltage `-2` and current `4` on a unit line. -/
example : ¬ ‖(-3 : ℂ)‖ ≤ ‖(1 : ℂ)‖ := by
  rw [norm_reflected_le_norm_incident_iff (-2) 4 1 (-3) (-1 / 2) 1 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- The bundled criterion at load `3` on a unit line. -/
example : ‖((3 : ℂ) - ((1 : ℝ) : ℂ)) / ((3 : ℂ) + ((1 : ℝ) : ℂ))‖ ≤ 1 :=
  ((passiveLoadReflection 3 1 (by norm_num) (by norm_num)).1).mpr (by norm_num)

/-- Load power for the passive wave: `3` from the amplitudes and `3` from
the load law. -/
example : ((3 : ℂ) * (starRingEnd ℂ) 1).re = (‖(2 : ℂ)‖ ^ 2 - ‖(1 : ℂ)‖ ^ 2) / 1 :=
  load_power_eq_incident_sub_reflected 3 1 2 1 1 (by norm_num) (by norm_num)
    (by norm_num)

example : ((3 : ℂ) * (starRingEnd ℂ) 1).re = (3 : ℂ).re * ‖(1 : ℂ)‖ ^ 2 :=
  load_power_eq_re_mul_norm_sq 3 1 3 (by norm_num)

/-- A unit forward wave with no reflection on a unit line has
`Re (V * conj I) = 1`. Read as RMS phasors, the average load power is
`1`. -/
example :
    (∫ t in (0 : ℝ)..(0 + 2 * Real.pi / 1),
      rmsWaveform 1 1 t * rmsWaveform 1 1 t) / (2 * Real.pi / 1) = 1 := by
  rw [average_rmsWaveform_load_power_eq_incident_sub_reflected 1 1 1 0 1 1
    (by norm_num) 0 (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- Read as peak phasors, the same wave averages to `1 / 2`. -/
example :
    (∫ t in (0 : ℝ)..(0 + 2 * Real.pi / 1),
      peakWaveform 1 1 t * peakWaveform 1 1 t) / (2 * Real.pi / 1) = 1 / 2 := by
  rw [average_peakWaveform_load_power_eq_incident_sub_reflected 1 1 1 0 1 1
    (by norm_num) 0 (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- Instantaneous reflection at resistor `3` on a unit line with
`vplus t = 2 * t` and `vminus t = t`. -/
example (t : ℝ) : t = resistiveReflection 3 1 * (2 * t) :=
  instantaneous_resistive_reflection 3 1 (by norm_num) (by norm_num)
    (fun t => 2 * t) (fun t => t) (fun t => 3 * t) (fun t => t)
    (fun t => by ring) (fun t => by ring) (fun t => by ring) t

end PhyslibExtTest.Circuits.PassiveLoadReflection
