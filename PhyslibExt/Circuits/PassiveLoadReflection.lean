/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.LineWaveTermination
public import PhyslibExt.Circuits.RMSAveragePower
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Passive loads and the reflection-coefficient bound

## i. Overview

A line of real characteristic impedance `Z0 > 0` terminated in a
complex load impedance `ZL` reflects with coefficient
`Gamma = (ZL - Z0) / (ZL + Z0)`, the canonical
`PhyslibExt.Circuits.LineWaveTermination.reflectionCoefficient`. For
`ZL + Z0 != 0` the load is passive, `Re ZL >= 0`, exactly when
`|Gamma| <= 1`. The proof rests on the identity
`1 - |Gamma| ^ 2 = 4 * Z0 * Re ZL / |ZL + Z0| ^ 2`, obtained from
`|ZL + Z0| ^ 2 - |ZL - Z0| ^ 2 = 4 * Z0 * Re ZL` by expanding both
squared norms in real and imaginary parts. Its sign gives the bound,
the strict form `|Gamma| < 1 iff Re ZL > 0`, the lossless boundary
`|Gamma| = 1 iff Re ZL = 0`, and the active case
`|Gamma| > 1 iff Re ZL < 0`.

For an actual wave at the load plane, the load relations
`V = Aplus + Aminus`, `I = (Aplus - Aminus) / Z0` and `V = ZL * I`
with nonzero incident amplitude `Aplus` make the amplitude ratio
`Aminus / Aplus` equal to `Gamma`
(`PhyslibExt.Circuits.LineWaveTermination.load_reflectionCoefficient_eq`),
so `|Aminus| <= |Aplus|` exactly when `Re ZL >= 0`. The real part of
the complex power ties the two forms together:
`Re (V * conj I) = (|Aplus| ^ 2 - |Aminus| ^ 2) / Z0 = Re ZL * |I| ^ 2`.
This real part is the time-averaged load power only when `V` and `I`
are RMS phasors
(`PhyslibExt.Circuits.RMSAveragePower.average_rmsWaveform_mul_rmsWaveform`);
for peak phasors the period average carries an extra factor `1 / 2`
(`PhyslibExt.Circuits.RMSAveragePower.average_peakWaveform_mul_peakWaveform`).
Both readings are stated for each form.

A resistive load `R` has the real coefficient
`Gamma_R = (R - Z0) / (R + Z0)`, and for such a load the reflection
holds instant by instant: `vminus t = Gamma_R * vplus t`. This file
does not model a load as a function of frequency; for the inductive
load `i * omega * L` it records only that the coefficient can change
with `omega` (one example at two frequencies), so that load has no
such frequency-independent time-domain reading. The guard `ZL + Z0 != 0`
cannot be dropped: at `ZL = -Z0` the total division in Lean gives
`Gamma = 0`, so the bound holds while `Re ZL < 0`. A zero load (short
circuit) lies inside the domain; an infinite (open) load is not a
value of `ZL`.

## ii. Key results

- `one_sub_norm_sq_reflectionCoefficient`: the power-balance identity
  for `1 - |Gamma| ^ 2`.
- `norm_reflection_le_one_iff` and
  `norm_reflectionCoefficient_le_one_iff`: `|Gamma| <= 1` if and only if
  `Re ZL >= 0`.
- `norm_reflected_le_norm_incident_iff`: the wave-amplitude form of the
  criterion.
- `load_power_eq_incident_sub_reflected` and
  `load_power_eq_re_mul_norm_sq`: the two expressions for the real
  part `Re (V * conj I)` of the complex power at the load plane.
- `average_rmsWaveform_load_power_eq_incident_sub_reflected`,
  `average_rmsWaveform_load_power_eq_re_mul_norm_sq` and their
  `average_peakWaveform_*` counterparts: the time-averaged load power
  for RMS phasors, and half of it for peak phasors.
- `passiveLoadReflection`: the ratio and wave-amplitude criteria
  together.
- `instantaneous_resistive_reflection`: time-domain reflection at a
  resistive load.

## iii. Table of contents

- A. Norm identity and the passivity criterion
- B. Wave reflection and load power
- C. Resistive loads
- D. Special loads and the excluded load

## iv. References

- D. M. Pozar, *Microwave Engineering*, fourth edition, Wiley, 2012,
  Chapter 2: the terminated lossless transmission line, the load
  reflection coefficient, and power delivered to the load.

## A. Norm identity and the passivity criterion
-/

@[expose] public section

namespace PhyslibExt.Circuits.PassiveLoadReflection

open PhyslibExt.Circuits.LineWaveTermination
open PhyslibExt.Circuits.RMSAveragePower

/-- Power-balance identity:
`1 - |Gamma| ^ 2 = 4 * Z0 * Re ZL / |ZL + Z0| ^ 2`. -/
theorem one_sub_norm_sq_reflectionCoefficient (ZL : ℂ) (Z0 : ℝ)
    (hsum : ZL + (Z0 : ℂ) ≠ 0) :
    1 - ‖reflectionCoefficient ZL Z0‖ ^ 2 =
      4 * Z0 * ZL.re / ‖ZL + (Z0 : ℂ)‖ ^ 2 := by
  have hD : ‖ZL + (Z0 : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr hsum
  have hD2 : (0:ℝ) < ‖ZL + (Z0 : ℂ)‖ ^ 2 := sq_pos_of_ne_zero hD
  have hsq : ‖ZL + (Z0:ℂ)‖^2 - ‖ZL - (Z0:ℂ)‖^2 = 4*Z0*ZL.re := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.sub_re, Complex.add_im,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  unfold reflectionCoefficient
  rw [norm_div, div_pow, eq_div_iff (ne_of_gt hD2),
    sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hD2)]
  exact hsq

/-- For real `Z0 > 0` and `ZL + Z0 != 0`,
`‖(ZL - Z0) / (ZL + Z0)‖ <= 1` if and only if `Re ZL >= 0`. -/
theorem norm_reflection_le_one_iff (ZL : ℂ) (Z0 : ℝ) (hZ0 : 0 < Z0)
    (hsum : ZL + (Z0 : ℂ) ≠ 0) :
    ‖(ZL - (Z0 : ℂ)) / (ZL + (Z0 : ℂ))‖ ≤ 1 ↔ 0 ≤ ZL.re := by
  change ‖reflectionCoefficient ZL Z0‖ ≤ 1 ↔ 0 ≤ ZL.re
  have hD : ‖ZL + (Z0 : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr hsum
  have hD2 : (0:ℝ) < ‖ZL + (Z0 : ℂ)‖ ^ 2 := sq_pos_of_ne_zero hD
  have h4Z0 : (0:ℝ) < 4 * Z0 := by linarith
  have hid := one_sub_norm_sq_reflectionCoefficient ZL Z0 hsum
  have hnn : (0:ℝ) ≤ ‖reflectionCoefficient ZL Z0‖ := norm_nonneg _
  have hsq1 : ‖reflectionCoefficient ZL Z0‖ ≤ 1
      ↔ ‖reflectionCoefficient ZL Z0‖^2 ≤ 1 := (sq_le_one_iff₀ hnn).symm
  rw [hsq1, ← sub_nonneg, hid, le_div_iff₀ hD2, zero_mul,
    mul_nonneg_iff_of_pos_left h4Z0]

/-- The passivity criterion stated with `reflectionCoefficient`. -/
theorem norm_reflectionCoefficient_le_one_iff (ZL : ℂ) (Z0 : ℝ) (hZ0 : 0 < Z0)
    (hsum : ZL + (Z0 : ℂ) ≠ 0) :
    ‖reflectionCoefficient ZL Z0‖ ≤ 1 ↔ 0 ≤ ZL.re := by
  exact norm_reflection_le_one_iff ZL Z0 hZ0 hsum

/-- Strict form: `|Gamma| < 1` if and only if `Re ZL > 0`. -/
lemma norm_reflectionCoefficient_lt_one_iff (ZL : ℂ) (Z0 : ℝ) (hZ0 : 0 < Z0)
    (hsum : ZL + (Z0 : ℂ) ≠ 0) :
    ‖reflectionCoefficient ZL Z0‖ < 1 ↔ 0 < ZL.re := by
  have hD : ‖ZL + (Z0 : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr hsum
  have hD2 : (0:ℝ) < ‖ZL + (Z0 : ℂ)‖ ^ 2 := sq_pos_of_ne_zero hD
  have h4Z0 : (0:ℝ) < 4 * Z0 := by linarith
  have hid := one_sub_norm_sq_reflectionCoefficient ZL Z0 hsum
  have hnn : (0:ℝ) ≤ ‖reflectionCoefficient ZL Z0‖ := norm_nonneg _
  have hsq1 : ‖reflectionCoefficient ZL Z0‖ < 1
      ↔ ‖reflectionCoefficient ZL Z0‖^2 < 1 := (sq_lt_one_iff₀ hnn).symm
  rw [hsq1, ← sub_pos, hid, lt_div_iff₀ hD2, zero_mul,
    mul_pos_iff_of_pos_left h4Z0]

/-- Lossless boundary: `|Gamma| = 1` if and only if `Re ZL = 0`. -/
lemma norm_reflectionCoefficient_eq_one_iff (ZL : ℂ) (Z0 : ℝ) (hZ0 : 0 < Z0)
    (hsum : ZL + (Z0 : ℂ) ≠ 0) :
    ‖reflectionCoefficient ZL Z0‖ = 1 ↔ ZL.re = 0 := by
  have hnn : (0:ℝ) ≤ ‖reflectionCoefficient ZL Z0‖ := norm_nonneg _
  have hsq1 : ‖reflectionCoefficient ZL Z0‖ ^ 2 = 1
      ↔ ‖reflectionCoefficient ZL Z0‖ = 1 := by
    rw [sq_eq_one_iff]
    constructor
    · rintro (h | h)
      · exact h
      · linarith
    · intro h
      exact Or.inl h
  have hid := one_sub_norm_sq_reflectionCoefficient ZL Z0 hsum
  have hD2 : (0:ℝ) < ‖ZL + (Z0 : ℂ)‖ ^ 2 :=
    sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hsum)
  have h4Z0 : (0:ℝ) < 4 * Z0 := by linarith
  have hsub : (1:ℝ) - ‖reflectionCoefficient ZL Z0‖^2 = 0
      ↔ ‖reflectionCoefficient ZL Z0‖^2 = 1 := by
    constructor <;> intro h <;> linarith
  rw [← hsq1, ← hsub, hid, div_eq_zero_iff, mul_eq_zero]
  simp [ne_of_gt hD2, ne_of_gt h4Z0]

/-- Active loads: `|Gamma| > 1` if and only if `Re ZL < 0`. -/
lemma one_lt_norm_reflectionCoefficient_iff (ZL : ℂ) (Z0 : ℝ) (hZ0 : 0 < Z0)
    (hsum : ZL + (Z0 : ℂ) ≠ 0) :
    1 < ‖reflectionCoefficient ZL Z0‖ ↔ ZL.re < 0 := by
  have hle := norm_reflectionCoefficient_le_one_iff ZL Z0 hZ0 hsum
  constructor
  · intro hlt
    by_contra hcon
    have hnn : (0:ℝ) ≤ ZL.re := not_lt.mp hcon
    have := hle.mpr hnn
    linarith
  · intro hlt
    by_contra hcon
    have hle' : ‖reflectionCoefficient ZL Z0‖ ≤ 1 := not_lt.mp hcon
    have := hle.mp hle'
    linarith

/-! ## B. Wave reflection and load power -/

/-- Real part of the complex power at the load plane from the wave
amplitudes: `Re (V * conj I) = (|Aplus| ^ 2 - |Aminus| ^ 2) / Z0`. This
is the time-averaged load power only for RMS phasors
(`average_rmsWaveform_load_power_eq_incident_sub_reflected`); for peak
phasors the average is half of it
(`average_peakWaveform_load_power_eq_incident_sub_reflected`). -/
theorem load_power_eq_incident_sub_reflected (V I Aplus Aminus : ℂ) (Z0 : ℝ)
    (hZ0 : 0 < Z0) (hV : V = Aplus + Aminus)
    (hI : I = (Aplus - Aminus) / (Z0 : ℂ)) :
    (V * (starRingEnd ℂ) I).re = (‖Aplus‖ ^ 2 - ‖Aminus‖ ^ 2) / Z0 := by
  have hdiv : ∀ w : ℂ, (w / (Z0:ℂ)).re = w.re / Z0 := by
    intro w
    rw [div_eq_mul_inv, ← Complex.ofReal_inv]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      div_eq_mul_inv]
  have hZ0ne : Z0 ≠ 0 := ne_of_gt hZ0
  rw [hV, hI, eq_div_iff hZ0ne]
  simp only [map_div₀, map_sub, Complex.conj_ofReal]
  rw [← mul_div_assoc, hdiv, div_mul_cancel₀ _ hZ0ne]
  have hca : (Aplus * (starRingEnd ℂ) Aplus).re = ‖Aplus‖^2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  have hcb : (Aminus * (starRingEnd ℂ) Aminus).re = ‖Aminus‖^2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  have hconj : Aminus * (starRingEnd ℂ) Aplus
      = (starRingEnd ℂ) (Aplus * (starRingEnd ℂ) Aminus) := by
    simp only [starRingEnd_apply, star_mul, star_star]
  have hcross : (Aminus * (starRingEnd ℂ) Aplus).re
      = (Aplus * (starRingEnd ℂ) Aminus).re := by
    rw [hconj, Complex.conj_re]
  have hexp : (Aplus + Aminus) * ((starRingEnd ℂ) Aplus - (starRingEnd ℂ) Aminus)
      = Aplus * (starRingEnd ℂ) Aplus - Aplus * (starRingEnd ℂ) Aminus
        + (Aminus * (starRingEnd ℂ) Aplus - Aminus * (starRingEnd ℂ) Aminus) := by
    ring
  rw [hexp]
  simp only [Complex.add_re, Complex.sub_re]
  linear_combination hca - hcb + hcross

/-- Real part of the complex power at the load plane from the load law:
`Re (V * conj I) = Re ZL * |I| ^ 2`. This is the time-averaged load
power only for RMS phasors
(`average_rmsWaveform_load_power_eq_re_mul_norm_sq`); for peak phasors
the average is half of it
(`average_peakWaveform_load_power_eq_re_mul_norm_sq`). -/
theorem load_power_eq_re_mul_norm_sq (V I ZL : ℂ) (hload : V = ZL * I) :
    (V * (starRingEnd ℂ) I).re = ZL.re * ‖I‖ ^ 2 := by
  have hIc : I * (starRingEnd ℂ) I = ((‖I‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hload, mul_assoc, hIc]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- Time-averaged load power for RMS phasors: under the load-plane
relations, the average of the product of the RMS voltage and current
waveforms over any complete period is
`(|Aplus| ^ 2 - |Aminus| ^ 2) / Z0`. -/
theorem average_rmsWaveform_load_power_eq_incident_sub_reflected
    (V I Aplus Aminus : ℂ) (Z0 ω : ℝ) (hω : 0 < ω) (a : ℝ)
    (hZ0 : 0 < Z0) (hV : V = Aplus + Aminus)
    (hI : I = (Aplus - Aminus) / (Z0 : ℂ)) :
    (∫ t in a..(a + 2 * Real.pi / ω),
      rmsWaveform V ω t * rmsWaveform I ω t) / (2 * Real.pi / ω)
      = (‖Aplus‖ ^ 2 - ‖Aminus‖ ^ 2) / Z0 := by
  rw [average_rmsWaveform_mul_rmsWaveform V I hω a]
  exact load_power_eq_incident_sub_reflected V I Aplus Aminus Z0 hZ0 hV hI

/-- Time-averaged load power for peak phasors: under the load-plane
relations, the average of the product of the peak voltage and current
waveforms over any complete period is
`(1 / 2) * ((|Aplus| ^ 2 - |Aminus| ^ 2) / Z0)`. -/
theorem average_peakWaveform_load_power_eq_incident_sub_reflected
    (V I Aplus Aminus : ℂ) (Z0 ω : ℝ) (hω : 0 < ω) (a : ℝ)
    (hZ0 : 0 < Z0) (hV : V = Aplus + Aminus)
    (hI : I = (Aplus - Aminus) / (Z0 : ℂ)) :
    (∫ t in a..(a + 2 * Real.pi / ω),
      peakWaveform V ω t * peakWaveform I ω t) / (2 * Real.pi / ω)
      = (1 / 2) * ((‖Aplus‖ ^ 2 - ‖Aminus‖ ^ 2) / Z0) := by
  rw [average_peakWaveform_mul_peakWaveform V I hω a,
    load_power_eq_incident_sub_reflected V I Aplus Aminus Z0 hZ0 hV hI]

/-- Time-averaged load power for RMS phasors from the load law: the
average of the product of the RMS voltage and current waveforms over
any complete period is `Re ZL * |I| ^ 2`. -/
theorem average_rmsWaveform_load_power_eq_re_mul_norm_sq
    (V I ZL : ℂ) (ω : ℝ) (hω : 0 < ω) (a : ℝ) (hload : V = ZL * I) :
    (∫ t in a..(a + 2 * Real.pi / ω),
      rmsWaveform V ω t * rmsWaveform I ω t) / (2 * Real.pi / ω)
      = ZL.re * ‖I‖ ^ 2 := by
  rw [average_rmsWaveform_mul_rmsWaveform V I hω a]
  exact load_power_eq_re_mul_norm_sq V I ZL hload

/-- Time-averaged load power for peak phasors from the load law: the
average of the product of the peak voltage and current waveforms over
any complete period is `(1 / 2) * (Re ZL * |I| ^ 2)`. -/
theorem average_peakWaveform_load_power_eq_re_mul_norm_sq
    (V I ZL : ℂ) (ω : ℝ) (hω : 0 < ω) (a : ℝ) (hload : V = ZL * I) :
    (∫ t in a..(a + 2 * Real.pi / ω),
      peakWaveform V ω t * peakWaveform I ω t) / (2 * Real.pi / ω)
      = (1 / 2) * (ZL.re * ‖I‖ ^ 2) := by
  rw [average_peakWaveform_mul_peakWaveform V I hω a,
    load_power_eq_re_mul_norm_sq V I ZL hload]

/-- Wave form of the criterion: under the load-plane relations and a
nonzero incident amplitude, the reflected amplitude is at most the
incident amplitude if and only if `Re ZL >= 0`. These hypotheses already
force `ZL + Z0 != 0` (`LineWaveTermination.load_sum_ne_zero`). -/
theorem norm_reflected_le_norm_incident_iff (V I Aplus Aminus ZL : ℂ) (Z0 : ℝ)
    (hZ0 : 0 < Z0) (hV : V = Aplus + Aminus)
    (hI : I = (Aplus - Aminus) / (Z0 : ℂ)) (hload : V = ZL * I)
    (hA : Aplus ≠ 0) :
    ‖Aminus‖ ≤ ‖Aplus‖ ↔ 0 ≤ ZL.re := by
  have hsum := load_sum_ne_zero V I Aplus Aminus ZL Z0 hZ0 hV hI hload hA
  have hApos : 0 < ‖Aplus‖ := norm_pos_iff.mpr hA
  rw [← div_le_one hApos, ← norm_div,
    load_reflectionCoefficient_eq V I Aplus Aminus ZL Z0 hZ0 hV hI hload hA,
    norm_reflectionCoefficient_le_one_iff ZL Z0 hZ0 hsum]

/-- The ratio criterion together with its wave-amplitude form under the
load-plane relations and a nonzero incident amplitude. The guard
`ZL + Z0 != 0` is needed only by the ratio form
(`reflection_criterion_fails_at_excluded_load`); the wave form derives it. -/
theorem passiveLoadReflection (ZL : ℂ) (Z0 : ℝ) (hZ0 : 0 < Z0)
    (hsum : ZL + (Z0 : ℂ) ≠ 0) :
    (‖(ZL - (Z0 : ℂ)) / (ZL + (Z0 : ℂ))‖ ≤ 1 ↔ 0 ≤ ZL.re) ∧
      (∀ V I Aplus Aminus : ℂ, V = Aplus + Aminus →
        I = (Aplus - Aminus) / (Z0 : ℂ) → V = ZL * I → Aplus ≠ 0 →
          (‖Aminus‖ ≤ ‖Aplus‖ ↔ 0 ≤ ZL.re)) := by
  constructor
  · exact norm_reflection_le_one_iff ZL Z0 hZ0 hsum
  · intro V I Aplus Aminus hV hI hload hA
    exact norm_reflected_le_norm_incident_iff V I Aplus Aminus ZL Z0 hZ0 hV hI hload hA

/-! ## C. Resistive loads -/

/-- Real reflection coefficient `(R - Z0) / (R + Z0)` of a resistive
load `R`. -/
noncomputable def resistiveReflection (R Z0 : ℝ) : ℝ :=
  (R - Z0) / (R + Z0)

/-- A real load has the real reflection coefficient. -/
lemma reflectionCoefficient_ofReal (R Z0 : ℝ) :
    reflectionCoefficient (R : ℂ) Z0 = (resistiveReflection R Z0 : ℂ) := by
  simp only [reflectionCoefficient, resistiveReflection, Complex.ofReal_div, Complex.ofReal_sub,
    Complex.ofReal_add]

/-- Resistive criterion: `|Gamma_R| <= 1` if and only if `R >= 0`. -/
theorem abs_resistiveReflection_le_one_iff (R Z0 : ℝ) (hZ0 : 0 < Z0)
    (hsum : R + Z0 ≠ 0) :
    |resistiveReflection R Z0| ≤ 1 ↔ 0 ≤ R := by
  have hpos : 0 < |R + Z0| := abs_pos.mpr hsum
  have h4Z0 : (0:ℝ) < 4 * Z0 := by linarith
  unfold resistiveReflection
  rw [abs_div, div_le_one hpos, abs_le_iff_mul_self_le]
  constructor
  · intro h
    have hsub : (R + Z0) * (R + Z0) - (R - Z0) * (R - Z0) = 4 * R * Z0 := by ring
    have h4' : (0:ℝ) ≤ (4 * Z0) * R := by linarith
    exact (mul_nonneg_iff_of_pos_left h4Z0).mp h4'
  · intro hR
    have hsub : (R + Z0) * (R + Z0) - (R - Z0) * (R - Z0) = 4 * R * Z0 := by ring
    have hnn : (0:ℝ) ≤ 4 * R * Z0 := by positivity
    linarith

/-- Instantaneous real reflection at a resistive load: if at every time the
load voltage is `vplus t + vminus t`, the load current is
`(vplus t - vminus t) / Z0`, and `v t = R * i t`, then
`vminus t = Gamma_R * vplus t` at every time. -/
theorem instantaneous_resistive_reflection (R Z0 : ℝ) (hZ0 : 0 < Z0)
    (hsum : R + Z0 ≠ 0) (vplus vminus v i : ℝ → ℝ)
    (hv : ∀ t, v t = vplus t + vminus t)
    (hi : ∀ t, i t = (vplus t - vminus t) / Z0)
    (hload : ∀ t, v t = R * i t) :
    ∀ t, vminus t = resistiveReflection R Z0 * vplus t := by
  intro t
  have hZ0' : Z0 ≠ 0 := ne_of_gt hZ0
  have h4 : (vplus t + vminus t) * Z0 = R * (vplus t - vminus t) := by
    rw [← hv t, hload t, hi t, ← mul_div_assoc, div_mul_cancel₀ _ hZ0']
  have hgoal : vminus t * (R + Z0) = (R - Z0) * vplus t := by
    linear_combination h4
  unfold resistiveReflection
  rw [div_mul_eq_mul_div, eq_div_iff hsum]
  exact hgoal

/-! ## D. Special loads and the excluded load -/

/-- A matched load `ZL = Z0` on a line with `Z0 > 0` lies in the domain,
`Z0 + Z0 != 0`, and reflects nothing. -/
lemma reflectionCoefficient_matched (Z0 : ℝ) (hZ0 : 0 < Z0) :
    reflectionCoefficient (Z0 : ℂ) Z0 = 0 := by
  have hsum : (Z0 : ℂ) + (Z0 : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (add_pos hZ0 hZ0)
  unfold reflectionCoefficient
  rw [div_eq_iff hsum, sub_self, zero_mul]

/-- A short circuit (zero load) lies in the domain and reflects with a sign
flip. -/
lemma reflectionCoefficient_short (Z0 : ℝ) (hZ0 : 0 < Z0) :
    reflectionCoefficient 0 Z0 = -1 := by
  have hZ0c : (Z0:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hZ0
  unfold reflectionCoefficient
  rw [zero_sub, zero_add, neg_div, div_self hZ0c]

/-- A positive resistor gives `|Gamma_R| < 1`. -/
lemma abs_resistiveReflection_lt_one_of_pos (R Z0 : ℝ) (hZ0 : 0 < Z0)
    (hR : 0 < R) :
    |resistiveReflection R Z0| < 1 := by
  have hsum : R + Z0 ≠ 0 := ne_of_gt (add_pos hR hZ0)
  have hpos : 0 < |R + Z0| := abs_pos.mpr hsum
  unfold resistiveReflection
  rw [abs_div, div_lt_one hpos, abs_of_pos (add_pos hR hZ0), abs_lt]
  constructor <;> linarith

/-- A pure reactance `ZL = i * X` gives `|Gamma| = 1`; the denominator is
automatically nonzero. -/
lemma norm_reflectionCoefficient_pure_reactance (X Z0 : ℝ) (hZ0 : 0 < Z0) :
    ‖reflectionCoefficient (Complex.I * (X : ℂ)) Z0‖ = 1 := by
  have hre : (Complex.I * (X:ℂ) + (Z0:ℂ)).re = Z0 := by
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  have hsum : Complex.I * (X:ℂ) + (Z0:ℂ) ≠ 0 := by
    intro hcon
    rw [hcon, Complex.zero_re] at hre
    linarith
  have him : (Complex.I * (X:ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  exact (norm_reflectionCoefficient_eq_one_iff (Complex.I * (X:ℂ)) Z0 hZ0 hsum).mpr him

/-- A negative resistance `R < 0` with `R != -Z0` gives `|Gamma_R| > 1`. -/
lemma one_lt_abs_resistiveReflection_of_neg (R Z0 : ℝ) (hZ0 : 0 < Z0)
    (hR : R < 0) (hsum : R + Z0 ≠ 0) :
    1 < |resistiveReflection R Z0| := by
  exact not_le.mp
    (mt (abs_resistiveReflection_le_one_iff R Z0 hZ0 hsum).mp (not_le.mpr hR))

/-- `ZL = -Z0` is outside the ratio domain: there the total division gives
`Gamma = 0`, so the norm bound holds while `Re ZL < 0`, and the
criterion fails without the denominator guard. -/
lemma reflection_criterion_fails_at_excluded_load (Z0 : ℝ) (hZ0 : 0 < Z0) :
    ‖reflectionCoefficient (-(Z0 : ℂ)) Z0‖ ≤ 1 ∧ (-(Z0 : ℂ)).re < 0 := by
  have hden : (-(Z0:ℂ)) + (Z0:ℂ) = 0 := neg_add_cancel _
  have hval : reflectionCoefficient (-(Z0:ℂ)) Z0 = 0 := by
    unfold reflectionCoefficient
    rw [hden, div_zero]
  constructor
  · rw [hval, norm_zero]
    exact zero_le_one
  · simp only [Complex.neg_re, Complex.ofReal_re]
    linarith

/-- An inductive load can have a frequency-dependent coefficient: the
reactance `i * omega * L` with `L = 1`, `Z0 = 1` gives different
coefficients at `omega = 1` and `omega = 2`. This is one example, not a
general statement about reactive loads. -/
lemma reflectionCoefficient_inductive_depends_on_frequency :
    reflectionCoefficient (Complex.I * ((1 : ℝ) * 1 : ℝ)) 1 ≠
      reflectionCoefficient (Complex.I * ((2 : ℝ) * 1 : ℝ)) 1 := by
  have r1 : ((((1:ℝ)*1 : ℝ)):ℂ) = 1 := by norm_num
  have r2 : ((((2:ℝ)*1 : ℝ)):ℂ) = 2 := by norm_num
  have hden1 : (Complex.I * (1:ℂ) + (1:ℂ)) ≠ 0 := by
    have hre1 : (Complex.I * (1:ℂ) + (1:ℂ)).re = 1 := by simp
    intro hcon
    rw [hcon, Complex.zero_re] at hre1
    exact one_ne_zero hre1.symm
  have hden2 : (Complex.I * (2:ℂ) + (1:ℂ)) ≠ 0 := by
    have hre2 : (Complex.I * (2:ℂ) + (1:ℂ)).re = 1 := by simp
    intro hcon
    rw [hcon, Complex.zero_re] at hre2
    exact one_ne_zero hre2.symm
  rw [r1, r2]
  unfold reflectionCoefficient
  rw [Complex.ofReal_one]
  intro hcontra
  rw [div_eq_div_iff hden1 hden2] at hcontra
  have h2I : (-2:ℂ) * Complex.I = 0 := by linear_combination hcontra
  rcases (mul_eq_zero.mp h2I) with h | h
  · norm_num at h
  · exact Complex.I_ne_zero h

end PhyslibExt.Circuits.PassiveLoadReflection
