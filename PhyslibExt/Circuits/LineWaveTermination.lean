/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Lossless transmission-line waves and load termination

## i. Overview

A lossless transmission line with per-unit-length inductance
`L > 0` and capacitance `C > 0` has wave speed `1 / sqrt (L * C)`
and characteristic impedance `sqrt (L / C)`. At fixed angular
frequency under the `exp (+i * omega * t)` convention, the same
convention as the canonical waveforms
`PhyslibExt.Circuits.RMSAveragePower.rmsWaveform` and
`PhyslibExt.Circuits.RMSAveragePower.peakWaveform` (whose period
averages are
`PhyslibExt.Circuits.RMSAveragePower.average_rmsWaveform_mul_rmsWaveform`
and
`PhyslibExt.Circuits.RMSAveragePower.average_peakWaveform_mul_peakWaveform`),
the voltage and current phasors are superpositions of a forward
wave of amplitude `Aplus` and a backward wave of amplitude
`Aminus`, with phase constant `omega * sqrt (L * C)`. At
the load plane the phasors are `V = Aplus + Aminus` and
`I = (Aplus - Aminus) / Z0`; together with `V = ZL * I` they give
the multiplicative relation
`(ZL + Z0) * Aminus = (ZL - Z0) * Aplus`, and the divided
reflection formula under `Aplus != 0`. The denominator guard
`ZL + Z0 != 0` is not an independent assumption: it follows from
the load relations and `Aplus != 0`.

The parameter identities are proved from positivity and the
real square-root laws for `L * C` and `L / C`. The phasor
derivative identities are proved by differentiating the two
exponential wave factors and using the square-root identities
`sqrt (L * C) * sqrt (L / C) = L` and the corresponding
capacitance identity, which is where positivity of `L` and `C`
is used. The load identities are proved by clearing the
characteristic-impedance denominator and comparing coefficients;
the matched, short-circuit and open-circuit cases are the
corresponding specializations (the short-circuit case needs no
excitation guard), and the zero-excitation example
records that the divided formula is not available when both
amplitudes vanish.

## ii. Key results

- `voltagePhasor_deriv` and `currentPhasor_deriv`: the phasor
  telegrapher equations for voltage and current.
- `load_multiplicative_relation`: the division-free reflection
  relation at the load plane.
- `load_sum_ne_zero`: nonzero excitation forces a nonzero
  denominator `ZL + Z0`.
- `load_reflection_ratio_of_ne_zero` and
  `load_reflectionCoefficient_eq`: the divided reflection formula under
  nonzero excitation alone; `load_reflection_ratio` states it with the
  denominator guard spelled out.
- `lineWaveTerminationRelations`: the combined speed, impedance,
  telegrapher and load relations.

## iii. Table of contents

- A. Wave parameters and phasors
- B. Parameter identities
- C. Load-plane values and phasor telegrapher equations
- D. Load termination and reflection
- E. Combined relations

## iv. References

- D. M. Pozar, *Microwave Engineering*, fourth edition, Wiley,
  2012: transmission-line theory, propagation on a lossless
  line, and the load reflection coefficient.

## A. Wave parameters and phasors
-/

@[expose] public section

namespace PhyslibExt.Circuits.LineWaveTermination

/-- Wave speed `1 / sqrt(L * C)`. -/
noncomputable def waveSpeed (L C : ℝ) : ℝ :=
  1 / Real.sqrt (L * C)

/-- Characteristic impedance `sqrt(L / C)`, a positive real number
under the hypotheses stated separately. -/
noncomputable def characteristicImpedance (L C : ℝ) : ℝ :=
  Real.sqrt (L / C)

/-- Phase constant `beta = omega * sqrt(L * C)`, the real wavenumber of
the phasors `exp (-i * beta * x)` and `exp (i * beta * x)`. On a
lossless line the complex propagation constant is `i * beta`. -/
noncomputable def phaseConstant (L C ω : ℝ) : ℝ :=
  ω * Real.sqrt (L * C)

/-- Voltage phasor at position `x`: a forward wave plus a backward
wave. -/
noncomputable def voltagePhasor (Aplus Aminus : ℂ) (β x : ℝ) : ℂ :=
  Aplus * Complex.exp (↑(-(β * x)) * Complex.I)
    + Aminus * Complex.exp (↑(β * x) * Complex.I)

/-- Current phasor at position `x`: the forward wave minus the
backward wave, divided by the characteristic impedance. -/
noncomputable def currentPhasor (Aplus Aminus : ℂ) (Z0 β x : ℝ) : ℂ :=
  (Aplus * Complex.exp (↑(-(β * x)) * Complex.I)
    - Aminus * Complex.exp (↑(β * x) * Complex.I)) / (Z0 : ℂ)

/-- Reflection coefficient `(ZL - Z0) / (ZL + Z0)`. -/
noncomputable def reflectionCoefficient (ZL : ℂ) (Z0 : ℝ) : ℂ :=
  (ZL - (Z0 : ℂ)) / (ZL + (Z0 : ℂ))

/-! ## B. Parameter identities -/

/-- The wave speed is positive. -/
lemma waveSpeed_pos (L C : ℝ) (hL : 0 < L) (hC : 0 < C) :
    0 < waveSpeed L C := by
  unfold waveSpeed
  exact one_div_pos.mpr (Real.sqrt_pos.mpr (mul_pos hL hC))

/-- The characteristic impedance is positive. -/
lemma characteristicImpedance_pos (L C : ℝ) (hL : 0 < L) (hC : 0 < C) :
    0 < characteristicImpedance L C := by
  unfold characteristicImpedance
  exact Real.sqrt_pos.mpr (div_pos hL hC)

/-- The wave speed is the reciprocal of `sqrt(L * C)`. -/
lemma waveSpeed_mul_sqrt (L C : ℝ) (hL : 0 < L) (hC : 0 < C) :
    waveSpeed L C * Real.sqrt (L * C) = 1 := by
  unfold waveSpeed
  exact one_div_mul_cancel (ne_of_gt (Real.sqrt_pos.mpr (mul_pos hL hC)))

/-- The squared characteristic impedance is `L / C`. -/
lemma characteristicImpedance_sq (L C : ℝ) (hL : 0 < L) (hC : 0 < C) :
    characteristicImpedance L C ^ 2 = L / C := by
  unfold characteristicImpedance
  exact Real.sq_sqrt (le_of_lt (div_pos hL hC))

/-- Speed times impedance is `1 / C`. -/
lemma waveSpeed_mul_characteristicImpedance (L C : ℝ) (hL : 0 < L)
    (hC : 0 < C) :
    waveSpeed L C * characteristicImpedance L C = 1 / C := by
  have hZ : characteristicImpedance L C = Real.sqrt (L * C) / C := by
    have hL' : 0 ≤ L := le_of_lt hL
    have hsC : Real.sqrt C ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hC)
    have hCne : C ≠ 0 := ne_of_gt hC
    unfold characteristicImpedance
    rw [Real.sqrt_div hL', Real.sqrt_mul hL', div_eq_div_iff hsC hCne,
      mul_assoc, Real.mul_self_sqrt (le_of_lt hC)]
  rw [hZ, ← mul_div_assoc, waveSpeed_mul_sqrt L C hL hC]

/-- Impedance divided by speed is `L`. -/
lemma characteristicImpedance_div_waveSpeed (L C : ℝ) (hL : 0 < L)
    (hC : 0 < C) :
    characteristicImpedance L C / waveSpeed L C = L := by
  have hZ : characteristicImpedance L C = Real.sqrt (L * C) / C := by
    have hL' : 0 ≤ L := le_of_lt hL
    have hsC : Real.sqrt C ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hC)
    have hCne : C ≠ 0 := ne_of_gt hC
    unfold characteristicImpedance
    rw [Real.sqrt_div hL', Real.sqrt_mul hL', div_eq_div_iff hsC hCne,
      mul_assoc, Real.mul_self_sqrt (le_of_lt hC)]
  have hs2 : Real.sqrt (L * C) ^ 2 = L * C :=
    Real.sq_sqrt (le_of_lt (mul_pos hL hC))
  have hsne : Real.sqrt (L * C) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (mul_pos hL hC))
  have hCne : C ≠ 0 := ne_of_gt hC
  have hvne : waveSpeed L C ≠ 0 := ne_of_gt (waveSpeed_pos L C hL hC)
  rw [hZ, div_eq_iff hvne]
  unfold waveSpeed
  rw [div_eq_iff hCne]
  have hring : L * (1 / Real.sqrt (L * C)) * C
      = (L * C) / Real.sqrt (L * C) := by ring
  rw [hring, eq_div_iff hsne, ← pow_two]
  exact hs2

/-- The phase constant is frequency divided by wave speed. -/
lemma phaseConstant_eq_div_waveSpeed (L C ω : ℝ) (hL : 0 < L)
    (hC : 0 < C) :
    phaseConstant L C ω = ω / waveSpeed L C := by
  unfold phaseConstant waveSpeed
  have hsne : Real.sqrt (L * C) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (mul_pos hL hC))
  field_simp

/-! ## C. Load-plane values and phasor telegrapher equations -/

/-- The voltage phasor at the load plane is the sum of the two wave
amplitudes. -/
lemma voltagePhasor_at_zero (Aplus Aminus : ℂ) (β : ℝ) :
    voltagePhasor Aplus Aminus β 0 = Aplus + Aminus := by
  unfold voltagePhasor
  simp

/-- The current phasor at the load plane is the difference of the two
wave amplitudes divided by the characteristic impedance. -/
lemma currentPhasor_at_zero (Aplus Aminus : ℂ) (Z0 β : ℝ) :
    currentPhasor Aplus Aminus Z0 β 0 = (Aplus - Aminus) / (Z0 : ℂ) := by
  unfold currentPhasor
  simp

/-- Phasor telegrapher equation for voltage: the spatial derivative
of the voltage phasor is `-i * omega * L` times the current phasor. -/
theorem voltagePhasor_deriv (Aplus Aminus : ℂ) (L C ω Z0 β x : ℝ)
    (hL : 0 < L) (hC : 0 < C)
    (hβ : β = phaseConstant L C ω) (hZ : Z0 = characteristicImpedance L C) :
    deriv (fun y : ℝ => voltagePhasor Aplus Aminus β y) x
      = -(Complex.I * (ω : ℂ) * (L : ℂ)) * currentPhasor Aplus Aminus Z0 β x := by
  have hmul : Real.sqrt (L * C) * Real.sqrt (L / C) = L := by
    rw [← Real.sqrt_mul (le_of_lt (mul_pos hL hC))]
    have hCne : C ≠ 0 := ne_of_gt hC
    have hLC : (L * C) * (L / C) = L ^ 2 := by
      field_simp
    rw [hLC, Real.sqrt_sq (le_of_lt hL)]
  have hβZ0 : β * Z0 = ω * L := by
    rw [hβ, hZ]
    unfold phaseConstant characteristicImpedance
    rw [mul_assoc, hmul]
  have hβZ0c : (β : ℂ) * (Z0 : ℂ) = (ω : ℂ) * (L : ℂ) := by exact_mod_cast hβZ0
  have hZ0pos : 0 < Z0 := by
    rw [hZ]
    exact characteristicImpedance_pos L C hL hC
  have hZ0ne : (Z0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hZ0pos)
  have hexp_gen : ∀ c : ℂ, HasDerivAt (fun y : ℝ => Complex.exp (↑y * c))
      (Complex.exp (↑x * c) * c) x := by
    intro c
    have hinner : HasDerivAt (fun z : ℂ => z * c) c (↑x) := hasDerivAt_mul_const c
    have hexpC := hinner.cexp
    simpa using hexpC.comp_ofReal
  have hpt1 : ∀ y : ℝ, (↑(-(β * y)) * Complex.I : ℂ)
      = ↑y * (-(β : ℂ) * Complex.I) := by
    intro y
    push_cast
    ring
  have hpt2 : ∀ y : ℝ, (↑(β * y) * Complex.I : ℂ)
      = ↑y * ((β : ℂ) * Complex.I) := by
    intro y
    push_cast
    ring
  have hF : HasDerivAt (fun y : ℝ => Complex.exp (↑(-(β * y)) * Complex.I))
      (Complex.exp (↑x * (-(β : ℂ) * Complex.I)) * (-(β : ℂ) * Complex.I)) x := by
    simp only [hpt1]
    exact hexp_gen _
  have hB : HasDerivAt (fun y : ℝ => Complex.exp (↑(β * y) * Complex.I))
      (Complex.exp (↑x * ((β : ℂ) * Complex.I)) * ((β : ℂ) * Complex.I)) x := by
    simp only [hpt2]
    exact hexp_gen _
  have h1 : HasDerivAt (fun y : ℝ => Aplus * Complex.exp (↑(-(β * y)) * Complex.I))
      (Aplus * (Complex.exp (↑x * (-(β : ℂ) * Complex.I))
        * (-(β : ℂ) * Complex.I))) x :=
    HasDerivAt.const_mul Aplus hF
  have h2 : HasDerivAt (fun y : ℝ => Aminus * Complex.exp (↑(β * y) * Complex.I))
      (Aminus * (Complex.exp (↑x * ((β : ℂ) * Complex.I))
        * ((β : ℂ) * Complex.I))) x :=
    HasDerivAt.const_mul Aminus hB
  have hsum : HasDerivAt
      ((fun y : ℝ => Aplus * Complex.exp (↑(-(β * y)) * Complex.I))
        + (fun y : ℝ => Aminus * Complex.exp (↑(β * y) * Complex.I)))
      (Aplus * (Complex.exp (↑x * (-(β : ℂ) * Complex.I)) * (-(β : ℂ) * Complex.I))
        + Aminus * (Complex.exp (↑x * ((β : ℂ) * Complex.I))
          * ((β : ℂ) * Complex.I))) x :=
    h1.add h2
  have hFsum_eq : (fun y : ℝ => Aplus * Complex.exp (↑(-(β * y)) * Complex.I))
        + (fun y : ℝ => Aminus * Complex.exp (↑(β * y) * Complex.I))
      = fun y : ℝ => voltagePhasor Aplus Aminus β y := by
    ext y
    simp [voltagePhasor, Pi.add_apply]
  rw [← hFsum_eq, hsum.deriv]
  unfold currentPhasor
  rw [hpt1 x, hpt2 x, ← mul_div_assoc, eq_div_iff hZ0ne]
  linear_combination (Complex.I * (Aminus * Complex.exp (↑x * ((β : ℂ) * Complex.I))
    - Aplus * Complex.exp (↑x * (-(β : ℂ) * Complex.I)))) * hβZ0c

/-- Phasor telegrapher equation for current: the spatial derivative
of the current phasor is `-i * omega * C` times the voltage phasor. -/
theorem currentPhasor_deriv (Aplus Aminus : ℂ) (L C ω Z0 β x : ℝ)
    (hL : 0 < L) (hC : 0 < C)
    (hβ : β = phaseConstant L C ω) (hZ : Z0 = characteristicImpedance L C) :
    deriv (fun y : ℝ => currentPhasor Aplus Aminus Z0 β y) x
      = -(Complex.I * (ω : ℂ) * (C : ℂ)) * voltagePhasor Aplus Aminus β x := by
  have hZdiv : characteristicImpedance L C = Real.sqrt (L * C) / C := by
    have hL' : 0 ≤ L := le_of_lt hL
    have hsC : Real.sqrt C ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hC)
    have hCne : C ≠ 0 := ne_of_gt hC
    unfold characteristicImpedance
    rw [Real.sqrt_div hL', Real.sqrt_mul hL', div_eq_div_iff hsC hCne,
      mul_assoc, Real.mul_self_sqrt (le_of_lt hC)]
  have hCne : C ≠ 0 := ne_of_gt hC
  have hCs : C * (Real.sqrt (L * C) / C) = Real.sqrt (L * C) := by
    rw [mul_comm, div_mul_cancel₀ _ hCne]
  have hβeq : β = ω * C * Z0 := by
    rw [hβ, hZ, hZdiv]
    unfold phaseConstant
    rw [mul_assoc, hCs]
  have hβc : (β : ℂ) = (ω : ℂ) * (C : ℂ) * (Z0 : ℂ) := by exact_mod_cast hβeq
  have hZ0pos : 0 < Z0 := by
    rw [hZ]
    exact characteristicImpedance_pos L C hL hC
  have hZ0ne : (Z0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hZ0pos)
  have hexp_gen : ∀ c : ℂ, HasDerivAt (fun y : ℝ => Complex.exp (↑y * c))
      (Complex.exp (↑x * c) * c) x := by
    intro c
    have hinner : HasDerivAt (fun z : ℂ => z * c) c (↑x) := hasDerivAt_mul_const c
    have hexpC := hinner.cexp
    simpa using hexpC.comp_ofReal
  have hpt1 : ∀ y : ℝ, (↑(-(β * y)) * Complex.I : ℂ)
      = ↑y * (-(β : ℂ) * Complex.I) := by
    intro y
    push_cast
    ring
  have hpt2 : ∀ y : ℝ, (↑(β * y) * Complex.I : ℂ)
      = ↑y * ((β : ℂ) * Complex.I) := by
    intro y
    push_cast
    ring
  have hF : HasDerivAt (fun y : ℝ => Complex.exp (↑(-(β * y)) * Complex.I))
      (Complex.exp (↑x * (-(β : ℂ) * Complex.I)) * (-(β : ℂ) * Complex.I)) x := by
    simp only [hpt1]
    exact hexp_gen _
  have hB : HasDerivAt (fun y : ℝ => Complex.exp (↑(β * y) * Complex.I))
      (Complex.exp (↑x * ((β : ℂ) * Complex.I)) * ((β : ℂ) * Complex.I)) x := by
    simp only [hpt2]
    exact hexp_gen _
  have h1 : HasDerivAt (fun y : ℝ => Aplus * Complex.exp (↑(-(β * y)) * Complex.I))
      (Aplus * (Complex.exp (↑x * (-(β : ℂ) * Complex.I))
        * (-(β : ℂ) * Complex.I))) x :=
    HasDerivAt.const_mul Aplus hF
  have h2 : HasDerivAt (fun y : ℝ => Aminus * Complex.exp (↑(β * y) * Complex.I))
      (Aminus * (Complex.exp (↑x * ((β : ℂ) * Complex.I))
        * ((β : ℂ) * Complex.I))) x :=
    HasDerivAt.const_mul Aminus hB
  have hsub : HasDerivAt
      ((fun y : ℝ => Aplus * Complex.exp (↑(-(β * y)) * Complex.I))
        - (fun y : ℝ => Aminus * Complex.exp (↑(β * y) * Complex.I)))
      (Aplus * (Complex.exp (↑x * (-(β : ℂ) * Complex.I)) * (-(β : ℂ) * Complex.I))
        - Aminus * (Complex.exp (↑x * ((β : ℂ) * Complex.I))
          * ((β : ℂ) * Complex.I))) x :=
    h1.sub h2
  have hdiv : HasDerivAt (fun y : ℝ => (((fun y : ℝ =>
      Aplus * Complex.exp (↑(-(β * y)) * Complex.I))
        - (fun y : ℝ => Aminus * Complex.exp (↑(β * y) * Complex.I))) y / (Z0 : ℂ)))
      ((Aplus * (Complex.exp (↑x * (-(β : ℂ) * Complex.I)) * (-(β : ℂ) * Complex.I))
        - Aminus * (Complex.exp (↑x * ((β : ℂ) * Complex.I))
          * ((β : ℂ) * Complex.I))) / (Z0 : ℂ)) x :=
    hsub.div_const _
  have hFdiv_eq : (fun y : ℝ => (((fun y : ℝ =>
      Aplus * Complex.exp (↑(-(β * y)) * Complex.I))
        - (fun y : ℝ => Aminus * Complex.exp (↑(β * y) * Complex.I))) y / (Z0 : ℂ)))
      = fun y : ℝ => currentPhasor Aplus Aminus Z0 β y := by
    ext y
    simp [currentPhasor, Pi.sub_apply]
  rw [← hFdiv_eq, hdiv.deriv]
  unfold voltagePhasor
  rw [hpt1 x, hpt2 x, div_eq_iff hZ0ne]
  linear_combination (-(Complex.I * (Aplus * Complex.exp (↑x * (-(β : ℂ) * Complex.I))
    + Aminus * Complex.exp (↑x * ((β : ℂ) * Complex.I))))) * hβc

/-! ## D. Load termination and reflection -/

/-- Load elimination in multiplicative form: the load relations imply
`(ZL + Z0) * Aminus = (ZL - Z0) * Aplus`, with no division by a wave
amplitude and no division by `ZL + Z0`. -/
theorem load_multiplicative_relation (V I Aplus Aminus ZL : ℂ) (Z0 : ℝ)
    (hZ0 : 0 < Z0) (hV : V = Aplus + Aminus)
    (hI : I = (Aplus - Aminus) / (Z0 : ℂ)) (hload : V = ZL * I) :
    (ZL + (Z0 : ℂ)) * Aminus = (ZL - (Z0 : ℂ)) * Aplus := by
  have hZ0ne : (Z0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hZ0)
  rw [hV, hI] at hload
  have h2 : (Aplus + Aminus) * (Z0 : ℂ) = ZL * (Aplus - Aminus) := by
    rw [hload, mul_assoc, div_mul_cancel₀ _ hZ0ne]
  linear_combination h2

/-- Nonzero excitation forces a nonzero denominator: if `ZL + Z0 = 0`,
the multiplicative relation gives `0 = (-2 * Z0) * Aplus`, so
`Aplus = 0`. -/
lemma load_sum_ne_zero (V I Aplus Aminus ZL : ℂ) (Z0 : ℝ)
    (hZ0 : 0 < Z0) (hV : V = Aplus + Aminus)
    (hI : I = (Aplus - Aminus) / (Z0 : ℂ)) (hload : V = ZL * I)
    (hA : Aplus ≠ 0) :
    ZL + (Z0 : ℂ) ≠ 0 := by
  intro hsum
  have hZ0ne : (Z0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hZ0)
  have hmul := load_multiplicative_relation V I Aplus Aminus ZL Z0 hZ0 hV hI hload
  have hZL : ZL = -(Z0 : ℂ) := by linear_combination hsum
  rw [hsum, zero_mul, hZL] at hmul
  have h2 : (-(Z0 : ℂ) - (Z0 : ℂ)) ≠ 0 := by
    have h22 : -(Z0 : ℂ) - (Z0 : ℂ) = -(2 * (Z0 : ℂ)) := by ring
    rw [h22, neg_ne_zero]
    exact mul_ne_zero two_ne_zero hZ0ne
  exact hA ((mul_eq_zero.mp hmul.symm).resolve_left h2)

/-- Guarded reflection ratio: under nonzero excitation and a nonzero
denominator, the amplitude ratio is `(ZL - Z0) / (ZL + Z0)`. The
denominator guard is implied by the others (`load_sum_ne_zero`);
`load_reflection_ratio_of_ne_zero` states the result without it. -/
theorem load_reflection_ratio (V I Aplus Aminus ZL : ℂ) (Z0 : ℝ)
    (hZ0 : 0 < Z0) (hV : V = Aplus + Aminus)
    (hI : I = (Aplus - Aminus) / (Z0 : ℂ)) (hload : V = ZL * I)
    (hA : Aplus ≠ 0) (hsum : ZL + (Z0 : ℂ) ≠ 0) :
    Aminus / Aplus = (ZL - (Z0 : ℂ)) / (ZL + (Z0 : ℂ)) := by
  have hmul := load_multiplicative_relation V I Aplus Aminus ZL Z0 hZ0 hV hI hload
  rw [div_eq_div_iff hA hsum]
  linear_combination hmul

/-- Reflection ratio under nonzero excitation alone: the denominator
guard is derived by `load_sum_ne_zero`. -/
theorem load_reflection_ratio_of_ne_zero (V I Aplus Aminus ZL : ℂ) (Z0 : ℝ)
    (hZ0 : 0 < Z0) (hV : V = Aplus + Aminus)
    (hI : I = (Aplus - Aminus) / (Z0 : ℂ)) (hload : V = ZL * I)
    (hA : Aplus ≠ 0) :
    Aminus / Aplus = (ZL - (Z0 : ℂ)) / (ZL + (Z0 : ℂ)) :=
  load_reflection_ratio V I Aplus Aminus ZL Z0 hZ0 hV hI hload hA
    (load_sum_ne_zero V I Aplus Aminus ZL Z0 hZ0 hV hI hload hA)

/-- Under nonzero excitation the amplitude ratio is the reflection
coefficient; the denominator guard is derived by `load_sum_ne_zero`. -/
lemma load_reflectionCoefficient_eq (V I Aplus Aminus ZL : ℂ) (Z0 : ℝ)
    (hZ0 : 0 < Z0) (hV : V = Aplus + Aminus)
    (hI : I = (Aplus - Aminus) / (Z0 : ℂ)) (hload : V = ZL * I)
    (hA : Aplus ≠ 0) :
    Aminus / Aplus = reflectionCoefficient ZL Z0 := by
  unfold reflectionCoefficient
  exact load_reflection_ratio_of_ne_zero V I Aplus Aminus ZL Z0 hZ0 hV hI hload hA

/-- Matched load: a load equal to the characteristic impedance
reflects nothing. -/
lemma matched_load_reflection_eq_zero (V I Aplus Aminus : ℂ) (Z0 : ℝ)
    (hZ0 : 0 < Z0) (hV : V = Aplus + Aminus)
    (hI : I = (Aplus - Aminus) / (Z0 : ℂ)) (hload : V = (Z0 : ℂ) * I) :
    Aminus = 0 := by
  have hZ0ne : (Z0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hZ0)
  have hmul := load_multiplicative_relation V I Aplus Aminus (↑Z0) Z0 hZ0 hV hI hload
  rw [sub_self, zero_mul] at hmul
  have h2 : (Z0 : ℂ) + (Z0 : ℂ) ≠ 0 := by
    have h22 : (Z0 : ℂ) + (Z0 : ℂ) = 2 * (Z0 : ℂ) := by ring
    rw [h22]
    exact mul_ne_zero two_ne_zero hZ0ne
  exact (mul_eq_zero.mp hmul).resolve_left h2

/-- Short circuit: zero load voltage forces the backward amplitude to
be the negated forward amplitude, with no excitation guard. -/
lemma shortCircuit_reflection (Aplus Aminus : ℂ) (hV : Aplus + Aminus = 0) :
    Aminus = -Aplus := by
  linear_combination hV

/-- Short-circuit load: a zero load impedance reflects with a sign
flip. Only the voltage relation is used, so neither an excitation
guard nor the current relation is needed. -/
lemma shortCircuit_load_reflection (V I Aplus Aminus : ℂ)
    (hV : V = Aplus + Aminus) (hload : V = (0 : ℂ) * I) :
    Aminus = -Aplus := by
  rw [hV, zero_mul] at hload
  exact shortCircuit_reflection Aplus Aminus hload

/-- Open-circuit limit: zero load current forces the backward
amplitude to equal the forward amplitude. This is the separate
infinite-impedance limit; no infinite impedance value is used. -/
lemma openCircuit_reflection (Aplus Aminus : ℂ) (Z0 : ℝ) (hZ0 : 0 < Z0)
    (hI : (Aplus - Aminus) / (Z0 : ℂ) = 0) :
    Aminus = Aplus := by
  have hZ0ne : (Z0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hZ0)
  have h : Aplus - Aminus = 0 := by
    have hcon := congrArg (· * (Z0 : ℂ)) hI
    rw [div_mul_cancel₀ _ hZ0ne, zero_mul] at hcon
    exact hcon
  linear_combination -h

/-- Zero excitation does not justify the divided formula: with both
amplitudes zero the amplitude ratio is `0`, while the impedance ratio
at unit characteristic impedance and load `3` is `1 / 2`. The
multiplicative relation still holds in this case; only the division
step fails. -/
lemma zeroExcitation_ratio_example :
    (0 : ℂ) / (0 : ℂ) ≠ ((3 : ℂ) - 1) / ((3 : ℂ) + 1) := by
  have h1 : ((3 : ℂ) - 1) = ((2 : ℝ) : ℂ) := by norm_num [Complex.ext_iff]
  have h2 : ((3 : ℂ) + 1) = ((4 : ℝ) : ℂ) := by norm_num [Complex.ext_iff]
  rw [zero_div, h1, h2, ← Complex.ofReal_div, ← Complex.ofReal_zero]
  intro h
  have h3 : (0 : ℝ) = 2 / 4 := Complex.ofReal_injective h
  norm_num at h3

/-! ## E. Combined relations -/

/-- Headline correctness: the speed and impedance relations hold, the
phasor telegrapher equations for both voltage and current hold at
every position, the load relations imply the
multiplicative reflection relation, and nonzero excitation alone gives
both the denominator guard `ZL + Z0 != 0` (`load_sum_ne_zero`) and the
divided formula. -/
theorem lineWaveTerminationRelations (Aplus Aminus ZL : ℂ) (L C ω Z0 β : ℝ)
    (hL : 0 < L) (hC : 0 < C) (hω : 0 < ω) (hZ0 : 0 < Z0)
    (hβ : β = phaseConstant L C ω) (hZ : Z0 = characteristicImpedance L C) :
    waveSpeed L C * Real.sqrt (L * C) = 1 ∧
      characteristicImpedance L C ^ 2 = L / C ∧
      (∀ x : ℝ, deriv (fun y : ℝ => voltagePhasor Aplus Aminus β y) x
        = -(Complex.I * (ω : ℂ) * (L : ℂ))
          * currentPhasor Aplus Aminus Z0 β x) ∧
      (∀ x : ℝ, deriv (fun y : ℝ => currentPhasor Aplus Aminus Z0 β y) x
        = -(Complex.I * (ω : ℂ) * (C : ℂ))
          * voltagePhasor Aplus Aminus β x) ∧
      (∀ V I : ℂ, V = Aplus + Aminus
        → I = (Aplus - Aminus) / (Z0 : ℂ) → V = ZL * I
        → (ZL + (Z0 : ℂ)) * Aminus = (ZL - (Z0 : ℂ)) * Aplus
          ∧ (Aplus ≠ 0 → ZL + (Z0 : ℂ) ≠ 0
            ∧ Aminus / Aplus = (ZL - (Z0 : ℂ)) / (ZL + (Z0 : ℂ)))) := by
  refine ⟨waveSpeed_mul_sqrt L C hL hC, characteristicImpedance_sq L C hL hC, ?_, ?_, ?_⟩
  · intro x
    exact voltagePhasor_deriv Aplus Aminus L C ω Z0 β x hL hC hβ hZ
  · intro x
    exact currentPhasor_deriv Aplus Aminus L C ω Z0 β x hL hC hβ hZ
  · intro V I hV hI hload
    refine ⟨load_multiplicative_relation V I Aplus Aminus ZL Z0 hZ0 hV hI hload, ?_⟩
    intro hA
    exact ⟨load_sum_ne_zero V I Aplus Aminus ZL Z0 hZ0 hV hI hload hA,
      load_reflection_ratio_of_ne_zero V I Aplus Aminus ZL Z0 hZ0 hV hI hload hA⟩

end PhyslibExt.Circuits.LineWaveTermination
