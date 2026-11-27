/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.LineWaveTermination
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

open PhyslibExt.Circuits.LineWaveTermination

namespace PhyslibExtTest.Circuits.LineWaveTermination

/-- Concrete multiplicative relation: forward amplitude `2`,
backward amplitude `1`, unit characteristic impedance and load
`3` satisfy `(3 + 1) * 1 = (3 - 1) * 2`. -/
example : ((3 : ℂ) + 1) * 1 = ((3 : ℂ) - 1) * 2 :=
  load_multiplicative_relation 3 1 2 1 3 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- Concrete guarded ratio: with the same values,
`1 / 2 = (3 - 1) / (3 + 1)`. -/
example : (1 : ℂ) / 2 = ((3 : ℂ) - 1) / ((3 : ℂ) + 1) :=
  load_reflection_ratio 3 1 2 1 3 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The same ratio from nonzero excitation alone, with the
denominator guard derived. -/
example : (1 : ℂ) / 2 = ((3 : ℂ) - 1) / ((3 : ℂ) + 1) :=
  load_reflection_ratio_of_ne_zero 3 1 2 1 3 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- The same ratio is the reflection coefficient at load `3` and
unit characteristic impedance. -/
example : (1 : ℂ) / 2 = reflectionCoefficient 3 1 :=
  load_reflectionCoefficient_eq 3 1 2 1 3 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- At the load plane the voltage phasor is the sum of the two
amplitudes and the current phasor is their difference over the
characteristic impedance, at the same concrete amplitudes. -/
example : voltagePhasor 2 1 5 0 = 3 := by
  rw [voltagePhasor_at_zero]
  norm_num

example : currentPhasor 2 1 1 5 0 = 1 := by
  rw [currentPhasor_at_zero]
  norm_num

/-! Wave parameters at `L = 2`, `C = 8` and `omega = 3`, where
`sqrt (L * C) = 4` and `sqrt (L / C) = 1 / 2`. Swapping `L` and `C`
or inverting a square root changes every value below. -/

lemma sqrt_two_mul_eight : Real.sqrt (2 * 8) = 4 := by
  rw [show (2 : ℝ) * 8 = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- The wave speed `1 / sqrt (L * C)` at `L = 2`, `C = 8` is `1 / 4`. -/
example : waveSpeed 2 8 = 1 / 4 := by
  unfold waveSpeed
  rw [sqrt_two_mul_eight]

/-- The characteristic impedance `sqrt (L / C)` at `L = 2`, `C = 8`
is `1 / 2`. -/
lemma characteristicImpedance_two_eight : characteristicImpedance 2 8 = 1 / 2 := by
  unfold characteristicImpedance
  rw [show (2 : ℝ) / 8 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- The phase constant `omega * sqrt (L * C)` at `L = 2`,
`C = 8`, `omega = 3` is `12`. -/
lemma phaseConstant_two_eight_three : phaseConstant 2 8 3 = 12 := by
  unfold phaseConstant
  rw [sqrt_two_mul_eight]
  norm_num

/-! Phasors away from the load plane, with phase constant `12`
at `x = pi / 24`, so `beta * x = pi / 2`. The forward factor
`exp (-i * beta * x)` is `-i` and the backward factor is `i`; a
convention with the propagation directions swapped would give the
opposite signs. -/

lemma exp_forward_at_quarter_turn :
    Complex.exp (↑(-(12 * (Real.pi / 24))) * Complex.I) = -Complex.I := by
  rw [show -(12 * (Real.pi / 24)) = -(Real.pi / 2) by ring, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

lemma exp_backward_at_quarter_turn :
    Complex.exp (↑(12 * (Real.pi / 24)) * Complex.I) = Complex.I := by
  rw [show 12 * (Real.pi / 24) = Real.pi / 2 by ring, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  simp

/-- With asymmetric amplitudes `2` and `1`, the voltage phasor at a
quarter turn is `2 * (-i) + 1 * i = -i`. -/
lemma voltagePhasor_at_quarter_turn :
    voltagePhasor 2 1 12 (Real.pi / 24) = -Complex.I := by
  unfold voltagePhasor
  rw [exp_forward_at_quarter_turn, exp_backward_at_quarter_turn]
  ring

/-- With the same amplitudes and characteristic impedance `1 / 2`, the
current phasor at a quarter turn is `(2 * (-i) - 1 * i) / (1 / 2) = -6 * i`. -/
lemma currentPhasor_at_quarter_turn :
    currentPhasor 2 1 (1 / 2) 12 (Real.pi / 24) = -6 * Complex.I := by
  unfold currentPhasor
  rw [exp_forward_at_quarter_turn, exp_backward_at_quarter_turn]
  push_cast
  ring

/-! Telegrapher equations at `L = 2`, `C = 8`, `omega = 3`. The
expected derivatives are computed by hand from the definitions:
`dV/dx = -i * beta * Aplus * exp (-i * beta * x)
  + i * beta * Aminus * exp (i * beta * x) = -24 - 12 = -36`
and `dI/dx = (-i * beta * Aplus * exp (-i * beta * x)
  - i * beta * Aminus * exp (i * beta * x)) / Z0 = (-24 + 12) / (1 / 2) = -24`.
A sign error in the propagation direction or in the factor
`-i * omega * L` (or `-i * omega * C`), or a swap of `L` and `C`, makes
these fail. -/

/-- Voltage telegrapher equation at a quarter turn:
`-(i * 3 * 2) * (-6 * i) = -36`. -/
example : deriv (fun y : ℝ => voltagePhasor 2 1 12 y) (Real.pi / 24) = -36 := by
  rw [voltagePhasor_deriv 2 1 2 8 3 (1 / 2) 12 (Real.pi / 24) (by norm_num) (by norm_num)
    phaseConstant_two_eight_three.symm characteristicImpedance_two_eight.symm,
    currentPhasor_at_quarter_turn]
  push_cast
  linear_combination 36 * Complex.I_sq

/-- Current telegrapher equation at a quarter turn:
`-(i * 3 * 8) * (-i) = -24`. -/
example : deriv (fun y : ℝ => currentPhasor 2 1 (1 / 2) 12 y) (Real.pi / 24) = -24 := by
  rw [currentPhasor_deriv 2 1 2 8 3 (1 / 2) 12 (Real.pi / 24) (by norm_num) (by norm_num)
    phaseConstant_two_eight_three.symm characteristicImpedance_two_eight.symm,
    voltagePhasor_at_quarter_turn]
  push_cast
  linear_combination 24 * Complex.I_sq

/-- Matched instance: a load equal to the unit characteristic
impedance, forward amplitude `2` and load voltage and current
`2`, reflects nothing. -/
example : (0 : ℂ) = 0 :=
  matched_load_reflection_eq_zero 2 2 2 0 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- Short-circuit instance: a zero load, forward amplitude `2`,
load voltage `0` and load current `4`, reflects with a sign
flip. -/
example : (-2 : ℂ) = -2 :=
  shortCircuit_load_reflection 0 4 2 (-2) (by norm_num) (by norm_num)

/-- Short-circuit load at zero excitation: both amplitudes zero, load
voltage and current zero, still satisfy the sign flip at the load
level. -/
example : (0 : ℂ) = -0 :=
  shortCircuit_load_reflection 0 0 0 0 (by norm_num) (by norm_num)

/-- The combined relation derives the denominator guard from nonzero
excitation: at unit characteristic impedance (`L = C = 1`) with
forward amplitude `2`, backward amplitude `1` and load `3`, it returns
`3 + 1 ≠ 0` without being given it. -/
example : ((3 : ℂ) + ((1 : ℝ) : ℂ)) ≠ 0 :=
  (((((lineWaveTerminationRelations 2 1 3 1 1 1 1 (phaseConstant 1 1 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) rfl
    (by simp [characteristicImpedance])).2.2.2.2) 3 1 (by norm_num)
    (by norm_num) (by norm_num)).2) (by norm_num)).1

/-- Short circuit at zero excitation: both amplitudes zero still
satisfy the sign flip. -/
example : (0 : ℂ) = -0 :=
  shortCircuit_reflection 0 0 (by norm_num)

/-- Zero excitation does not give the divided formula at unit
characteristic impedance and load `3`. -/
example : (0 : ℂ) / (0 : ℂ) ≠ ((3 : ℂ) - 1) / ((3 : ℂ) + 1) :=
  zeroExcitation_ratio_example

end PhyslibExtTest.Circuits.LineWaveTermination
