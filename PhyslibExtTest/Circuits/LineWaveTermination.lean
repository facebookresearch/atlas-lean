/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.LineWaveTermination
import Mathlib.Tactic.NormNum

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
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- At the load plane the voltage phasor is the sum of the two
amplitudes and the current phasor is their difference over the
characteristic impedance, at the same concrete amplitudes. -/
example : voltagePhasor 2 1 5 0 = 3 := by
  rw [voltagePhasor_at_zero]
  norm_num

example : currentPhasor 2 1 1 5 0 = 1 := by
  rw [currentPhasor_at_zero]
  norm_num

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
  shortCircuit_load_reflection 0 4 2 (-2) 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- Short circuit at zero excitation: both amplitudes zero still
satisfy the sign flip. -/
example : (0 : ℂ) = -0 :=
  shortCircuit_reflection 0 0 (by norm_num)

/-- Zero excitation does not give the divided formula at unit
characteristic impedance and load `3`. -/
example : (0 : ℂ) / (0 : ℂ) ≠ ((3 : ℂ) - 1) / ((3 : ℂ) + 1) :=
  zeroExcitation_ratio_example

end PhyslibExtTest.Circuits.LineWaveTermination
