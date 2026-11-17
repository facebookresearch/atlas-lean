/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.BalancedThreePhase

@[expose] public section

open PhyslibExt.Circuits.BalancedThreePhase

namespace PhyslibExtTest.Circuits.BalancedThreePhase

/-- Balanced phases carry no neutral current. -/
example (V : ℂ) : neutralCurrent (balancedPhases V) = 0 :=
  neutralCurrent_balancedPhases V

/-- Positive-sequence line voltages: `sqrt 3` times the phase
waveform with a +30-degree factor. -/
example : lineVoltage (balancedPhases (1 : ℂ)) =
    balancedPhases ((Real.sqrt 3 : ℂ) * Complex.exp (((Real.pi / 6 : ℝ) : ℂ) * Complex.I)) := by
  simpa using lineVoltage_balancedPhases (1 : ℂ)

/-- Reversed-sequence line voltages carry the -30-degree factor. -/
example : lineVoltage (reversedPhases (1 : ℂ)) =
    reversedPhases ((Real.sqrt 3 : ℂ) * Complex.exp ((-(Real.pi / 6 : ℝ) : ℂ) * Complex.I)) := by
  simpa using lineVoltage_reversedPhases (1 : ℂ)

/-- Delta line currents sum to zero. -/
example (J : ZMod 3 → ℂ) : ∑ p, deltaLineCurrent J p = 0 :=
  sum_deltaLineCurrent J

/-- Total balanced power at unit phasors is `3`. -/
example : ∑ p, complexPower (balancedPhases (1 : ℂ) p) (balancedPhases (1 : ℂ) p) = 3 := by
  have h := sum_complexPower_balancedPhases (1 : ℂ) (1 : ℂ)
  simpa using h

/-- An altered third phase leaves neutral current equal to the
alteration. -/
example : neutralCurrent (alteredPhases (1 : ℂ) (2 : ℂ)) = 2 :=
  neutralCurrent_altered 1 2

end PhyslibExtTest.Circuits.BalancedThreePhase
