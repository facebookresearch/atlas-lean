/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Electronics.LoadedOnePoleAmplifier
import Mathlib.Tactic.NormNum

@[expose] public section

namespace PhyslibExtTest.Electronics.LoadedOnePoleAmplifier

open PhyslibExt.Electronics.LoadedOnePoleAmplifier

/-- The concrete fixture: equal resistances halve both dividers, the
DC gain is `5 / 12`, and the pole location is `-12`. -/
example : sourceDivider 1 1 = 1 / 2 ∧ loadDivider 1 1 = 1 / 2 ∧
    loadedTransfer 10 2 1 (1 / 2) (1 / 2) 0 = ((5 / 12 : ℝ) : ℂ) ∧
    closedLoopPole 2 1 (1 / 2) 10 = -12 :=
  loaded_example

/-- The DC gain of the fixture, read through the transfer at
`s = 0` and through the real DC gain. -/
example : loadedDcGain 10 1 (1 / 2) (1 / 2) = 5 / 12 := by
  have h := loadedTransfer_zero 10 2 1 (1 / 2) (1 / 2)
  rw [loaded_example.2.2.1] at h
  exact_mod_cast h.symm

/-- The fixture DC gain also factors through the canonical
finite-gain closed-loop gain. -/
example : loadedDcGain 10 1 (1 / 2) (1 / 2)
    = (1 / 2) * PhyslibExt.Electronics.FiniteGainFeedback.closedLoopGain
        ((1 / 2) * 10) 1 :=
  loadedDcGain_eq_sourceDivider_mul_closedLoopGain 10 1 (1 / 2) (1 / 2)

/-- The fixture DC gain is positive and below the divider-scaled
ideal gain `(1 / 2) / 1`. -/
example : 0 < loadedDcGain 10 1 (1 / 2) (1 / 2) ∧
    loadedDcGain 10 1 (1 / 2) (1 / 2) < (1 / 2) / 1 :=
  loadedDcGain_pos_and_lt 10 1 (1 / 2) (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- Both dividers of the fixture lie in `(0, 1]`. -/
example : 0 < sourceDivider 1 1 ∧ sourceDivider 1 1 ≤ 1 :=
  sourceDivider_pos_and_le_one 1 1 (by norm_num) (by norm_num)

example : 0 < loadDivider 1 1 ∧ loadDivider 1 1 ≤ 1 :=
  loadDivider_pos_and_le_one 1 1 (by norm_num) (by norm_num)

/-- The loaded denominator of the fixture vanishes at `s = -12`,
the cast of the pole location. -/
example : (1 : ℂ) + (-12 : ℂ) / ((2 : ℝ) : ℂ)
      + (((1 * (1 / 2) * 10 : ℝ)) : ℂ) = 0 := by
  apply (denominator_eq_zero_iff 2 1 (1 / 2) 10 (by norm_num) (-12)).mpr
  have hp := loaded_example.2.2.2
  rw [hp]
  norm_num

/-- The denominator is nonzero at the origin, a point of the closed
right half-plane. -/
example : (1 : ℂ) + (0 : ℂ) / ((2 : ℝ) : ℂ)
      + (((1 * (1 / 2) * 10 : ℝ)) : ℂ) ≠ 0 :=
  denominator_ne_zero_of_re_nonneg 10 2 1 (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) 0 (by simp)

/-- The pole location of the fixture is strictly negative. -/
example : closedLoopPole 2 1 (1 / 2) 10 < 0 :=
  closedLoopPole_neg 2 1 (1 / 2) 10 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- Headline transfer at DC: with `vi = 12`, the model equations hold
for `vamp = 10` and `vo = 5`, and the output is the transfer times the
input. -/
example : (5 : ℂ) = loadedTransfer 10 2 1 (1 / 2) (1 / 2) 0 * 12 :=
  output_eq_loadedTransfer_mul_input 10 2 1 (1 / 2) (1 / 2) 0 12 5 10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [openLoopGain])
    (by norm_num)

/-- Signal-level DC gain of the fixture: with `vi = 12`, the model
equations at `s = 0` hold for `vamp = 10` and `vo = 5`, and the output
is the real DC gain times the input. -/
example : (5 : ℂ) = ((loadedDcGain 10 1 (1 / 2) (1 / 2) : ℝ) : ℂ) * 12 :=
  output_eq_loadedDcGain_mul_input 10 2 1 (1 / 2) (1 / 2) 12 5 10
    (by norm_num) (by norm_num) (by norm_num [openLoopGain]) (by norm_num)

/-- With no source or output resistance both dividers equal one, and
the loaded transfer reduces to the unloaded form. -/
example : sourceDivider 0 3 = 1 ∧ loadDivider 0 7 = 1 :=
  dividers_eq_one_of_no_source_output_resistance 3 7 (by norm_num) (by norm_num)

example (s : ℂ) : loadedTransfer 10 2 1 1 1 s
    = (10 : ℂ) / (1 + s / ((2 : ℝ) : ℂ) + (((1 * 10 : ℝ)) : ℂ)) :=
  loadedTransfer_at_unit_dividers 10 2 1 s

end PhyslibExtTest.Electronics.LoadedOnePoleAmplifier
