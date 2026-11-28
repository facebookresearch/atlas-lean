/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

import MathlibExt.Analysis.Fourier.CircleFejerCoefficients
import Mathlib.Tactic.NormNum

/-!
# The first Fourier character under Fejér truncation

On `UnitAddCircle = ℝ/ℤ`, use the Haar probability measure and the character
`e₁(x) = fourier 1 x`. Its values at zero and a half turn are `1` and `-1`, so it is
nonconstant. Its Fourier coefficient at frequency one is `1`, while its zero and negative-one
coefficients vanish. The zeroth Fejér polynomial cuts off frequency one; the first Fejér
polynomial retains that frequency with coefficient `1/2`, using the normalization `N+1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal
open MathlibExt.Analysis.Fourier

namespace CircleFejerFrequencyOneSmoke

private instance : Fact (1 ≤ (∞ : ℝ≥0∞)) := ⟨le_top⟩

private def character : C(UnitAddCircle, ℂ) := fourier (1 : ℤ)

private def frequencyOne : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
  fourierLp (T := (1 : ℝ)) ∞ (1 : ℤ)

private theorem character_zero : character 0 = 1 :=
  fourier_eval_zero (1 : ℤ)

private theorem character_half : character ((1 / 2 : ℝ) : UnitAddCircle) = -1 := by
  have h := fourier_add_half_inv_index (T := (1 : ℝ)) (n := (1 : ℤ))
    (by decide) zero_lt_one (0 : UnitAddCircle)
  simpa only [character, zero_add, Int.cast_one, div_one, fourier_eval_zero] using h

private theorem frequencyOne_coefficient (k : ℤ) :
    fourierCoeff (frequencyOne : UnitAddCircle → ℂ) k = if k = 1 then 1 else 0 := by
  have h := fourierCoeff_congr_ae
    (coeFn_fourierLp (T := (1 : ℝ)) ∞ (1 : ℤ))
  rw [fourierCoeff_fourier (T := (1 : ℝ)) (1 : ℤ)] at h
  simpa only [frequencyOne, Pi.single_apply] using congrFun h k

example : character 0 = 1 ∧ character ((1 / 2 : ℝ) : UnitAddCircle) = -1 ∧
    character 0 ≠ character ((1 / 2 : ℝ) : UnitAddCircle) := by
  refine ⟨character_zero, character_half, ?_⟩
  rw [character_zero, character_half]
  norm_num

example : fourierCoeff (frequencyOne : UnitAddCircle → ℂ) 1 = 1 ∧
    fourierCoeff (frequencyOne : UnitAddCircle → ℂ) 0 = 0 ∧
    fourierCoeff (frequencyOne : UnitAddCircle → ℂ) (-1) = 0 := by
  constructor
  · simpa using frequencyOne_coefficient 1
  · constructor
    · simpa using frequencyOne_coefficient 0
    · simpa using frequencyOne_coefficient (-1)

example :
    fourierCoeff (fun x : UnitAddCircle => circleFejerPolynomial frequencyOne 0 x) 1 = 0 := by
  rw [circleFejerPolynomial_fourierCoeff, frequencyOne_coefficient]
  norm_num [circleFejerWeight]

example :
    fourierCoeff (fun x : UnitAddCircle => circleFejerPolynomial frequencyOne 1 x) 1 =
      (1 / 2 : ℂ) := by
  rw [circleFejerPolynomial_fourierCoeff, frequencyOne_coefficient]
  norm_num [circleFejerWeight]

end CircleFejerFrequencyOneSmoke
