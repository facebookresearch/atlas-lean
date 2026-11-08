/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.RegularVariation

import Mathlib.Tactic.NormNum

@[expose] public section

open MeasureTheory Filter
open scoped Topology
open MathlibExt.Probability.RegularVariation

namespace MathlibExtTest.Probability.RegularVariation

/-- The constant function `1` is slowly varying. -/
example : IsSlowlyVarying (fun _ => (1 : ℝ)) := isSlowlyVarying_one

/-- A positive constant function is slowly varying. -/
example : IsSlowlyVarying (fun _ => (2 : ℝ)) := isSlowlyVarying_const two_pos

/-- Slowly varying functions are closed under multiplication. -/
example : IsSlowlyVarying (fun x : ℝ => 2 * (1 + (1 + x)⁻¹)) :=
  (isSlowlyVarying_const two_pos).mul isSlowlyVarying_one_add_inv

/-- The power function is regularly varying of its exponent. -/
example : IsRegularlyVarying (fun x : ℝ => x ^ (3 : ℝ)) 3 :=
  isRegularlyVarying_rpow 3

/-- Products of powers are regularly varying, with indices adding. -/
example : IsRegularlyVarying ((fun x : ℝ => x ^ (2 : ℝ)) * (fun x : ℝ => x ^ (3 : ℝ)))
    (2 + 3) :=
  (isRegularlyVarying_rpow 2).mul (isRegularlyVarying_rpow 3)

/-- A positive constant multiple of a power is regularly varying. -/
example : IsRegularlyVarying (fun x : ℝ => 2 * x ^ (3 : ℝ)) 3 :=
  isRegularlyVarying_const_mul_rpow two_pos

/-- A regularly varying function is eventually positive. -/
example : ∀ᶠ x in atTop, 0 < (fun y : ℝ => 2 * y ^ (3 : ℝ)) x :=
  (isRegularlyVarying_const_mul_rpow (c := 2) (ρ := 3) two_pos).eventually_pos

/-- The right tail of a finite measure tends to `0`. -/
example (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Tendsto (rightTail μ) atTop (𝓝 0) :=
  tendsto_rightTail_atTop μ

/-- The combined tail of a finite measure tends to `0`. -/
example (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Tendsto (combinedTail μ) atTop (𝓝 0) :=
  tendsto_combinedTail_atTop μ

/-- The right tail is at most `1` for a probability measure. -/
example (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    rightTail μ x ≤ 1 :=
  rightTail_le_one μ x

/-- A Dirac mass has no defined tail-balance ratio eventually. -/
example (a : ℝ) : ¬ HasTailBalance (Measure.dirac a) 0 := not_hasTailBalance_dirac a 0

/-- A bounded-domain modification with value zero at `1` is still slowly varying. -/
theorem slowlyVarying_bounded_modification :
    let L : ℝ → ℝ := fun x => if x = 1 then 0 else 1
    IsSlowlyVarying L ∧ L 1 = 0 := by
  intro L
  constructor
  · apply isSlowlyVarying_one.of_eventuallyEq
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    simp [L, ne_of_gt hx]
  · simp [L]

/-- The atom at the excluded left boundary contributes neither to the strict tail
nor to `P(|X| > 1)`. -/
theorem strict_left_boundary_atom :
    leftTail (Measure.dirac (-1 : ℝ)) 1 = 0 ∧
    combinedTail (Measure.dirac (-1 : ℝ)) 1 = 0 ∧
    (Measure.dirac (-1 : ℝ) {y : ℝ | (1 : ℝ) < |y|}).toReal = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [leftTail, combinedTail, rightTail, Measure.dirac_apply]

/-- Totalized `0/0` cannot give the zero measure a tail-balance parameter. -/
theorem zero_measure_not_tailBalance (p : ℝ) : ¬ HasTailBalance (0 : Measure ℝ) p := by
  apply not_hasTailBalance_of_eventually_combinedTail_eq_zero
  filter_upwards with x
  simp [combinedTail, rightTail, leftTail]

/-- The zero-right-tail criterion now requires an actually positive denominator. -/
example (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hzero : ∀ᶠ x in atTop, rightTail μ x = 0)
    (hpos : ∀ᶠ x in atTop, 0 < combinedTail μ x) : HasTailBalance μ 0 :=
  hasTailBalance_zero_of_eventually_rightTail_eq_zero μ hzero hpos

#print axioms tendsto_combinedTail_atTop
#print axioms IsRegularlyVarying.mul
#print axioms not_hasTailBalance_dirac
#print axioms IsSlowlyVarying.mul


/-- An infinite negative atom and a finite positive atom on the actual real Borel space. -/
noncomputable def infiniteTailMeasure : Measure ℝ :=
  (⊤ : ENNReal) • Measure.dirac (-1 : ℝ) + Measure.dirac (1 : ℝ)

/-- One strict tail and the total mass are infinite; the other strict tail has mass one. -/
theorem infinite_tail_masses :
    infiniteTailMeasure (Set.Iio (0 : ℝ)) = ⊤ ∧
    infiniteTailMeasure (Set.Ioi (0 : ℝ)) = 1 ∧
    infiniteTailMeasure Set.univ = ⊤ := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [infiniteTailMeasure, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply, smul_eq_mul]

/-- The real projection loses the infinite left mass, leaving a positive denominator
and ratio one at threshold zero. This is a projection check, not asymptotic balance. -/
theorem infinite_tail_real_projection :
    leftTail infiniteTailMeasure 0 = 0 ∧
    rightTail infiniteTailMeasure 0 = 1 ∧
    0 < combinedTail infiniteTailMeasure 0 ∧
    rightTail infiniteTailMeasure 0 / combinedTail infiniteTailMeasure 0 = 1 := by
  rcases infinite_tail_masses with ⟨hl, hr, _⟩
  norm_num [leftTail, rightTail, combinedTail, hl, hr]

/-- The fixture cannot supply the finite-measure instance required by tail balance. -/
theorem infinite_tail_not_finite : ¬ IsFiniteMeasure infiniteTailMeasure := by
  exact not_isFiniteMeasure_iff.mpr infinite_tail_masses.2.2

end MathlibExtTest.Probability.RegularVariation
