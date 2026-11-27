/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.StandardizedSelection

import MathlibExt.Probability.Statistics.Measurement.AffineLaws
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Linear linking of score scales -/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExt.Probability.Statistics.Measurement

/-- **Linear linking of score scales.** For positive source and target standard deviations
`σX` and `σY`, the map `x ↦ μY + (σY / σX) * (x - μX)` has inverse
`y ↦ μX + (σX / σY) * (y - μY)`. Applied to a square-integrable score with mean `μX` and
population standard deviation `σX`, it gives a score with mean `μY` and population standard
deviation `σY`. This is a change of score coordinates, not a statement that different test
forms are interchangeable. -/
theorem linear_score_scale_linking (μX μY : ℝ) {σX σY : ℝ}
    (hσX : 0 < σX) (hσY : 0 < σY) :
    let link := fun x : ℝ => μY + (σY / σX) * (x - μX)
    let unlink := fun y : ℝ => μX + (σX / σY) * (y - μY)
    Function.LeftInverse unlink link ∧ Function.RightInverse unlink link ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Ω → ℝ), MemLp X 2 P → (∫ ω, X ω ∂P) = μX → populationSD P X = σX →
          (∫ ω, link (X ω) ∂P) = μY ∧ populationSD P (fun ω => link (X ω)) = σY := by
  intro link unlink
  have hab : (σX / σY) * (σY / σX) = 1 := by
    field_simp [hσX.ne', hσY.ne']
  refine ⟨?_, ?_, ?_⟩
  · intro x
    change μX + (σX / σY) * (μY + (σY / σX) * (x - μX) - μY) = x
    rw [add_sub_cancel_left, ← mul_assoc, hab, one_mul]
    ring
  · intro y
    change μY + (σY / σX) * (μX + (σX / σY) * (y - μY) - μX) = y
    rw [add_sub_cancel_left, ← mul_assoc, mul_comm (σY / σX) (σX / σY), hab, one_mul]
    ring
  · intro Ω _ P _ X hX hmean hsd
    have ha : 0 < σY / σX := div_pos hσY hσX
    have hlink : (fun ω => link (X ω)) =
        fun ω => (σY / σX) * X ω + (μY - (σY / σX) * μX) := by
      funext ω
      dsimp only [link]
      ring
    constructor
    · change (∫ ω, (fun ω => link (X ω)) ω ∂P) = μY
      rw [hlink, integral_const_mul_add_const (hX.integrable one_le_two), hmean]
      ring
    · rw [hlink]
      unfold populationSD at hsd ⊢
      rw [variance_const_mul_add_const hX.aestronglyMeasurable,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ha.le, hsd, div_mul_cancel₀ _ hσX.ne']

end MathlibExt.Probability.Statistics.Measurement
