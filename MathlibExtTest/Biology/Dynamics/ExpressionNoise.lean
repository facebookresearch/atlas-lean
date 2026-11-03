/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.ExpressionNoise

/-! Tests for the intrinsic/extrinsic noise decomposition: a non-vacuity witness of
`IsIdenticalReporterPair` (one reporter observed twice when the extrinsic σ-algebra is
everything, so all noise is extrinsic), and the two-reporter identity on it. -/

open MeasureTheory ProbabilityTheory

namespace MathlibExtTest.Biology.Dynamics.ExpressionNoise

open MathlibExt.Biology.Dynamics.ExpressionNoise

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Non-vacuity witness.** If the extrinsic σ-algebra is the whole σ-algebra, a
square-integrable reporter paired with itself satisfies the hypotheses. -/
example {X : Ω → ℝ} (hX : MemLp X 2 μ) (hXm : StronglyMeasurable X) :
    IsIdenticalReporterPair ‹MeasurableSpace Ω› μ X X := by
  have hXX : Integrable (X * X) μ := hX.integrable_mul hX
  refine ⟨ae_eq_refl _, ae_eq_refl _, ?_⟩
  rw [condExp_of_stronglyMeasurable le_rfl (hXm.mul hXm) hXX,
    condExp_of_stronglyMeasurable le_rfl hXm (hX.integrable one_le_two)]

/-- In that case there is no intrinsic noise. -/
example (X : Ω → ℝ) : intrinsicNoiseSq μ X X = 0 := by simp [intrinsicNoiseSq]

/-- The two-reporter identity on independent-looking constants: all strengths vanish. -/
example : totalNoiseSq μ (fun _ ↦ (2 : ℝ)) (fun _ ↦ 2) =
    intrinsicNoiseSq μ (fun _ ↦ (2 : ℝ)) (fun _ ↦ 2) +
      extrinsicNoiseSq μ (fun _ ↦ (2 : ℝ)) (fun _ ↦ 2) :=
  totalNoiseSq_eq_add (memLp_const 2) (memLp_const 2)

example : extrinsicNoiseSq μ (fun _ ↦ (2 : ℝ)) (fun _ ↦ 2) = 0 := by
  simp [extrinsicNoiseSq]

/-- Junk value: a zero-mean reporter pair has all noise strengths `0` (`x / 0 = 0`). -/
example : totalNoiseSq μ (fun _ ↦ (0 : ℝ)) (fun _ ↦ 0) = 0 := by simp [totalNoiseSq]

end MathlibExtTest.Biology.Dynamics.ExpressionNoise
