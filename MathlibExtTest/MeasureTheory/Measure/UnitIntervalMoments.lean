/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.Measure.UnitIntervalMoments

/-! # Tests for mixed moments on `[0, 1]` -/

@[expose] public section

open MeasureTheory unitInterval

/-- The zeroth moment includes all the mass, including any endpoint atoms. -/
example (μ : Measure I) [IsFiniteMeasure μ] : unitIntervalMoment μ 0 0 = μ.real Set.univ := by
  simp [unitIntervalMoment]

/-- An atom at `0` contributes to complementary powers, but not to positive powers of `x`. -/
example (b : ℕ) : unitIntervalMoment (Measure.dirac 0) 0 b = 1 ∧
    unitIntervalMoment (Measure.dirac 0) 1 b = 0 := by
  simp [unitIntervalMoment]

/-- Degree elevation splits a mixed moment without binomial coefficients. -/
example (μ : Measure I) [IsFiniteMeasure μ] :
    unitIntervalMoment μ 2 3 = unitIntervalMoment μ 2 4 + unitIntervalMoment μ 3 3 :=
  unitIntervalMoment_rec μ 2 3
