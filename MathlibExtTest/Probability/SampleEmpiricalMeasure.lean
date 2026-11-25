/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.SampleEmpiricalMeasure
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Tests for empirical measures of a sample
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal
open MathlibExt.Probability.SampleEmpiricalMeasure

namespace MathlibExtTest.Probability.SampleEmpiricalMeasure

/-- The empirical measure of the first three natural numbers (as reals) is the average of the
three Dirac masses. -/
example : (sampleEmpiricalMeasure (fun i : ℕ => (i : ℝ)) 3 : Measure ℝ) =
    (3 : ℝ≥0∞)⁻¹ • ∑ i ∈ range 3, Measure.dirac ((i : ℕ) : ℝ) := by
  simpa using toMeasure_sampleEmpiricalMeasure (fun i : ℕ => (i : ℝ)) (n := 3) (by norm_num)

/-- A constant sample puts full empirical mass on its value. -/
example (n : ℕ) (hn : n ≠ 0) :
    (sampleEmpiricalMeasure (fun _ : ℕ => (5 : ℝ)) n : Measure ℝ) {5} = 1 := by
  rw [sampleEmpiricalMeasure_apply _ hn (measurableSet_singleton 5)]
  simp [ENNReal.inv_mul_cancel (by exact_mod_cast hn) (ENNReal.natCast_ne_top n)]

end MathlibExtTest.Probability.SampleEmpiricalMeasure
