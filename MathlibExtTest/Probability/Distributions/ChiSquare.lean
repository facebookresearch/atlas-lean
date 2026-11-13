/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.ChiSquare

/-!
# Tests for chi-square laws: no atoms

* `χ²₁` puts no mass at `0` (`chiSquareMeasure_singleton`), the fact that separates it from the
  degenerate limit `δ₀` in the monomorphic Hardy–Weinberg and zero-cell Pearson counterexamples.
* The `NullSingletonClass` instance: every countable set is `χ²_p`-null.
* Non-vacuity: `χ²₁` is a probability measure, so it is not the zero measure, yet each point,
  and the countable set `ℕ ⊆ ℝ`, is null; consequently `χ²₁ ≠ δ₀`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ChiSquareTest

/-- `χ²₁` has no atom at `0`. -/
example : chiSquareMeasure 1 {0} = 0 := chiSquareMeasure_singleton 1 0

/-- Through the instance, Mathlib's generic `measure_singleton` applies to every `χ²_p`. -/
example (p : ℕ) (x : ℝ) : chiSquareMeasure p {x} = 0 := measure_singleton x

/-- Every countable set is `χ²_p`-null; e.g. the natural numbers inside `ℝ`. -/
example (p : ℕ) : chiSquareMeasure p (Set.range ((↑) : ℕ → ℝ)) = 0 :=
  (Set.countable_range _).measure_zero _

/-- Non-vacuity: `χ²₁` has total mass `1`, so the atom statement is not about the zero
measure. -/
example : chiSquareMeasure 1 Set.univ = 1 := by
  have := isProbabilityMeasure_chiSquareMeasure one_pos
  exact measure_univ

/-- **`χ²₁` is not the point mass at `0`**: the Dirac mass gives `{0}` mass `1`, `χ²₁` gives it
mass `0`. -/
example : chiSquareMeasure 1 ≠ Measure.dirac 0 := by
  intro h
  have := chiSquareMeasure_singleton 1 0
  rw [h, Measure.dirac_apply_of_mem (Set.mem_singleton 0)] at this
  exact one_ne_zero this

end ChiSquareTest
