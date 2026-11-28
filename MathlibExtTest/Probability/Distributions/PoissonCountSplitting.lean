/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Distributions.PoissonCountSplitting
import Mathlib.Tactic.NormNum

/-! # Regressions for Poisson count splitting -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal unitInterval

namespace MathlibExtTest.Probability.Distributions.PoissonCountSplitting

private noncomputable def quarter : I := ⟨1 / 4, by constructor <;> norm_num⟩

-- At p = 0, no positive first count has mass; at p = 1, no positive remainder does.
example (r : ℝ≥0) : poissonBinomialSplit r (0 : I) {(1, 0)} = 0 := by
  rw [poissonBinomialSplit_singleton, binomial_singleton]
  simp

example (r : ℝ≥0) : poissonBinomialSplit r (1 : I) {(0, 1)} = 0 := by
  rw [poissonBinomialSplit_singleton, binomial_singleton]
  simp

-- Rate zero places all mass on the pair of zeros, regardless of the split probability.
example (p : I) : poissonBinomialSplit 0 p = Measure.dirac (0, 0) := by
  rw [poissonBinomialSplit_eq_prod, mul_zero, mul_zero]
  have hz : poissonMeasure 0 = Measure.dirac (0 : ℕ) := by
    apply Measure.ext_of_singleton
    intro n
    cases n <;> simp [poissonMeasure_singleton]
  rw [hz, Measure.dirac_prod_dirac]

-- Distinct rates and an asymmetric split check both coordinates after regrouping.
example :
    (Measure.pi (fun i : Bool => poissonBinomialSplit (if i then 8 else 4) quarter)).map
        (fun x : Bool → ℕ × ℕ => ((fun i => (x i).1), (fun i => (x i).2))) =
      (Measure.pi (fun i : Bool => poissonMeasure (if i then 2 else 1))).prod
        (Measure.pi (fun i : Bool => poissonMeasure (if i then 6 else 3))) := by
  rw [pi_poissonBinomialSplit_eq_prod]
  have hp : unitInterval.toNNReal quarter = 1 / 4 := by
    apply NNReal.eq
    norm_num [quarter]
  have hq : unitInterval.toNNReal (unitInterval.symm quarter) = 3 / 4 := by
    apply NNReal.eq
    norm_num [quarter, unitInterval.coe_symm_eq]
  rw [hp, hq]
  have hr₁ (i : Bool) : (1 / 4 : ℝ≥0) * (if i then 8 else 4) = if i then 2 else 1 := by
    cases i <;> norm_num
  have hr₂ (i : Bool) : (3 / 4 : ℝ≥0) * (if i then 8 else 4) = if i then 6 else 3 := by
    cases i <;> norm_num
  simp only [hr₁, hr₂]

end MathlibExtTest.Probability.Distributions.PoissonCountSplitting
