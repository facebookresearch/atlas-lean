/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.StieltjesMeasureConstruction

import Mathlib.Probability.CDF

/-!
# Tests for the construction of measures on ℝ from Stieltjes functions

Concrete instantiation for the CDF of the Dirac mass at `0`: its Stieltjes
measure is a probability measure assigning the interval `(-1, 1]` mass `1`.
Also, the two public theorems are restated with their exact signatures, and
`#print axioms` checks that they depend only on the standard axioms.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology
open MathlibExt.Probability.StieltjesMeasureConstruction

namespace MathlibExtTest.Probability.StieltjesMeasureConstruction

/-- The CDF of the Dirac mass at `0` equals `1` at `1`: `0 ∈ Iic 1`. -/
private lemma cdf_dirac_zero_one :
    ProbabilityTheory.cdf (Measure.dirac (0 : ℝ)) 1 = 1 := by
  have h := ProbabilityTheory.ofReal_cdf (Measure.dirac (0 : ℝ)) 1
  rw [Measure.dirac_apply_of_mem (show (0 : ℝ) ∈ Set.Iic 1 by norm_num)] at h
  have h2 : ENNReal.ofReal (ProbabilityTheory.cdf (Measure.dirac (0 : ℝ)) 1) =
      ENNReal.ofReal 1 := by
    rw [h, ENNReal.ofReal_one]
  exact (ENNReal.ofReal_eq_ofReal_iff
    (ProbabilityTheory.cdf_nonneg (Measure.dirac (0 : ℝ)) 1) zero_le_one).mp h2

/-- The CDF of the Dirac mass at `0` equals `0` at `-1`: `0 ∉ Iic (-1)`. -/
private lemma cdf_dirac_zero_neg_one :
    ProbabilityTheory.cdf (Measure.dirac (0 : ℝ)) (-1) = 0 := by
  have h := ProbabilityTheory.ofReal_cdf (Measure.dirac (0 : ℝ)) (-1)
  have hdirac : Measure.dirac (0 : ℝ) (Set.Iic (-1)) = 0 := by
    rw [Measure.dirac_apply]
    simp
  rw [hdirac] at h
  have hle : ProbabilityTheory.cdf (Measure.dirac (0 : ℝ)) (-1) ≤ 0 :=
    ENNReal.ofReal_eq_zero.mp h
  exact le_antisymm hle (ProbabilityTheory.cdf_nonneg (Measure.dirac (0 : ℝ)) (-1))

/-- The main theorem, restated with its exact public signature. -/
example (f : StieltjesFunction ℝ)
    (hf_bot : Tendsto f atBot (𝓝 0)) (hf_top : Tendsto f atTop (𝓝 1)) :
    IsProbabilityMeasure f.measure ∧
    (∀ a b : ℝ, a ≤ b → f.measure (Ioc a b) = ENNReal.ofReal (f b - f a)) ∧
    (∀ ν : Measure ℝ, [IsFiniteMeasure ν] →
      (∀ a b : ℝ, a ≤ b → ν (Ioc a b) = ENNReal.ofReal (f b - f a)) →
      ν = f.measure) :=
  stieltjes_measure_construction f hf_bot hf_top

/-- The `∃!` form, restated with its exact public signature. -/
example (f : StieltjesFunction ℝ)
    (hf_bot : Tendsto f atBot (𝓝 0)) (hf_top : Tendsto f atTop (𝓝 1)) :
    ∃! μ : Measure ℝ, IsProbabilityMeasure μ ∧
      ∀ a b : ℝ, a ≤ b → μ (Ioc a b) = ENNReal.ofReal (f b - f a) :=
  exists_unique_probabilityMeasure_of_stieltjes f hf_bot hf_top

/-- Concretely: the Stieltjes measure of the CDF of the Dirac mass at `0`
is a probability measure. -/
example : IsProbabilityMeasure
    (ProbabilityTheory.cdf (Measure.dirac (0 : ℝ))).measure :=
  (stieltjes_measure_construction (ProbabilityTheory.cdf (Measure.dirac (0 : ℝ)))
    (ProbabilityTheory.tendsto_cdf_atBot _)
    (ProbabilityTheory.tendsto_cdf_atTop _)).1

/-- Concretely: that measure assigns the interval `(-1, 1]` mass `1`,
since the CDF jumps from `0` at `-1` to `1` at `1`. -/
example : (ProbabilityTheory.cdf (Measure.dirac (0 : ℝ))).measure (Ioc (-1) 1) = 1 := by
  obtain ⟨-, hIoc, -⟩ := stieltjes_measure_construction
    (ProbabilityTheory.cdf (Measure.dirac (0 : ℝ)))
    (ProbabilityTheory.tendsto_cdf_atBot _)
    (ProbabilityTheory.tendsto_cdf_atTop _)
  rw [hIoc (-1) 1 (by norm_num), cdf_dirac_zero_one, cdf_dirac_zero_neg_one]
  simp

#print axioms stieltjes_measure_construction
#print axioms exists_unique_probabilityMeasure_of_stieltjes

end MathlibExtTest.Probability.StieltjesMeasureConstruction
