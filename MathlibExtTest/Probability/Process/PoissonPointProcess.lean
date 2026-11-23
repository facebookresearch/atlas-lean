/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Process.PoissonPointProcess

@[expose] public section

open Function MeasureTheory ProbabilityTheory Set MathlibExt.Probability.PoissonPointProcess
open scoped ENNReal NNReal

namespace MathlibExtTest.Probability.Process.PoissonPointProcess

variable {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsFiniteMeasure μ]

/-! ### Non-vacuity: the construction is a probability measure for any finite intensity -/

example : IsProbabilityMeasure (poissonPointProcess μ) := inferInstance

/-- A concrete intensity: two atoms on `Bool` with masses `1` and `2`. -/
noncomputable def boolIntensity : Measure Bool :=
  Measure.dirac true + 2 • Measure.dirac false

instance : IsFiniteMeasure boolIntensity := by
  unfold boolIntensity; infer_instance

example : IsProbabilityMeasure (poissonPointProcess boolIntensity) := inferInstance

/-! ### Counts -/

/-- The total number of points has the Poisson law of mean `μ(E)`. -/
example : (poissonPointProcess μ).map (fun η => η univ) =
    (poissonMeasure (μ univ).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞) :=
  map_apply_eq_poissonMeasure μ MeasurableSet.univ

/-- On `Bool`, the counts at `true` and at `false` are independent Poisson variables. -/
example : (poissonPointProcess boolIntensity).map (fun η b => η {b}) =
    Measure.pi fun b => (poissonMeasure (boolIntensity {b}).toNNReal).map
      (Nat.cast : ℕ → ℝ≥0∞) :=
  map_apply_pi _ _ (fun _ => measurableSet_singleton _)
    (fun _ _ h => Set.disjoint_singleton.2 h)

/-! ### Campbell, Laplace and Mecke on simple functionals -/

/-- Campbell with `f = 1`: the mean number of points is `μ(E)`. -/
example : ∫⁻ η, η univ ∂(poissonPointProcess μ) = μ univ := by
  simpa using lintegral_lintegral μ (f := fun _ => 1) measurable_const

/-- Laplace functional at `f = 0` (boundary): both sides equal `1`. -/
example : ∫ η, Real.exp (-(∫⁻ _, ((0 : ℝ≥0) : ℝ≥0∞) ∂η).toReal) ∂(poissonPointProcess μ) =
    1 := by
  rw [integral_exp_neg μ (f := fun _ => 0) measurable_const]
  simp

/-- Mecke with `h(x, η) = η(E)` gives the second moment of the total count,
`E η(E)² = μ(E) (μ(E) + 1)`, the Poisson value. -/
example : ∫⁻ η, η univ * η univ ∂(poissonPointProcess μ) = μ univ * (μ univ + 1) := by
  have hh : Measurable (Function.uncurry fun (_ : E) (η : Measure E) => η univ) :=
    (Measure.measurable_coe MeasurableSet.univ).comp measurable_snd
  have hm := lintegral_lintegral_mecke μ hh
  have hmean : ∫⁻ η, η univ ∂(poissonPointProcess μ) = μ univ := by
    simpa using lintegral_lintegral μ (f := fun _ => 1) measurable_const
  simp only [lintegral_const, Measure.add_apply, Measure.dirac_apply_of_mem (mem_univ _)] at hm
  rw [hm, lintegral_add_right _ measurable_const, hmean, lintegral_const,
    measure_univ (μ := poissonPointProcess μ), mul_one, mul_comm]

/-! ### Mapping -/

/-- Forgetting positions maps the process to the Poisson process on a point with mass `μ(E)`. -/
example : (poissonPointProcess μ).map (fun η => η.map (fun _ => ())) =
    poissonPointProcess (μ.map fun _ => ()) :=
  map_map μ measurable_const

end MathlibExtTest.Probability.Process.PoissonPointProcess
