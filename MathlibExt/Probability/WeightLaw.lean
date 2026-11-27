/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Finite laws from real point masses

`weightLaw g` is the measure `∑ x, ENNReal.ofReal (g x) • δ_x` on a finite measurable space. For
`g ≥ 0` with `∑ x, g x = 1` it is a probability measure (`isProbabilityMeasure_weightLaw`), and
for `g ≥ 0` integration against it is the weighted sum `∑ x, g x * φ x` (`integral_weightLaw`)
and the mass of `{x}` is `g x` (`measureReal_weightLaw_singleton`), so nonnegative masses are
recovered from their law (`weightLaw_injOn_nonneg`). It is always a finite measure
(`isFiniteMeasure_weightLaw`).

It is the finite categorical law shared by the observation laws of
`MathlibExt.Probability.Statistics.Bayesian.FiniteConsistency` and the per-unit assignment laws
of `MathlibExt.Probability.Statistics.Experiment.Factorial`.
-/

@[expose] public section

namespace MathlibExt.Probability

open MeasureTheory

/-- The law on a finite space `𝓧` with real point masses `g x`:
`∑ x, ENNReal.ofReal (g x) • δ_x`. For `g ≥ 0` with `∑ x, g x = 1` it is a probability measure
(`isProbabilityMeasure_weightLaw`). -/
noncomputable def weightLaw {𝓧 : Type*} [Fintype 𝓧] [MeasurableSpace 𝓧] (g : 𝓧 → ℝ) :
    Measure 𝓧 :=
  ∑ x, ENNReal.ofReal (g x) • Measure.dirac x

/-- Nonnegative point masses summing to one give a probability measure. -/
theorem isProbabilityMeasure_weightLaw {𝓧 : Type*} [Fintype 𝓧] [MeasurableSpace 𝓧]
    (g : 𝓧 → ℝ) (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_sum : ∑ x, g x = 1) :
    IsProbabilityMeasure (weightLaw g) := by
  constructor
  rw [weightLaw, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hg_nonneg x), hg_sum, ENNReal.ofReal_one]

/-- `weightLaw g` is a finite measure: it has finitely many finite point masses. -/
instance isFiniteMeasure_weightLaw {𝓧 : Type*} [Fintype 𝓧] [MeasurableSpace 𝓧] (g : 𝓧 → ℝ) :
    IsFiniteMeasure (weightLaw g) := by
  constructor
  simp only [weightLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.sum_lt_top.2 fun _ _ => ENNReal.ofReal_lt_top

/-- With nonnegative point masses, the mass of a singleton is its point mass. -/
theorem measureReal_weightLaw_singleton {𝓧 : Type*} [Fintype 𝓧] [MeasurableSpace 𝓧]
    [MeasurableSingletonClass 𝓧] {g : 𝓧 → ℝ} (hg : ∀ x, 0 ≤ g x) (a : 𝓧) :
    (weightLaw g).real {a} = g a := by
  classical
  simp only [Measure.real, weightLaw, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, Measure.dirac_apply, Set.indicator, Set.mem_singleton_iff, Pi.one_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact ENNReal.toReal_ofReal (hg a)

/-- `weightLaw` is injective on nonnegative weights: the law determines its point masses. -/
theorem weightLaw_injOn_nonneg {𝓧 : Type*} [Fintype 𝓧] [MeasurableSpace 𝓧]
    [MeasurableSingletonClass 𝓧] :
    Set.InjOn (weightLaw (𝓧 := 𝓧)) {g | ∀ x, 0 ≤ g x} := by
  intro g hg g' hg' hgg
  funext x
  have h : (weightLaw g).real {x} = (weightLaw g').real {x} := by rw [hgg]
  rw [measureReal_weightLaw_singleton hg x, measureReal_weightLaw_singleton hg' x] at h
  exact h

/-- With nonnegative point masses, integration against `weightLaw g` is the weighted sum
`∑ x, g x * φ x`. -/
theorem integral_weightLaw {𝓧 : Type*} [Fintype 𝓧] [MeasurableSpace 𝓧]
    [MeasurableSingletonClass 𝓧] (g : 𝓧 → ℝ) (hg : ∀ x, 0 ≤ g x) (φ : 𝓧 → ℝ) :
    ∫ x, φ x ∂(weightLaw g) = ∑ x, g x * φ x := by
  rw [weightLaw, integral_finsetSum_measure fun x _ =>
    (Integrable.of_finite (μ := Measure.dirac x)).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hg x), smul_eq_mul]

end MathlibExt.Probability
