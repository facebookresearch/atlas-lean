/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Contiguity

/-!
# Tests for contiguity and Le Cam's lemmas

* Exponential tilting at concrete parameters and at the boundary `v = 0` (Dirac masses).
* Non-vacuity of the LAN hypotheses with a nonzero local parameter: the Gaussian shift
  experiment `N(0, 1)` against `N(h, 1)`, where `Λₙ(x) = h x - h² / 2` and `Sₙ = id`. Le Cam's
  first lemma gives contiguity and the third lemma gives `id → N(h, 1)` under the tilted
  measures, which are `N(h, 1)` by the tilting identity.
* Contiguity is reflexive, and it transfers convergence in probability.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open MathlibExt.Probability.Statistics.Contiguity

namespace MathlibExtTest.Probability.Statistics.Contiguity

/-- Tilting `N(0, 4)` by `exp(x / 2 - 1 / 2)` (`h = 1/2`, `v = 4`) gives `N(2, 4)`. -/
example : (gaussianReal 0 4).withDensity
    (fun x => ENNReal.ofReal (Real.exp (1 / 2 * x - (1 / 2) ^ 2 * ((4 : ℝ≥0) : ℝ) / 2))) =
      gaussianReal 2 4 := by
  rw [gaussianReal_withDensity_exp]; norm_num

/-- Boundary `v = 0`: the tilted Dirac mass at `0` is the Dirac mass at `0`. -/
example (h : ℝ) : (Measure.dirac (0 : ℝ)).withDensity
    (fun x => ENNReal.ofReal (Real.exp (h * x - h ^ 2 * ((0 : ℝ≥0) : ℝ) / 2))) =
      Measure.dirac 0 := by
  simpa using gaussianReal_withDensity_exp h 0

/-- Contiguity is reflexive. -/
example {Ω : Type*} [MeasurableSpace Ω] (P : ℕ → Measure Ω) : IsContiguous P P :=
  fun _ _ h => h

/-- The tilted measures of the Gaussian shift experiment are probability measures. -/
instance (h : ℝ) : IsProbabilityMeasure ((gaussianReal 0 1).withDensity
    fun x => ENNReal.ofReal (Real.exp (h * x - h ^ 2 * ((1 : ℝ≥0) : ℝ) / 2))) := by
  rw [gaussianReal_withDensity_exp]; infer_instance

/-- The LAN hypothesis holds exactly in the Gaussian shift experiment. -/
theorem tendstoInMeasure_gaussianShift (h : ℝ) :
    TendstoInMeasure (gaussianReal 0 1)
      (fun (_ : ℕ) (x : ℝ) => (h * x - h ^ 2 * ((1 : ℝ≥0) : ℝ) / 2) - h * x) atTop
      (fun _ => -(h ^ 2 * ((1 : ℝ≥0) : ℝ) / 2)) := by
  refine tendstoInMeasure_of_tendsto_ae (fun _ => by fun_prop) (Eventually.of_forall fun x => ?_)
  refine tendsto_const_nhds.congr fun n => ?_
  ring

/-- **Non-vacuity of Le Cam's first lemma** with `h ≠ 0`: `N(h, 1)` (constant sequence) is
contiguous with respect to `N(0, 1)`. -/
example (h : ℝ) : IsContiguous
    (fun _ => (gaussianReal 0 1).withDensity fun x => ENNReal.ofReal
      (Real.exp (h * x - h ^ 2 * ((1 : ℝ≥0) : ℝ) / 2)))
    (fun _ => gaussianReal 0 1) :=
  isContiguous_withDensity_exp (Λ := fun _ x => h * x - h ^ 2 * ((1 : ℝ≥0) : ℝ) / 2)
    (S := fun _ x => x) (fun _ => by fun_prop)
    (tendstoInDistribution_const aemeasurable_id) (tendstoInMeasure_gaussianShift h)

/-- **Non-vacuity of Le Cam's third lemma** with `h ≠ 0`: under the tilted measures the central
sequence `id` has the limit `N(h, 1)`. -/
example (h : ℝ) : TendstoInDistribution (fun (_ : ℕ) (x : ℝ) => x) atTop id
    (fun _ => (gaussianReal 0 1).withDensity fun x => ENNReal.ofReal
      (Real.exp (h * x - h ^ 2 * ((1 : ℝ≥0) : ℝ) / 2)))
    (gaussianReal (h * ((1 : ℝ≥0) : ℝ)) 1) :=
  tendstoInDistribution_withDensity_exp (Λ := fun _ x => h * x - h ^ 2 * ((1 : ℝ≥0) : ℝ) / 2)
    (S := fun _ x => x) (fun _ => by fun_prop)
    (tendstoInDistribution_const aemeasurable_id) (tendstoInMeasure_gaussianShift h)

/-- Contiguity transfers convergence in probability (here of a constant sequence). -/
example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : ℕ → Measure Ω) (hQ : IsContiguous Q (fun _ => P)) :
    Tendsto (fun n => Q n {ω | (1 : ℝ) ≤ |(fun (_ : ℕ) (_ : Ω) => (3 : ℝ)) n ω - 3|}) atTop
      (𝓝 0) :=
  hQ.tendsto_measure_abs_sub_ge (fun _ => measurable_const)
    (tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (Eventually.of_forall fun _ => tendsto_const_nhds)) one_pos

#print axioms isContiguous_withDensity_exp
#print axioms tendstoInDistribution_withDensity_exp

end MathlibExtTest.Probability.Statistics.Contiguity
