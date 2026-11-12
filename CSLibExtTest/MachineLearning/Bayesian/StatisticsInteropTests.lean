/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Bayesian.StatisticsInterop

@[expose] public section

namespace CSLibExtTest.MachineLearning.Bayesian.StatisticsInteropNormal

open MeasureTheory ProbabilityTheory Real
open Cslib.MachineLearning.Bayesian
open scoped ENNReal NNReal

/-- Use case: standard prior `N(0, 1)`, unit noise. The marginal-law posterior is almost
everywhere the candidate kernel, i.e. `N(x / 2, 1 / 2)`. -/
example :
    ∀ᵐ x ∂(gaussianLikelihood 1 ∘ₘ gaussianReal 0 1),
      ((gaussianLikelihood 1)†(gaussianReal 0 1)) x =
        gaussianReal (x / 2) (1 / 2) := by
  have h := posterior_gaussianMarginalLaw_one (0 : ℝ) (v₀ := (1 : ℝ≥0)) (v := (1 : ℝ≥0))
  filter_upwards [h] with x hx
  rw [hx, normalPosteriorKernel_apply 0 (by positivity) (by positivity) x]
  unfold normalPostMean normalPostVar
  norm_num

/-- Boundary: singletons have zero evidence, so no pointwise posterior formula fires. -/
example : (gaussianLikelihood 1 ∘ₘ gaussianReal 0 1) {(0 : ℝ)} = 0 := by
  rw [gaussianLikelihood_comp_gaussianReal 0 (by positivity) (by positivity)]
  exact gaussianReal_absolutelyContinuous 0 (by positivity) Real.volume_singleton

/-- Zero noise: the one-draw projection is the Dirac mass at the parameter. -/
example : (Measure.pi fun _ : Fin 1 => gaussianReal (0 : ℝ) 0).map (fun s => s 0) =
    Measure.dirac (0 : ℝ) := by
  rw [gaussianMarginalLaw_one_eq_gaussianLikelihood,
    gaussianLikelihood_zero_apply, gaussianReal_zero_var]

end CSLibExtTest.MachineLearning.Bayesian.StatisticsInteropNormal

namespace CSLibExtTest.MachineLearning.Bayesian.StatisticsInteropDirichlet

open MeasureTheory ProbabilityTheory
open Cslib.MachineLearning.Bayesian
open scoped ENNReal

/-- Use case: two labels with uniform probabilities. The one-sample categorical kernel is the
one-fold product of the one-draw categorical kernel. -/
example (hθ : (fun _ : Fin 2 => (1 / 2 : ℝ)) ∈ probVectors 1) :
    categoricalSeqKernel 1 1 (fun _ => (1 / 2 : ℝ)) =
      Measure.pi fun _ : Fin 1 => categoricalKernel 1 (fun _ => (1 / 2 : ℝ)) := by
  exact categoricalSeqKernel_eq_pi_categoricalKernel 1 1 _ hθ

/-- Use case: one observation of label `0`, uniform prior. The posterior is `Dir(2, 1)`. -/
example :
    bayesPosterior (categoricalSeqKernel 1 1) (dirichletMeasure (fun _ => (1 : ℝ)))
      (fun _ => (0 : Fin 2)) = dirichletMeasure ![2, 1] := by
  have h := posterior_sharedSeqLaw_bayesPosterior 1 1 (fun _ => (1 : ℝ)) (fun _ => one_pos)
    (fun _ => (0 : Fin 2))
  rw [h]
  congr 1
  funext i
  fin_cases i <;> simp [counts]; norm_num

/-- Use case: the `bayesPosterior` transport fires on the Laplace example. -/
example (s : Fin 1 → Fin 2) :
    bayesPosterior (categoricalSeqKernel 1 1) (dirichletMeasure (fun _ => (1 : ℝ))) s =
      dirichletMeasure (fun i => 1 + counts s i) := by
  exact posterior_sharedSeqLaw_bayesPosterior 1 1 _ (fun _ => one_pos) s

/-- Degenerate case: with no observations the posterior is the prior. -/
example (α : Fin 2 → ℝ) (hα : ∀ i, 0 < α i) (s : Fin 0 → Fin 2) :
    bayesPosterior (categoricalSeqKernel 1 0) (dirichletMeasure α) s =
      dirichletMeasure (fun i => α i + counts s i) := by
  exact posterior_sharedSeqLaw_bayesPosterior 1 0 α hα s

end CSLibExtTest.MachineLearning.Bayesian.StatisticsInteropDirichlet
