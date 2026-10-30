/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Bayesian.DirichletMultinomial

@[expose] public section

/-!
# Tests for Dirichlet–multinomial conjugacy
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Cslib.MachineLearning.Bayesian
open scoped ENNReal

namespace CSLibExtTest.MachineLearning.Bayesian.DirichletMultinomial

/-- Three labels, observed sequence `0, 2, 0, 0`. -/
def data : Fin 4 → Fin 3 := ![0, 2, 0, 0]

theorem counts_data : counts data = ![3, 0, 1] := by
  funext i
  fin_cases i <;> decide

/-- The likelihood of the sequence depends only on the counts. -/
example (θ : Fin 3 → ℝ) :
    seqLikelihood θ data = ENNReal.ofReal (θ 0) ^ 3 * ENNReal.ofReal (θ 2) := by
  rw [seqLikelihood_eq_prod_pow, counts_data]
  simp [Fin.prod_univ_three]

theorem uniform_pos : ∀ i, 0 < (![1, 1, 1] : Fin 3 → ℝ) i := fun i ↦ by fin_cases i <;> simp

instance : IsProbabilityMeasure (dirichletMeasure (![1, 1, 1] : Fin 3 → ℝ)) :=
  isProbabilityMeasure_dirichletMeasure uniform_pos

/-- After `0, 2, 0, 0` under a uniform `Dir(1, 1, 1)` prior, the posterior is `Dir(4, 1, 2)`. -/
example : ((categoricalSeqKernel 2 4)†(dirichletMeasure ![1, 1, 1])) data =
    dirichletMeasure ![4, 1, 2] := by
  rw [posterior_categoricalSeqKernel_dirichletMeasure uniform_pos, counts_data]
  congr 1
  funext i
  fin_cases i <;> norm_num

/-- Laplace smoothing: the next label is `0` with probability `(1 + 3) / (3 + 4) = 4/7`. -/
example : (categoricalKernel 2 ∘ₘ
      ((categoricalSeqKernel 2 4)†(dirichletMeasure ![1, 1, 1])) data) {0} =
    ENNReal.ofReal (4 / 7) := by
  rw [posterior_predictive_dirichletMeasure uniform_pos, counts_data]
  congr 1
  simp [Fin.sum_univ_three]
  norm_num

/-- An unseen label keeps positive predictive probability: `(1 + 0) / 7`. -/
example : (categoricalKernel 2 ∘ₘ
      ((categoricalSeqKernel 2 4)†(dirichletMeasure ![1, 1, 1])) data) {1} =
    ENNReal.ofReal (1 / 7) := by
  rw [posterior_predictive_dirichletMeasure uniform_pos, counts_data]
  congr 1
  simp [Fin.sum_univ_three]
  norm_num

end CSLibExtTest.MachineLearning.Bayesian.DirichletMultinomial
