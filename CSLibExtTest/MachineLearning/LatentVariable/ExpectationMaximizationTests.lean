/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.LatentVariable.ExpectationMaximization
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Expectation-maximization tests

Closed checks: the theorems instantiated on a toy model with a two-valued latent variable,
`p θ x z = exp (-(x - θ - z)²)` on real data, including the monotone likelihood along the iterates
of an M-step given as a hypothesis, and Gibbs' inequality on explicit weights. The definitions are
real-valued and not executable; the Gaussian-mixture instance with an explicit M-step is a separate
module.
-/

namespace Cslib.MachineLearning.LatentVariable.ExpectationMaximization

open Real

/-- A toy model: a shifted Gaussian kernel with a two-valued latent shift. -/
noncomputable def toy (θ x : ℝ) (z : Fin 2) : ℝ := exp (-(x - θ - z) ^ 2)

theorem toy_pos (θ x : ℝ) (z : Fin 2) : 0 < toy θ x z := exp_pos _

example (xs : Fin 5 → ℝ) (θ : ℝ) {q : Fin 5 → Fin 2 → ℝ} (hq : ∀ n, IsDist (q n)) :
    elbo toy xs θ q ≤ logLik toy xs θ :=
  elbo_le_logLik toy_pos xs θ hq

example (xs : Fin 5 → ℝ) (θ : ℝ) :
    elbo toy xs θ (fun n => posterior toy θ (xs n)) = logLik toy xs θ :=
  elbo_posterior toy_pos xs θ

example (xs : Fin 5 → ℝ) (M : ℝ → ℝ) (hM : ∀ θ, emQ toy xs θ θ ≤ emQ toy xs (M θ) θ) (θ₀ : ℝ)
    {j k : ℕ} (hjk : j ≤ k) : logLik toy xs (M^[j] θ₀) ≤ logLik toy xs (M^[k] θ₀) :=
  logLik_iterate_monotone toy_pos xs hM θ₀ hjk

-- Gibbs' inequality on explicit weights: `q = (1/2, 1/2)`, `p = (1, 3)`
example : ∑ z : Fin 2, ![1/2, 1/2] z * (log (![1, 3] z) - log (![1/2, 1/2] z)) ≤
    log (∑ z : Fin 2, ![(1 : ℝ), 3] z) :=
  sum_mul_log_sub_le (fun z => by fin_cases z <;> norm_num)
    ⟨fun z => by fin_cases z <;> norm_num, by simp [Fin.sum_univ_two]; norm_num⟩

#print axioms logLik_iterate_monotone
#print axioms elbo_le_logLik
#print axioms emQ_sub_le_logLik_sub

end Cslib.MachineLearning.LatentVariable.ExpectationMaximization
