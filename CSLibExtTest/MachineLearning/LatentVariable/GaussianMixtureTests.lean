/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.LatentVariable.GaussianMixture

/-!
# Gaussian-mixture EM tests

Closed checks: the theorems instantiated for a three-component mixture in the plane, on five data
points that are not all equal. They cover the monotone log-likelihood along the EM iterates, the
M-step maximizing `Q` over arbitrary valid parameters, the responsibilities summing to one, and
the weighted mean minimizing weighted squared distances. The
definitions are real-valued and not executable.
-/

namespace Cslib.MachineLearning.LatentVariable.GaussianMixture

open Cslib.MachineLearning.LatentVariable.ExpectationMaximization

example (xs : Fin 5 → EuclideanSpace ℝ (Fin 2)) (hx : NotAllEqual xs) (θ₀ : ValidParams 2 3)
    {s t : ℕ} (hst : s ≤ t) :
    logLik joint xs ((emStep xs hx)^[s] θ₀) ≤ logLik joint xs ((emStep xs hx)^[t] θ₀) :=
  logLik_iterate_emStep_monotone xs hx θ₀ hst

example (xs : Fin 5 → EuclideanSpace ℝ (Fin 2)) (hx : NotAllEqual xs) (θ θ' : ValidParams 2 3) :
    emQ joint xs θ' θ ≤ emQ joint xs (emStep xs hx θ) θ :=
  emQ_le_emStep xs hx θ' θ

example (x : Fin 4 → EuclideanSpace ℝ (Fin 2)) (w : Fin 4 → ℝ) (hW : 0 < ∑ i, w i)
    (c : EuclideanSpace ℝ (Fin 2)) :
    ∑ i, w i * ‖x i - (∑ i, w i)⁻¹ • ∑ i, w i • x i‖ ^ 2 ≤ ∑ i, w i * ‖x i - c‖ ^ 2 :=
  sum_mul_norm_sub_sq_mean_le Finset.univ hW x c

example (θ : ValidParams 2 3) (x : EuclideanSpace ℝ (Fin 2)) : ∑ k, resp θ x k = 1 :=
  sum_resp θ x

#print axioms logLik_iterate_emStep_monotone
#print axioms emQ_le_emStep
#print axioms log_isoGaussPDF

end Cslib.MachineLearning.LatentVariable.GaussianMixture
