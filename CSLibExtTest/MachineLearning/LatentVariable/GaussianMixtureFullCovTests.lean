/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.LatentVariable.GaussianMixtureFullCov

open Cslib.MachineLearning.LatentVariable.GaussianMixtureFullCov
open Cslib.MachineLearning.LatentVariable.ExpectationMaximization
open Matrix WithLp MetaMathlibExt Real

-- Two distinct points on the line are in general position.
example : SpansAffinely
    (![toLp 2 ![0], toLp 2 ![1]] : Fin 2 → EuclideanSpace ℝ (Fin 1)) := by
  refine ⟨by norm_num, fun v hv => ⟨0, 1, ?_⟩⟩
  have hv0 : v 0 ≠ 0 := fun h => hv (by ext i; fin_cases i; simpa using h)
  simpa [EuclideanSpace.inner_eq_star_dotProduct, vecHead] using hv0.symm

-- The M-step's covariance update is positive definite on data in general position.
example (xs : Fin 5 → EuclideanSpace ℝ (Fin 2)) (hx : SpansAffinely xs) (θ : ValidParams 2 3)
    (k : Fin 3) : (newCov xs θ k).PosDef :=
  newCov_posDef hx θ k

-- EM for a full-covariance mixture never decreases the log-likelihood along its iterates.
example (xs : Fin 5 → EuclideanSpace ℝ (Fin 2)) (hx : SpansAffinely xs)
    (θ₀ : ValidParams 2 3) :
    Monotone fun t => logLik joint xs ((emStep xs hx)^[t] θ₀) :=
  logLik_iterate_emStep_monotone xs hx θ₀

#print axioms logLik_iterate_emStep_monotone
