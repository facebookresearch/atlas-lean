/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.LatentVariable.BernoulliMixture

/-!
# Bernoulli-mixture EM tests

Closed checks: the theorems instantiated for a two-component mixture on binary vectors of length
3, including the monotone log-likelihood along the EM iterates, the M-step maximizing `Q` against an
arbitrary valid candidate, and the two-point bound behind the coordinate update. The definitions
are real-valued and not executable.
-/

namespace Cslib.MachineLearning.LatentVariable.BernoulliMixture

open Real Cslib.MachineLearning.LatentVariable.ExpectationMaximization

example (xs : Fin 6 → Fin 3 → Bool) (hx : Rich xs) (θ₀ : ValidParams 3 2) {s t : ℕ}
    (hst : s ≤ t) :
    logLik joint xs ((emStep xs hx)^[s] θ₀) ≤ logLik joint xs ((emStep xs hx)^[t] θ₀) :=
  logLik_iterate_emStep_monotone xs hx θ₀ hst

example (xs : Fin 6 → Fin 3 → Bool) (hx : Rich xs) (θ θ' : ValidParams 3 2) :
    emQ joint xs θ' θ ≤ emQ joint xs (emStep xs hx θ) θ :=
  emQ_le_emStep xs hx θ' θ

-- the two-point case: counts `(2, 3)` against any `p ∈ (0, 1)`
example (p : ℝ) (h0 : 0 < p) (h1 : p < 1) :
    ∑ b : Bool, (if b then (2 : ℝ) else 3) * log (if b then p else 1 - p) ≤
      ∑ b : Bool, (if b then (2 : ℝ) else 3) *
        log ((if b then (2 : ℝ) else 3) / ∑ b' : Bool, if b' then (2 : ℝ) else 3) :=
  sum_mul_log_le_sum_mul_log_div (fun b => by cases b <;> norm_num)
    (by simp; norm_num) (fun b => by cases b <;> simp [h0, h1])
    (by simp)

#print axioms logLik_iterate_emStep_monotone
#print axioms emQ_le_emStep

end Cslib.MachineLearning.LatentVariable.BernoulliMixture
