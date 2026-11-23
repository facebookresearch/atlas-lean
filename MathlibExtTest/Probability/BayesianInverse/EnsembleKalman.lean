/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BayesianInverse.EnsembleKalman

@[expose] public section

open MathlibExt.Probability.BayesianInverse

namespace MathlibExtTest.Probability.BayesianInverse.EnsembleKalman

/-- A two-member ensemble in `ℝ³`, nonlinear scalar forward map `G(u) = u₀² + u₁`,
noise covariance `Γ = 1`: every iterate stays in the span of the initial members. -/
example (u : ℕ → Fin 2 → (Fin 3 → ℝ)) (y : ℕ → Fin 2 → ℝ)
    (hstep : ∀ n, u (n + 1) = ekiStep (fun v ↦ v 0 ^ 2 + v 1) LinearMap.id (u n) (y (n + 1)))
    (n : ℕ) (j : Fin 2) : u n j ∈ Submodule.span ℝ (Set.range (u 0)) :=
  eki_mem_span _ _ u y hstep n j

/-- If the initial ensemble is constant, EKI never moves away from that line. -/
example (a : ℝ) (G : ℝ → ℝ) (Γ : ℝ →ₗ[ℝ] ℝ) (y : Fin 3 → ℝ) (j : Fin 3) :
    ekiStep G Γ (fun _ ↦ a) y j ∈ Submodule.span ℝ {a} :=
  ekiStep_mem _ G Γ (fun _ ↦ Submodule.mem_span_singleton_self a) y j

end MathlibExtTest.Probability.BayesianInverse.EnsembleKalman
