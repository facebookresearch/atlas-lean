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
open scoped InnerProductSpace

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

/-- A constant three-member ensemble solves the continuous-time ODE for arbitrary truth and
satisfies the collapse estimate for two distinct members. -/
example (a u_true t : ℝ) (ht : 0 < t) :
    let u : ℝ → Fin 3 → ℝ := fun _ _ ↦ a
    let A := ContinuousLinearMap.id ℝ ℝ
    let Γ := ContinuousLinearEquiv.refl ℝ ℝ
    |⟪A (u t 0 - ensembleMean (u t)), Γ.symm (A (u t 2 - ensembleMean (u t)))⟫_ℝ| ≤
      (3 : ℝ) / (2 * t) := by
  intro u A Γ
  have hmean (s : ℝ) : ensembleMean (u s) = a := by
    simp [u, ensembleMean]
  have hΓ : (Γ : ℝ →L[ℝ] ℝ).IsPositive := ContinuousLinearMap.isPositive_id
  refine MathlibExt.Probability.EnsembleKalmanWanted.eki_ensemble_collapse
    (A := A) (Γ := Γ) (hΓ := hΓ) (u_true := u_true) (u := u) (hode := ?_)
    (l := 0) (j := 2) (t := t) (ht := ht)
  intro s _ i
  rw [hmean s]
  simpa [u] using (hasDerivAt_const s a)

end MathlibExtTest.Probability.BayesianInverse.EnsembleKalman
