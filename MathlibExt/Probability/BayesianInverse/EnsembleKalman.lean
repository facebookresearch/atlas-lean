/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Ensemble Kalman inversion: the invariant subspace property

Ensemble Kalman inversion (EKI) solves an inverse problem `y = G(u) + η`, with unknown `u` in a
real vector space `X` and data in a real inner product space `F`, by moving an ensemble
`u⁽¹⁾, …, u⁽ᴶ⁾` with the Kalman update

`u⁽ʲ⁾ₙ₊₁ = u⁽ʲ⁾ₙ + C^{up}(uₙ) (C^{pp}(uₙ) + Γ)⁻¹ (y⁽ʲ⁾ₙ₊₁ - G(u⁽ʲ⁾ₙ))`,

where, with ensemble means `ū` and `Ḡ = (1/J) Σ G(u⁽ᵏ⁾)`,

* `C^{up}(u) d = (1/J) Σₖ ⟨G(u⁽ᵏ⁾) - Ḡ, d⟩ (u⁽ᵏ⁾ - ū)` is the cross-covariance,
* `C^{pp}(u) d = (1/J) Σₖ ⟨G(u⁽ᵏ⁾) - Ḡ, d⟩ (G(u⁽ᵏ⁾) - Ḡ)` is the output covariance,

and `y⁽ʲ⁾ₙ₊₁` are the (possibly perturbed) data (Iglesias, Law and Stuart, *Ensemble Kalman
methods for inverse problems*, Inverse Problems 29 (2013), arXiv:1209.2736, equations (19)-(25);
Schillings and Stuart, *Analysis of the ensemble Kalman filter for inverse problems*, SIAM J.
Numer. Anal. 55 (2017), arXiv:1602.02020, equations (4)-(5), where `Γ` is replaced by `h⁻¹Γ`).

## Main results

* `ekiStep`: one EKI update. The inverse of `C^{pp} + Γ` is `Ring.inverse` in the endomorphism
  ring of `F`, which is the true inverse whenever `C^{pp} + Γ` is invertible (for instance
  when `F` is finite-dimensional and `Γ` is positive definite).
* `ekiStep_mem` and `eki_mem_span` (**invariant subspace property**, Iglesias-Law-Stuart
  Theorem 2.1; Schillings-Stuart Lemma 1): every ensemble member, at every step, lies in the
  linear span of the initial ensemble. This holds for every forward map `G`, every `Γ` and every
  choice of perturbed data.
* `infDist_le_dist_ensembleMean` (Iglesias-Law-Stuart Corollary 2.3): the error of the ensemble
  mean is at least the distance from the truth to that span.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.BayesianInverse

open scoped InnerProductSpace

variable {X F : Type*} [AddCommGroup X] [Module ℝ X] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] {J : ℕ}

/-- **Ensemble mean.** `(1/J) Σⱼ v⁽ʲ⁾` for an ensemble `v : Fin J → X`. -/
noncomputable def ensembleMean {V : Type*} [AddCommGroup V] [Module ℝ V] (v : Fin J → V) : V :=
  (J : ℝ)⁻¹ • ∑ j, v j

/-- **EKI cross-covariance applied to a vector.**
`C^{up}(u) d = (1/J) Σₖ ⟨G(u⁽ᵏ⁾) - Ḡ, d⟩ (u⁽ᵏ⁾ - ū)` (Schillings and Stuart, arXiv:1602.02020,
equation (5); Iglesias, Law and Stuart, arXiv:1209.2736, equations (20) and (22)). -/
noncomputable def crossCov (G : X → F) (u : Fin J → X) (d : F) : X :=
  (J : ℝ)⁻¹ • ∑ k, ⟪G (u k) - ensembleMean (G ∘ u), d⟫_ℝ • (u k - ensembleMean u)

/-- **EKI output covariance.** The linear map
`C^{pp}(u) d = (1/J) Σₖ ⟨G(u⁽ᵏ⁾) - Ḡ, d⟩ (G(u⁽ᵏ⁾) - Ḡ)` (Schillings and Stuart,
arXiv:1602.02020, equation (5); Iglesias, Law and Stuart, arXiv:1209.2736, equation (21)). -/
noncomputable def outputCov (G : X → F) (u : Fin J → X) : F →ₗ[ℝ] F where
  toFun d := (J : ℝ)⁻¹ • ∑ k, ⟪G (u k) - ensembleMean (G ∘ u), d⟫_ℝ •
    (G (u k) - ensembleMean (G ∘ u))
  map_add' d₁ d₂ := by
    simp only [inner_add_right, add_smul, Finset.sum_add_distrib, smul_add]
  map_smul' c d := by
    simp only [inner_smul_right, RingHom.id_apply, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    congr 1; ring

/-- **One step of ensemble Kalman inversion.**
`u⁽ʲ⁾ ↦ u⁽ʲ⁾ + C^{up}(u) (C^{pp}(u) + Γ)⁻¹ (y⁽ʲ⁾ - G(u⁽ʲ⁾))`, with the inverse taken by
`Ring.inverse` in `F →ₗ[ℝ] F` (Iglesias, Law and Stuart, arXiv:1209.2736, equation (25);
Schillings and Stuart, arXiv:1602.02020, equation (4) with `Γ ↦ h⁻¹Γ`). -/
noncomputable def ekiStep (G : X → F) (Γ : F →ₗ[ℝ] F) (u : Fin J → X) (y : Fin J → F) :
    Fin J → X :=
  fun j ↦ u j + crossCov G u (Ring.inverse (outputCov G u + Γ) (y j - G (u j)))

/-- **The ensemble mean stays in a subspace.** The ensemble mean of members of a subspace lies in
that subspace. -/
theorem ensembleMean_mem {V : Type*} [AddCommGroup V] [Module ℝ V] (S : Submodule ℝ V)
    {v : Fin J → V} (hv : ∀ j, v j ∈ S) : ensembleMean v ∈ S :=
  S.smul_mem _ (S.sum_mem fun j _ ↦ hv j)

/-- **The cross-covariance stays in the ensemble's subspace.** The cross-covariance of an ensemble
in a subspace takes values in that subspace: it is a
linear combination of the deviations `u⁽ᵏ⁾ - ū`. -/
theorem crossCov_mem (S : Submodule ℝ X) (G : X → F) {u : Fin J → X} (hu : ∀ j, u j ∈ S)
    (d : F) : crossCov G u d ∈ S :=
  S.smul_mem _ (S.sum_mem fun k _ ↦ S.smul_mem _ (S.sub_mem (hu k) (ensembleMean_mem S hu)))

/-- **One EKI step preserves every subspace containing the ensemble.** If every `u⁽ʲ⁾` lies in a
subspace `S`, so does every member of `ekiStep G Γ u y`, for any forward map `G`, any `Γ` and any
data `y` (the inductive step in the proof of Theorem 2.1 of Iglesias, Law and Stuart,
arXiv:1209.2736). -/
theorem ekiStep_mem (S : Submodule ℝ X) (G : X → F) (Γ : F →ₗ[ℝ] F) {u : Fin J → X}
    (hu : ∀ j, u j ∈ S) (y : Fin J → F) (j : Fin J) : ekiStep G Γ u y j ∈ S :=
  S.add_mem (hu j) (crossCov_mem S G hu _)

/-- **Invariant subspace property of ensemble Kalman inversion.** If `uₙ₊₁ = ekiStep G Γ uₙ yₙ₊₁`
for all `n`, then every ensemble member `u⁽ʲ⁾ₙ` lies in the linear span of the initial ensemble
`{u⁽¹⁾₀, …, u⁽ᴶ⁾₀}` (Iglesias, Law and Stuart, arXiv:1209.2736, Theorem 2.1; Schillings and
Stuart, arXiv:1602.02020, Lemma 1). -/
theorem eki_mem_span (G : X → F) (Γ : F →ₗ[ℝ] F) (u : ℕ → Fin J → X) (y : ℕ → Fin J → F)
    (hstep : ∀ n, u (n + 1) = ekiStep G Γ (u n) (y (n + 1))) (n : ℕ) (j : Fin J) :
    u n j ∈ Submodule.span ℝ (Set.range (u 0)) := by
  induction n generalizing j with
  | zero => exact Submodule.subset_span ⟨j, rfl⟩
  | succ n ih => rw [hstep n]; exact ekiStep_mem _ G Γ ih _ j

/-- **The EKI estimate cannot beat the best approximation from the initial span.** With
`uₙ₊₁ = ekiStep G Γ uₙ yₙ₊₁`, the ensemble mean satisfies
`‖ūₙ - u†‖ ≥ inf_{v ∈ A} ‖v - u†‖`, where `A` is the span of the initial ensemble (Iglesias, Law
and Stuart, arXiv:1209.2736, Corollary 2.3). -/
theorem infDist_le_dist_ensembleMean {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (G : X → F) (Γ : F →ₗ[ℝ] F) (u : ℕ → Fin J → X) (y : ℕ → Fin J → F)
    (hstep : ∀ n, u (n + 1) = ekiStep G Γ (u n) (y (n + 1))) (n : ℕ) (u_true : X) :
    Metric.infDist u_true (Submodule.span ℝ (Set.range (u 0)) : Set X) ≤
      ‖ensembleMean (u n) - u_true‖ := by
  rw [← dist_eq_norm, dist_comm]
  exact Metric.infDist_le_dist_of_mem
    (ensembleMean_mem _ fun j ↦ eki_mem_span G Γ u y hstep n j)

end MathlibExt.Probability.BayesianInverse
