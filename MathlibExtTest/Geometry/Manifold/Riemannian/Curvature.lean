/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.Manifold.Riemannian.VectorSpace

/-!
# Tests for the Riemannian curvature API

Public use of `Manifold.riemannCurvature`, `sectionalCurvature`, `ricci`, `scalarCurvature` and the
curvature-bound predicates: instance inference for the standard metric of Euclidean space, flatness
of `ℝⁿ` through the public API, the bounds that hold and fail on `ℝⁿ`, the vanishing of the
sectional-curvature formula on dependent vectors, and a statement-shaped use on an abstract closed
Riemannian manifold.
-/

open Bundle Manifold
open scoped Manifold ContDiff

namespace RiemannianCurvatureTests

/-- The standard metric of `ℝⁿ` is found as a `C^∞` Riemannian metric. -/
example (n : ℕ) :
    IsContMDiffRiemannianBundle (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (fun x : EuclideanSpace ℝ (Fin n) ↦ TangentSpace (𝓡 n) x) :=
  inferInstance

/-- `ℝ³` is flat. -/
example (x : EuclideanSpace ℝ (Fin 3)) (u v w : TangentSpace (𝓡 3) x) :
    riemannCurvature (𝓡 3) x u v w = 0 :=
  riemannCurvature_vectorSpace x u v w

/-- `ℝⁿ` has sectional curvature `≤ 0` and `≥ 0`, Ricci curvature `≥ 0`, scalar curvature `≥ 0`. -/
example (n : ℕ) :
    SectionalCurvatureLE (𝓡 n) (EuclideanSpace ℝ (Fin n)) 0 ∧
      SectionalCurvatureGE (𝓡 n) (EuclideanSpace ℝ (Fin n)) 0 ∧
      RicciGE (𝓡 n) (EuclideanSpace ℝ (Fin n)) 0 ∧
      ScalarCurvatureGE (𝓡 n) (EuclideanSpace ℝ (Fin n)) 0 :=
  ⟨fun x u v _ ↦ (sectionalCurvature_vectorSpace x u v).le,
    fun x u v _ ↦ (sectionalCurvature_vectorSpace x u v).ge,
    fun x v ↦ by simp [ricci_vectorSpace],
    fun x ↦ (scalarCurvature_vectorSpace x).ge⟩

/-- The Ricci bound is not vacuous: `ℝ` does not have `Ric ≥ g`. -/
example : ¬ RicciGE 𝓘(ℝ, ℝ) ℝ 1 := by
  intro h
  let v : TangentSpace 𝓘(ℝ, ℝ) (0 : ℝ) := (1 : ℝ)
  have hv : v ≠ 0 := one_ne_zero (α := ℝ)
  have h1 := h 0 v
  rw [ricci_vectorSpace] at h1
  have := norm_pos_iff.mpr hv
  nlinarith

/-- The scalar curvature bound is not vacuous: `ℝ²` does not have scalar curvature `≥ 1`. -/
example : ¬ ScalarCurvatureGE (𝓡 2) (EuclideanSpace ℝ (Fin 2)) 1 := by
  intro h
  have h1 := h 0
  rw [scalarCurvature_vectorSpace] at h1
  norm_num at h1

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The sectional-curvature formula is `0` on dependent pairs, so the curvature bounds only
quantify over linearly independent pairs. -/
example (x : M) (u : TangentSpace I x) :
    sectionalCurvature I x u u = 0 ∧ sectionalCurvature I x u ((2 : ℝ) • u) = 0 :=
  ⟨sectionalCurvature_self I x u, sectionalCurvature_smul_right I x u 2⟩

/-- Antisymmetry of the Riemann curvature endomorphism. -/
example (x : M) (u v w : TangentSpace I x) :
    riemannCurvature I x u v w + riemannCurvature I x v u w = 0 := by
  rw [riemannCurvature_antisymm I x u v w, neg_add_cancel]

end General

/-- Statement shape: a closed Riemannian `n`-manifold with `Ric ≥ (n - 1) g` and positive scalar
curvature (the hypotheses elaborate). -/
example : Prop :=
  ∀ (n : ℕ) (M : Type) [EMetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [CompactSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)]
    [IsContMDiffRiemannianBundle (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (fun x : M ↦ TangentSpace (𝓡 n) x)]
    [IsRiemannianManifold (𝓡 n) M],
    RicciGE (𝓡 n) M ((n : ℝ) - 1) → (∀ x : M, 0 < scalarCurvature (𝓡 n) x) → True

end RiemannianCurvatureTests
