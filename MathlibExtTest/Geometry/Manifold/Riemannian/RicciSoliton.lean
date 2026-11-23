/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.Manifold.Riemannian.RicciSoliton

/-!
# Tests for gradient Ricci solitons

Public use of `Manifold.IsGradientRicciSoliton` and
`Manifold.IsGradientShrinkingRicciSoliton`: the Gaussian shrinker on `ℝ⁴`,
instance inference for Euclidean space, vanishing scalar curvature and its
upper bound, an existential packaging of the shrinker, mutations in the
constant, the coefficient and the sign, and the projection to the soliton
equation and positivity on an abstract Riemannian manifold.
-/

open Bundle Manifold
open scoped Manifold ContDiff

namespace RicciSolitonTests

/-- The Gaussian shrinker on `ℝ⁴` with constant `1 / 2`. -/
example : IsGradientShrinkingRicciSoliton (𝓡 4)
    (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖ ^ 2 / 4) (1 / 2) := by
  have h_eq : (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖ ^ 2 / 4) =
      (fun x => ((1 / 2 : ℝ) / 2) * ‖x‖ ^ 2) := by
    funext x
    ring
  rw [h_eq]
  exact isGradientShrinkingRicciSoliton_gaussian (1 / 2 : ℝ) (by norm_num)

/-- `ℝ⁴` is complete. -/
example : CompleteSpace (EuclideanSpace ℝ (Fin 4)) :=
  inferInstance

/-- `ℝ⁴` is connected. -/
example : ConnectedSpace (EuclideanSpace ℝ (Fin 4)) :=
  inferInstance

/-- Euclidean space carries its standard Riemannian manifold structure. -/
example : IsRiemannianManifold (𝓡 4) (EuclideanSpace ℝ (Fin 4)) :=
  inferInstance

/-- `ℝ⁴` is positive-dimensional. -/
example : Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 4 := by
  simp

/-- The scalar curvature of `ℝ⁴` vanishes. -/
example (x : EuclideanSpace ℝ (Fin 4)) :
    scalarCurvature (𝓡 4) x = 0 :=
  scalarCurvature_vectorSpace x

/-- Hence the scalar curvature of `ℝ⁴` is bounded above. -/
example : ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin 4),
    scalarCurvature (𝓡 4) x ≤ C :=
  ⟨0, fun x => (scalarCurvature_vectorSpace x).le⟩

/-- Existential packaging of the Gaussian shrinker on `ℝ⁴`. -/
example : ∃ f : EuclideanSpace ℝ (Fin 4) → ℝ,
    IsGradientShrinkingRicciSoliton (𝓡 4) f (1 / 2) := by
  have h_eq : (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖ ^ 2 / 4) =
      (fun x => ((1 / 2 : ℝ) / 2) * ‖x‖ ^ 2) := by
    funext x
    ring
  refine ⟨fun x => ‖x‖ ^ 2 / 4, ?_⟩
  rw [h_eq]
  exact isGradientShrinkingRicciSoliton_gaussian (1 / 2 : ℝ) (by norm_num)

/-- Wrong constant: the shrinker potential is not a soliton with constant `1`. -/
example : ¬ IsGradientRicciSoliton (𝓡 4)
    (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖ ^ 2 / 4) 1 := by
  have h_eq : (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖ ^ 2 / 4) =
      (fun x => ((1 / 2 : ℝ) / 2) * ‖x‖ ^ 2) := by
    funext x
    ring
  rw [h_eq]
  intro h
  have h1 : (1 / 2 : ℝ) = 1 :=
    (isGradientRicciSoliton_gaussian_iff (1 / 2 : ℝ) 1).mp h
  norm_num at h1

/-- Wrong coefficient: `‖x‖ ^ 2 / 2` is not a soliton with constant `1 / 2`. -/
example : ¬ IsGradientRicciSoliton (𝓡 4)
    (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖ ^ 2 / 2) (1 / 2) := by
  have h_eq : (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖ ^ 2 / 2) =
      (fun x => ((1 : ℝ) / 2) * ‖x‖ ^ 2) := by
    funext x
    ring
  rw [h_eq]
  intro h
  have h1 : (1 : ℝ) = 1 / 2 :=
    (isGradientRicciSoliton_gaussian_iff 1 (1 / 2 : ℝ)).mp h
  norm_num at h1

/-- Sign flip: `-‖x‖ ^ 2 / 4` is not shrinking with constant `1 / 2`. -/
example : ¬ IsGradientShrinkingRicciSoliton (𝓡 4)
    (fun x : EuclideanSpace ℝ (Fin 4) => -‖x‖ ^ 2 / 4) (1 / 2) := by
  have h_eq : (fun x : EuclideanSpace ℝ (Fin 4) => -‖x‖ ^ 2 / 4) =
      (fun x => ((-1 / 2 : ℝ) / 2) * ‖x‖ ^ 2) := by
    funext x
    ring
  rw [h_eq]
  intro h
  have h1 := (isGradientShrinkingRicciSoliton_gaussian_iff
    (-1 / 2 : ℝ) (1 / 2 : ℝ)).mp h
  have heq : (-1 / 2 : ℝ) = 1 / 2 := h1.1
  norm_num at heq

/-- The expanding Gaussian is a soliton with constant `-1 / 2`. -/
example : IsGradientRicciSoliton (𝓡 4)
    (fun x : EuclideanSpace ℝ (Fin 4) => -‖x‖ ^ 2 / 4) (-1 / 2) := by
  have h_eq : (fun x : EuclideanSpace ℝ (Fin 4) => -‖x‖ ^ 2 / 4) =
      (fun x => ((-1 / 2 : ℝ) / 2) * ‖x‖ ^ 2) := by
    funext x
    ring
  rw [h_eq]
  exact isGradientRicciSoliton_gaussian (-1 / 2 : ℝ)

/-- The expanding Gaussian is not shrinking with constant `-1 / 2`. -/
example : ¬ IsGradientShrinkingRicciSoliton (𝓡 4)
    (fun x : EuclideanSpace ℝ (Fin 4) => -‖x‖ ^ 2 / 4) (-1 / 2) := by
  have h_eq : (fun x : EuclideanSpace ℝ (Fin 4) => -‖x‖ ^ 2 / 4) =
      (fun x => ((-1 / 2 : ℝ) / 2) * ‖x‖ ^ 2) := by
    funext x
    ring
  rw [h_eq]
  intro h
  have h2 : (0 : ℝ) < -1 / 2 :=
    (isGradientShrinkingRicciSoliton_gaussian_iff
      (-1 / 2 : ℝ) (-1 / 2 : ℝ)).mp h |>.2
  norm_num at h2

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- A shrinking soliton satisfies the soliton equation. -/
example (f : M → ℝ) (c : ℝ) (h : IsGradientShrinkingRicciSoliton I f c)
    (x : M) (u v : TangentSpace I x) :
    ricci I x u v + hessian I f x u v = c * inner ℝ u v :=
  h.toIsGradientRicciSoliton.ricci_add_hessian x u v

/-- A shrinking soliton has a positive constant. -/
example (f : M → ℝ) (c : ℝ) (h : IsGradientShrinkingRicciSoliton I f c) :
    0 < c :=
  h.pos

end General

end RicciSolitonTests
