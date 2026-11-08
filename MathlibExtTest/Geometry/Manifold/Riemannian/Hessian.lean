/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.Manifold.Riemannian.Hessian

/-!
# Tests for the Riemannian Hessian API

Public use of `Manifold.hessian` and `Manifold.riemannianGradient`:
quadratic Hessian pins on `ℝ²` through the vector-space lemmas,
and the gradient characterization on an abstract manifold.
-/

open Bundle Manifold
open scoped Manifold ContDiff

noncomputable section

namespace HessianTests

/-- First coordinate functional on `ℝ²`, as Riesz representative of `e₀`. -/
private def hessL0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  (InnerProductSpace.toDual ℝ _) (EuclideanSpace.single 0 (1 : ℝ))

/-- Second coordinate functional on `ℝ²`, as Riesz representative of `e₁`. -/
private def hessL1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  (InnerProductSpace.toDual ℝ _) (EuclideanSpace.single 1 (1 : ℝ))

/-- Quadratic `q` with Hessian entries `(2, 3; 3, 0)`, via Riesz functionals. -/
private def hessQ : EuclideanSpace ℝ (Fin 2) → ℝ :=
  fun x => (hessL0 x) * (hessL0 x) + 3 * ((hessL0 x) * (hessL1 x))

/-- Linear part in `y` of `D y v₀`, for the second-derivative step. -/
private def hessG (v₀ : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  hessL0 v₀ • hessL0 + hessL0 v₀ • hessL0 +
    (3 : ℝ) • (hessL1 v₀ • hessL0 + hessL0 v₀ • hessL1)

/-- Value of the first functional on `e₀`. -/
private theorem hessL0_e0 :
    hessL0 (EuclideanSpace.single 0 (1 : ℝ)) = 1 := by
  unfold hessL0
  rw [InnerProductSpace.toDual_apply_apply, EuclideanSpace.inner_single_left]
  simp

/-- Value of the first functional on `e₁`. -/
private theorem hessL0_e1 :
    hessL0 (EuclideanSpace.single 1 (1 : ℝ)) = 0 := by
  unfold hessL0
  rw [InnerProductSpace.toDual_apply_apply, EuclideanSpace.inner_single_left]
  simp

/-- Value of the second functional on `e₀`. -/
private theorem hessL1_e0 :
    hessL1 (EuclideanSpace.single 0 (1 : ℝ)) = 0 := by
  unfold hessL1
  rw [InnerProductSpace.toDual_apply_apply, EuclideanSpace.inner_single_left]
  simp

/-- Value of the second functional on `e₁`. -/
private theorem hessL1_e1 :
    hessL1 (EuclideanSpace.single 1 (1 : ℝ)) = 1 := by
  unfold hessL1
  rw [InnerProductSpace.toDual_apply_apply, EuclideanSpace.inner_single_left]
  simp

/-- First-derivative formula for `hessQ`, from linearity and product rules. -/
private theorem hessQ_hasFDerivAt (y : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt hessQ
      (hessL0 y • hessL0 + hessL0 y • hessL0 +
        (3 : ℝ) • (hessL0 y • hessL1 + hessL1 y • hessL0)) y := by
  have h0 : HasFDerivAt ⇑hessL0 hessL0 y := hessL0.hasFDerivAt
  have h1 : HasFDerivAt ⇑hessL1 hessL1 y := hessL1.hasFDerivAt
  have h := (h0.mul h0).add ((h0.mul h1).const_mul (3 : ℝ))
  refine h.congr_of_eventuallyEq ?_
  apply Filter.Eventually.of_forall
  intro x
  unfold hessQ
  simp only [Pi.add_apply, Pi.mul_apply]

/-- Fréchet-derivative formula for `hessQ`. -/
private theorem hessQ_fderiv (y : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ hessQ y =
      (hessL0 y • hessL0 + hessL0 y • hessL0 +
        (3 : ℝ) • (hessL0 y • hessL1 + hessL1 y • hessL0)) :=
  (hessQ_hasFDerivAt y).fderiv

/-- General Hessian formula for `hessQ` at the origin, via `hessian_vectorSpace`. -/
private theorem hessQ_hessian
    (u v : TangentSpace (𝓡 2) (0 : EuclideanSpace ℝ (Fin 2))) :
    hessian (𝓡 2) hessQ (0 : EuclideanSpace ℝ (Fin 2)) u v =
      2 * hessL0 ((NormedSpace.fromTangentSpace
        (0 : EuclideanSpace ℝ (Fin 2))) u) *
        hessL0 ((NormedSpace.fromTangentSpace
        (0 : EuclideanSpace ℝ (Fin 2))) v) +
      3 * hessL0 ((NormedSpace.fromTangentSpace
        (0 : EuclideanSpace ℝ (Fin 2))) u) *
        hessL1 ((NormedSpace.fromTangentSpace
        (0 : EuclideanSpace ℝ (Fin 2))) v) +
      3 * hessL1 ((NormedSpace.fromTangentSpace
        (0 : EuclideanSpace ℝ (Fin 2))) u) *
        hessL0 ((NormedSpace.fromTangentSpace
        (0 : EuclideanSpace ℝ (Fin 2))) v) := by
  show hessian 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) hessQ
    (0 : EuclideanSpace ℝ (Fin 2)) u v = _
  rw [hessian_vectorSpace]
  set u₀ := (NormedSpace.fromTangentSpace
    (0 : EuclideanSpace ℝ (Fin 2))) u
  set v₀ := (NormedSpace.fromTangentSpace
    (0 : EuclideanSpace ℝ (Fin 2))) v
  have hg : (fun y => fderiv ℝ hessQ y v₀) = ⇑(hessG v₀) := by
    funext y
    rw [hessQ_fderiv y]
    simp only [hessG, add_apply, smul_apply, smul_eq_mul]
    ring
  rw [hg]
  have hHat : HasFDerivAt ⇑(hessG v₀) (hessG v₀)
      (0 : EuclideanSpace ℝ (Fin 2)) := (hessG v₀).hasFDerivAt
  have hGf : fderiv ℝ ⇑(hessG v₀) (0 : EuclideanSpace ℝ (Fin 2)) =
      hessG v₀ := hHat.fderiv
  rw [hGf]
  simp only [hessG, add_apply, smul_apply, smul_eq_mul]
  ring

/-- Hessian of `q` at the origin on `(e₀, e₀)` is `2`. -/
example :
    hessian (𝓡 2) hessQ (0 : EuclideanSpace ℝ (Fin 2))
      ((NormedSpace.fromTangentSpace
        (0 : EuclideanSpace ℝ (Fin 2))).symm
        (EuclideanSpace.single 0 (1 : ℝ)))
      ((NormedSpace.fromTangentSpace
        (0 : EuclideanSpace ℝ (Fin 2))).symm
        (EuclideanSpace.single 0 (1 : ℝ))) = 2 := by
  rw [hessQ_hessian]
  simp only [ContinuousLinearEquiv.apply_symm_apply, hessL0_e0, hessL1_e0]
  ring

/-- Hessian of `q` at the origin on `(e₀, e₁)` is `3`. -/
example :
    hessian (𝓡 2) hessQ (0 : EuclideanSpace ℝ (Fin 2))
      ((NormedSpace.fromTangentSpace
        (0 : EuclideanSpace ℝ (Fin 2))).symm
        (EuclideanSpace.single 0 (1 : ℝ)))
      ((NormedSpace.fromTangentSpace
        (0 : EuclideanSpace ℝ (Fin 2))).symm
        (EuclideanSpace.single 1 (1 : ℝ))) = 3 := by
  rw [hessQ_hessian]
  simp only [ContinuousLinearEquiv.apply_symm_apply, hessL0_e0, hessL0_e1,
    hessL1_e0, hessL1_e1]
  ring

/-- Hessian of `q` at the origin on `(e₁, e₁)` is `0`. -/
example :
    hessian (𝓡 2) hessQ (0 : EuclideanSpace ℝ (Fin 2))
      ((NormedSpace.fromTangentSpace
        (0 : EuclideanSpace ℝ (Fin 2))).symm
        (EuclideanSpace.single 1 (1 : ℝ)))
      ((NormedSpace.fromTangentSpace
        (0 : EuclideanSpace ℝ (Fin 2))).symm
        (EuclideanSpace.single 1 (1 : ℝ))) = 0 := by
  rw [hessQ_hessian]
  simp only [ContinuousLinearEquiv.apply_symm_apply, hessL0_e1, hessL1_e1]
  ring

/-- Wrong-coefficient pin: the `(e₀, e₀)` Hessian is not `1`. -/
example :
    hessian (𝓡 2) hessQ (0 : EuclideanSpace ℝ (Fin 2))
      ((NormedSpace.fromTangentSpace
        (0 : EuclideanSpace ℝ (Fin 2))).symm
        (EuclideanSpace.single 0 (1 : ℝ)))
      ((NormedSpace.fromTangentSpace
        (0 : EuclideanSpace ℝ (Fin 2))).symm
        (EuclideanSpace.single 0 (1 : ℝ))) ≠ 1 := by
  have h2 : hessian (𝓡 2) hessQ (0 : EuclideanSpace ℝ (Fin 2))
      ((NormedSpace.fromTangentSpace
        (0 : EuclideanSpace ℝ (Fin 2))).symm
        (EuclideanSpace.single 0 (1 : ℝ)))
      ((NormedSpace.fromTangentSpace
        (0 : EuclideanSpace ℝ (Fin 2))).symm
        (EuclideanSpace.single 0 (1 : ℝ))) = 2 := by
    rw [hessQ_hessian]
    simp only [ContinuousLinearEquiv.apply_symm_apply, hessL0_e0, hessL1_e0]
    ring
  rw [h2]
  norm_num

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- Pairing of the Riemannian gradient with `v` is the differential. -/
example (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    inner ℝ (riemannianGradient I f x) v = (mvfderiv I f x) v :=
  inner_riemannianGradient I f x v

/-- Characterization of the Riemannian gradient by its pairings. -/
example (f : M → ℝ) (x : M) (w : TangentSpace I x) :
    riemannianGradient I f x = w ↔
      ∀ v, inner ℝ w v = (mvfderiv I f x) v :=
  riemannianGradient_eq_iff I f x w

/-- Norm of the Riemannian gradient is the operator norm of the differential. -/
example (f : M → ℝ) (x : M) :
    ‖riemannianGradient I f x‖ = ‖mvfderiv I f x‖ :=
  norm_riemannianGradient I f x

end General

end HessianTests
