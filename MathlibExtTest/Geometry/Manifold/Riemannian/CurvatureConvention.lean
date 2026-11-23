/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.Manifold.Riemannian.VectorSpace
import Mathlib.LinearAlgebra.Trace

/-!
# Sign convention of `CovariantDerivative.extendCurvature`

On the tangent bundle of a normed space `F`, the covariant derivative
`∇_X σ = Dσ(X) + Γ(X, σ)` with a constant bilinear map `Γ` (constant Christoffel symbols) has
curvature `R(u, v) w = Γ(u, Γ(v, w)) - Γ(v, Γ(u, w))`. This pins the convention
`R(X, Y) = [∇_X, ∇_Y] - ∇_[X, Y]` of `CovariantDerivative.extendCurvature` (do Carmo's
convention would give the negative), and shows that the definition is not trivially zero.
-/

open Bundle FiberBundle VectorField
open scoped Manifold

noncomputable section

namespace CurvatureConventionTests

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem differentiableAt_of_mdifferentiableAt_section {σ : Π y : F, TangentSpace 𝓘(ℝ, F) y}
    {y : F} (hσ : MDiffAt (T% σ) y) : DifferentiableAt ℝ (fun z ↦ (σ z : F)) y := by
  have := ((contMDiff_snd_tangentBundle_modelSpace F 𝓘(ℝ, F)).contMDiffAt.mdifferentiableAt
    one_ne_zero).comp y hσ
  exact mdifferentiableAt_iff_differentiableAt.mp this

/-- The flat covariant derivative of the tangent bundle of a normed space: `∇_X σ = Dσ(X)`. -/
def flatCov (σ : Π y : F, TangentSpace 𝓘(ℝ, F) y) (y : F) :
    TangentSpace 𝓘(ℝ, F) y →L[ℝ] TangentSpace 𝓘(ℝ, F) y :=
  (fderiv ℝ (fun z ↦ (σ z : F)) y : F →L[ℝ] F)

theorem flatCov_apply (σ : Π y : F, TangentSpace 𝓘(ℝ, F) y) (y : F)
    (X : TangentSpace 𝓘(ℝ, F) y) :
    flatCov σ y X = (fderiv ℝ (fun z ↦ (σ z : F)) y : F →L[ℝ] F) X := rfl

theorem isCovariantDerivativeOn_flatCov :
    IsCovariantDerivativeOn F (flatCov (F := F)) Set.univ where
  add {σ σ' y} hσ hσ' _ := by
    ext X
    have := fderiv_add (differentiableAt_of_mdifferentiableAt_section hσ)
      (differentiableAt_of_mdifferentiableAt_section hσ')
    exact congr($this X)
  leibniz {σ g y} hσ hg _ := by
    ext X
    have hg' := mdifferentiableAt_iff_differentiableAt.mp hg
    have := fderiv_smul hg' (differentiableAt_of_mdifferentiableAt_section hσ)
    have h2 := congr($this X)
    have hd : (d% g y : TangentSpace 𝓘(ℝ, F) y →L[ℝ] ℝ) = fderiv ℝ g y := by
      simp [mvfderiv, mfderiv_eq_fderiv]; rfl
    rw [hd]
    exact h2

theorem fderiv_section_eq_zero {τ : Π z : F, TangentSpace 𝓘(ℝ, F) z} {c : F}
    (h : ∀ z, τ z = c) (y : F) : fderiv ℝ (fun z ↦ (τ z : F)) y = 0 :=
  ((hasFDerivAt_const c y).congr_of_eventuallyEq (Filter.Eventually.of_forall h)).fderiv

/-- The covariant derivative `∇_X σ = Dσ(X) + Γ(X, σ)` on the tangent bundle of a normed space,
for a constant bilinear map `Γ` (constant Christoffel symbols). -/
def christoffelCov (Γ : F →L[ℝ] F →L[ℝ] F) :
    CovariantDerivative 𝓘(ℝ, F) F (TangentSpace 𝓘(ℝ, F) : F → Type _) :=
  CovariantDerivative.addOneForm ⟨flatCov, isCovariantDerivativeOn_flatCov⟩
    (fun _ ↦ (Γ.flip : F →L[ℝ] F →L[ℝ] F))

theorem christoffelCov_apply (Γ : F →L[ℝ] F →L[ℝ] F) (σ : Π y : F, TangentSpace 𝓘(ℝ, F) y)
    (y : F) (X : TangentSpace 𝓘(ℝ, F) y) :
    christoffelCov Γ σ y X = (fderiv ℝ (fun z ↦ (σ z : F)) y : F →L[ℝ] F) X + Γ X (σ y) := rfl

theorem christoffelCov_extend (Γ : F →L[ℝ] F →L[ℝ] F) {x : F} (w : TangentSpace 𝓘(ℝ, F) x)
    (y : F) (X : TangentSpace 𝓘(ℝ, F) y) :
    christoffelCov Γ (extend F w) y X = Γ X w := by
  rw [christoffelCov_apply, fderiv_section_eq_zero (extend_model_space x w), extend_model_space]
  exact zero_add _

/-- **Convention check**: for the connection `∇_X σ = Dσ(X) + Γ(X, σ)` with constant `Γ`,
`R(u, v) w = Γ(u, Γ(v, w)) - Γ(v, Γ(u, w))`, i.e. `R(X, Y) = [∇_X, ∇_Y] - ∇_[X, Y]`. -/
theorem curvature_christoffelCov (Γ : F →L[ℝ] F →L[ℝ] F) (x : F)
    (u v w : TangentSpace 𝓘(ℝ, F) x) :
    (christoffelCov Γ).extendCurvature x u v w = Γ u (Γ v w) - Γ v (Γ u w) := by
  have hin (a : TangentSpace 𝓘(ℝ, F) x) (z : F) :
      christoffelCov Γ (extend F w) z (extend F a z) = Γ a w := by
    rw [christoffelCov_extend, extend_model_space]
  simp only [CovariantDerivative.extendCurvature, mlieBracket_extend_model_space, map_zero,
    sub_zero]
  have h1 := christoffelCov_apply Γ (fun z ↦ christoffelCov Γ (extend F w) z (extend F v z)) x u
  have h2 := christoffelCov_apply Γ (fun z ↦ christoffelCov Γ (extend F w) z (extend F u z)) x v
  rw [fderiv_section_eq_zero (hin v), hin v x] at h1
  rw [fderiv_section_eq_zero (hin u), hin u x] at h2
  rw [h1, h2]
  have z1 : (0 : F →L[ℝ] F) u = 0 := rfl
  erw [z1]
  simp only [zero_add]
  rfl

/-- Constant Christoffel symbols on `ℝ × ℝ` with non-commuting `Γ(e₁) = A`, `Γ(e₂) = B`, where
`A (a, b) = (b, 0)` and `B (a, b) = (0, a)`. -/
def nonflatΓ : ℝ × ℝ →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
      ((ContinuousLinearMap.inl ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
      ((ContinuousLinearMap.inr ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ ℝ ℝ))

/-- **Non-vanishing check**: `extendCurvature` is not identically zero. For the connection with the
Christoffel symbols `nonflatΓ`, `R(e₁, e₂) e₁ = [A, B] e₁ = e₁`. -/
theorem extendCurvature_nonflat :
    (christoffelCov nonflatΓ).extendCurvature (0 : ℝ × ℝ) ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ))
      ((1 : ℝ), (0 : ℝ)) = ((1 : ℝ), (0 : ℝ)) :=
  (curvature_christoffelCov nonflatΓ (0 : ℝ × ℝ) ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ))
    ((1 : ℝ), (0 : ℝ))).trans (by simp [nonflatΓ]; rfl)

example : (christoffelCov nonflatΓ).extendCurvature (0 : ℝ × ℝ) ((1 : ℝ), (0 : ℝ))
    ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ)) ≠ 0 := fun h ↦ by
  have h1 : ((1 : ℝ), (0 : ℝ)).1 = (0 : ℝ × ℝ).1 :=
    congrArg Prod.fst (extendCurvature_nonflat.symm.trans h)
  simp at h1

/-- **Non-vanishing Ricci contraction**: for the connection with the Christoffel symbols
`nonflatΓ`, `z ↦ R(z, e₁) e₂` is `(a, b) ↦ (0, b)`, so `Ric(e₁, e₂) = 1`; the trace is taken in the
basis `Module.finBasis` chosen by `extendRicci`. -/
theorem extendRicci_nonflat :
    (christoffelCov nonflatΓ).extendRicci (0 : ℝ × ℝ) ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)) =
      1 := by
  let V := TangentSpace 𝓘(ℝ, ℝ × ℝ) (0 : ℝ × ℝ)
  -- `A z = R(z, e₁) e₂ = Γ(z, Γ(e₁, e₂)) - Γ(e₁, Γ(z, e₂))`
  let A : (ℝ × ℝ) →L[ℝ] ℝ × ℝ :=
    nonflatΓ.flip (nonflatΓ ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ))) -
      (nonflatΓ ((1 : ℝ), (0 : ℝ))).comp (nonflatΓ.flip ((0 : ℝ), (1 : ℝ)))
  have hA (z : ℝ × ℝ) : A z = ((0 : ℝ), z.2) := by simp [A, nonflatΓ]
  let L : V →ₗ[ℝ] V := A.toLinearMap
  have hL (z : V) : (christoffelCov nonflatΓ).extendCurvature (0 : ℝ × ℝ) z
      ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)) = L z :=
    (curvature_christoffelCov nonflatΓ (0 : ℝ × ℝ) z ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ))).trans
      rfl
  have htr : (christoffelCov nonflatΓ).extendRicci (0 : ℝ × ℝ) ((1 : ℝ), (0 : ℝ))
      ((0 : ℝ), (1 : ℝ)) = LinearMap.trace ℝ V L := by
    rw [LinearMap.trace_eq_matrix_trace ℝ (Module.finBasis ℝ V), Matrix.trace]
    simp only [CovariantDerivative.extendRicci, Matrix.diag, LinearMap.toMatrix_apply,
      Module.Basis.coord_apply]
    exact Finset.sum_congr rfl fun i _ ↦ congrArg (fun y ↦ (Module.finBasis ℝ V).repr y i) (hL _)
  let b : Module.Basis (Fin 2) ℝ V := Module.Basis.finTwoProd ℝ
  have h0 : L (b 0) = b 0 - b 0 := by
    change A (Module.Basis.finTwoProd ℝ 0) = _
    simp [hA, b]
    rfl
  have h1 : L (b 1) = b 1 := by
    change A (Module.Basis.finTwoProd ℝ 1) = _
    simp [hA, b]
    exact (Module.Basis.finTwoProd_one ℝ).symm
  rw [htr, LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace, Fin.sum_univ_two]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, h0, h1, sub_self, map_zero,
    Module.Basis.repr_self]
  simp

end CurvatureConventionTests
