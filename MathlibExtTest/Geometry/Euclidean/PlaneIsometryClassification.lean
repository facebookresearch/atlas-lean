/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Euclidean.PlaneIsometryClassification
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic

/-!
# Tests for the classification of plane isometries

The identity and every translation-by-a-vector isometry are translations.
Rotation by `180°` (the negation isometry) is a rotation, reflection across
the `x`-axis is a reflection, and reflection across the `x`-axis followed by
translation along the `x`-axis is a glide reflection. The classification
theorem puts each of these in its stated case.
-/

@[expose] public section

namespace MathlibExtTest.Geometry.Euclidean.PlaneIsometryClassification

-- `_root_` disambiguates from this file's own `...Euclidean.PlaneIsometryClassification`
-- namespace.
open _root_.Isometries

/-- The identity isometry is translation by `0`. -/
private theorem identity_isTranslation :
    IsTranslation (1 : Plane ≃ᵃⁱ[ℝ] Plane) :=
  ⟨0, fun x => by simp⟩

/-- Translation by `v` is a translation, witnessed by `v` itself. -/
private theorem constVAdd_isTranslation (v : Plane) :
    IsTranslation (AffineIsometryEquiv.constVAdd ℝ Plane v) :=
  ⟨v, fun x => by simp⟩

/-- Rotation by `180°`: negation, as an affine isometry of the plane. -/
private noncomputable def rot180 : Plane ≃ᵃⁱ[ℝ] Plane :=
  (LinearIsometryEquiv.neg ℝ (E := Plane)).toAffineIsometryEquiv

/-- Rotation by `180°` fixes `0`, has linear determinant `1`, and is not a
translation, so it is a rotation. -/
private theorem rot180_isRotation : IsRotation rot180 := by
  refine ⟨0, ?_, ?_, ?_⟩
  · simp [rot180]
  · have h : (rot180.linear.toLinearMap : Plane →ₗ[ℝ] Plane) = -LinearMap.id := rfl
    unfold linearDet; rw [h]
    rw [← neg_one_smul ℝ (LinearMap.id : Plane →ₗ[ℝ] Plane), LinearMap.det_smul]
    simp
  · intro ⟨v, hv⟩
    have h0 : rot180 0 = v +ᵥ (0 : Plane) := hv 0
    have h0v : v = 0 := by
      have h00 : rot180 0 = (0 : Plane) := by simp [rot180]
      rw [h00] at h0; simpa using h0.symm
    subst h0v
    have h1 : rot180 (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) =
        (0 : Plane) +ᵥ (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) := hv _
    have h1' : rot180 (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) =
        -(EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) := by simp [rot180]
    rw [h1'] at h1
    have h2 := congrArg (fun w : Plane => w (0 : Fin 2)) h1
    simp [EuclideanSpace.single] at h2
    norm_num at h2

/-- The `x`-axis, as a submodule of the plane. -/
private abbrev xAxis : Submodule ℝ Plane :=
  ℝ ∙ (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))

/-- The `x`-axis has finrank `1`, so its orthogonal complement also has
finrank `1`. -/
private theorem finrank_xAxis_orthogonal : Module.finrank ℝ xAxisᗮ = 1 := by
  have h := Submodule.finrank_add_finrank_orthogonal xAxis
  rw [show Module.finrank ℝ Plane = 2 from finrank_euclideanSpace_fin] at h
  have h2 : Module.finrank ℝ xAxis = 1 := by
    rw [xAxis, finrank_span_singleton]; simp [EuclideanSpace.single]
  omega

/-- Reflection across the `x`-axis, as an affine isometry of the plane. -/
private noncomputable def reflectX : Plane ≃ᵃⁱ[ℝ] Plane :=
  (xAxis.reflection).toAffineIsometryEquiv

/-- Reflection across the `x`-axis has linear determinant `-1`. -/
private theorem linearDet_reflectX : linearDet reflectX = -1 := by
  have h : (reflectX.linear.toLinearMap : Plane →ₗ[ℝ] Plane) =
      xAxis.reflection.toLinearMap := rfl
  unfold linearDet; rw [h, Submodule.det_reflection, finrank_xAxis_orthogonal]
  norm_num

/-- Reflection across the `x`-axis fixes the `x`-axis pointwise and has
linear determinant `-1`, so it is a reflection. -/
private theorem reflectX_isReflection : IsReflection reflectX := by
  refine ⟨AffineSubspace.mk' (0 : Plane) xAxis, ?_, ?_, linearDet_reflectX⟩
  · rw [AffineSubspace.direction_mk']
    rw [xAxis, finrank_span_singleton]; simp [EuclideanSpace.single]
  · intro x hx
    rw [AffineSubspace.mem_mk'] at hx
    have hxK : x ∈ xAxis := by simpa using hx
    have h : reflectX x = xAxis.reflection x := rfl
    rw [h, Submodule.reflection_mem_subspace_eq_self hxK]

/-- Glide reflection across the `x`-axis: reflect across the `x`-axis, then
translate by `(1, 0)` along it. -/
private noncomputable def glideX : Plane ≃ᵃⁱ[ℝ] Plane :=
  reflectX.trans
    (AffineIsometryEquiv.constVAdd ℝ Plane (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)))

/-- The glide reflection across the `x`-axis has linear determinant `-1`. -/
private theorem linearDet_glideX : linearDet glideX = -1 := by
  have h : (glideX.linear.toLinearMap : Plane →ₗ[ℝ] Plane) =
      xAxis.reflection.toLinearMap := by
    have hg : glideX.linear = reflectX.linear := rfl
    rw [hg]; rfl
  unfold linearDet; rw [h, Submodule.det_reflection, finrank_xAxis_orthogonal]
  norm_num

/-- The glide reflection across the `x`-axis acts on the `x`-axis as
translation by `(1, 0)`, so it is a glide reflection. -/
private theorem glideX_isGlideReflection : IsGlideReflection glideX := by
  refine ⟨linearDet_glideX, AffineSubspace.mk' (0 : Plane) xAxis, ?_,
    EuclideanSpace.single (0 : Fin 2) (1 : ℝ), ?_, ?_, ?_⟩
  · rw [AffineSubspace.direction_mk']
    rw [xAxis, finrank_span_singleton]; simp [EuclideanSpace.single]
  · rw [AffineSubspace.direction_mk']
    exact Submodule.mem_span_singleton_self _
  · intro h
    have h2 := congrArg (fun w : Plane => w (0 : Fin 2)) h
    simp [EuclideanSpace.single] at h2
  · intro x hx
    rw [AffineSubspace.mem_mk'] at hx
    have hxK : x ∈ xAxis := by simpa using hx
    show glideX x = EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +ᵥ x
    have h : glideX x =
        EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +ᵥ reflectX x := by
      simp [glideX]
    rw [h]
    have hr : reflectX x = x := by
      have hh : reflectX x = xAxis.reflection x := rfl
      rw [hh, Submodule.reflection_mem_subspace_eq_self hxK]
    rw [hr]

example : IsTranslation (1 : Plane ≃ᵃⁱ[ℝ] Plane) := identity_isTranslation

example (v : Plane) :
    IsTranslation (AffineIsometryEquiv.constVAdd ℝ Plane v) :=
  constVAdd_isTranslation v

example : IsRotation rot180 := rot180_isRotation

example : IsReflection reflectX := reflectX_isReflection

example : IsGlideReflection glideX := glideX_isGlideReflection

example : IsTranslation (1 : Plane ≃ᵃⁱ[ℝ] Plane) ∨ IsRotation (1 : Plane ≃ᵃⁱ[ℝ] Plane) ∨
    IsReflection (1 : Plane ≃ᵃⁱ[ℝ] Plane) ∨
    IsGlideReflection (1 : Plane ≃ᵃⁱ[ℝ] Plane) :=
  Or.inl identity_isTranslation

example (v : Plane) :
    IsTranslation (AffineIsometryEquiv.constVAdd ℝ Plane v) ∨
    IsRotation (AffineIsometryEquiv.constVAdd ℝ Plane v) ∨
    IsReflection (AffineIsometryEquiv.constVAdd ℝ Plane v) ∨
    IsGlideReflection (AffineIsometryEquiv.constVAdd ℝ Plane v) :=
  Or.inl (constVAdd_isTranslation v)

example : IsTranslation rot180 ∨ IsRotation rot180 ∨ IsReflection rot180 ∨
    IsGlideReflection rot180 :=
  Or.inr (Or.inl rot180_isRotation)

example : IsTranslation reflectX ∨ IsRotation reflectX ∨ IsReflection reflectX ∨
    IsGlideReflection reflectX :=
  Or.inr (Or.inr (Or.inl reflectX_isReflection))

example : IsTranslation glideX ∨ IsRotation glideX ∨ IsReflection glideX ∨
    IsGlideReflection glideX :=
  Or.inr (Or.inr (Or.inr glideX_isGlideReflection))

example (f : Plane ≃ᵃⁱ[ℝ] Plane) :
    IsTranslation f ∨ IsRotation f ∨ IsReflection f ∨ IsGlideReflection f :=
  plane_isometry_classification f

end MathlibExtTest.Geometry.Euclidean.PlaneIsometryClassification
