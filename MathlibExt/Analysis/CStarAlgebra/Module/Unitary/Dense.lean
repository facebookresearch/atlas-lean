/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Module.Unitary

import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Unitary equivalences from a common dense model

Two dense complex-linear maps out of one algebraic model determine a unitary
equivalence when they have the same coefficient-valued Gram form.  Mathlib's
dense isometric extension supplies the underlying linear isometry equivalence;
continuity of the Hilbert-module inner product upgrades the equality from the
dense model to the completed carriers.

No fullness, countability, unitality, or complementability hypothesis is used.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set

namespace CStarModule.UnitaryEquiv

noncomputable section

universe uB uX uE uF

variable {B : Type uB} {X : Type uX} {E : Type uE} {F : Type uF}
variable [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ]
  [StarOrderedRing Bᵐᵒᵖ]
variable [AddCommGroup X] [Module ℂ X]
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F]
  [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]

/-- Two dense linear realizations of one algebraic model with the same
coefficient-valued Gram form extend canonically to a unitary equivalence. -/
@[no_expose]
noncomputable def ofDenseLinearMaps
    (e : X →ₗ[ℂ] E) (f : X →ₗ[ℂ] F)
    (he : DenseRange e) (hf : DenseRange f)
    (hinner : ∀ x y,
      rightInner (B := B) (f x) (f y) =
        rightInner (B := B) (e x) (e y)) :
    CStarModule.UnitaryEquiv B E F := by
  let hnorm : ∀ x, ‖f x‖ = ‖e x‖ := fun x => by
    calc
      ‖f x‖ = √‖rightInner (B := B) (f x) (f x)‖ :=
        AdjointableOperator.norm_eq_sqrt_norm_rightInner (B := B) (f x)
      _ = √‖rightInner (B := B) (e x) (e x)‖ := by rw [hinner x x]
      _ = ‖e x‖ :=
        (AdjointableOperator.norm_eq_sqrt_norm_rightInner (B := B) (e x)).symm
  let U : E ≃ₗᵢ[ℂ] F :=
    LinearEquiv.extendOfIsometry (LinearEquiv.refl ℂ X) e f he hf hnorm
  apply ofLinearIsometryEquiv U
  intro x y
  have hEq :
      (fun p : E × E =>
        rightInner (B := B) (U p.1) (U p.2)) =
        fun p : E × E => rightInner (B := B) p.1 p.2 := by
    apply Continuous.ext_on (he.prodMap he)
    · exact (CStarModule.continuous_rightInner (B := B) (E := F)).comp
        (U.continuous.prodMap U.continuous)
    · exact CStarModule.continuous_rightInner (B := B) (E := E)
    · rintro _ ⟨⟨a, b⟩, rfl⟩
      have ha : U (e a) = f a := by
        simpa only [U, LinearEquiv.refl_apply] using
          LinearEquiv.extendOfIsometry_eq (LinearEquiv.refl ℂ X)
            e f he hf hnorm a
      have hb : U (e b) = f b := by
        simpa only [U, LinearEquiv.refl_apply] using
          LinearEquiv.extendOfIsometry_eq (LinearEquiv.refl ℂ X)
            e f he hf hnorm b
      simpa only [Prod.map_apply, ha, hb] using hinner a b
  exact congrFun hEq (x, y)

/-- The unitary extension agrees with the second realization on the common
dense model. -/
@[simp]
theorem ofDenseLinearMaps_apply
    (e : X →ₗ[ℂ] E) (f : X →ₗ[ℂ] F)
    (he : DenseRange e) (hf : DenseRange f)
    (hinner : ∀ x y,
      rightInner (B := B) (f x) (f y) =
        rightInner (B := B) (e x) (e y))
    (x : X) :
    ofDenseLinearMaps e f he hf hinner (e x) = f x := by
  unfold ofDenseLinearMaps
  simp only [ofLinearIsometryEquiv_apply]
  apply LinearEquiv.extendOfIsometry_eq

/-- The adjoint unitary extension sends the second realization back to the
first one. -/
@[simp]
theorem ofDenseLinearMaps_adjoint_apply
    (e : X →ₗ[ℂ] E) (f : X →ₗ[ℂ] F)
    (he : DenseRange e) (hf : DenseRange f)
    (hinner : ∀ x y,
      rightInner (B := B) (f x) (f y) =
        rightInner (B := B) (e x) (e y))
    (x : X) :
    (ofDenseLinearMaps e f he hf hinner).toAdjointable.adjoint (f x) =
      e x := by
  rw [← ofDenseLinearMaps_apply e f he hf hinner x,
    adjoint_apply_apply]

/-- A unitary equivalence with the prescribed action on the common dense
model is the canonical dense extension. -/
theorem ofDenseLinearMaps_unique
    (e : X →ₗ[ℂ] E) (f : X →ₗ[ℂ] F)
    (he : DenseRange e) (hf : DenseRange f)
    (hinner : ∀ x y,
      rightInner (B := B) (f x) (f y) =
        rightInner (B := B) (e x) (e y))
    (U : CStarModule.UnitaryEquiv B E F)
    (hU : ∀ x, U (e x) = f x) :
    U = ofDenseLinearMaps e f he hf hinner := by
  apply CStarModule.UnitaryEquiv.ext
  intro y
  have hEq :
      (fun z : E => U z) =
        fun z : E => ofDenseLinearMaps e f he hf hinner z := by
    apply Continuous.ext_on he
    · exact U.toAdjointable.toContinuousLinearMap.continuous
    · exact (ofDenseLinearMaps e f he hf hinner).toAdjointable.toContinuousLinearMap.continuous
    · rintro _ ⟨x, rfl⟩
      change U (e x) = ofDenseLinearMaps e f he hf hinner (e x)
      rw [hU x, ofDenseLinearMaps_apply]
  exact congrFun hEq y

end

end CStarModule.UnitaryEquiv
