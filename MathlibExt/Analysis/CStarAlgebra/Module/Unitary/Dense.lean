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
# Unitary equivalences from dense linear maps

Let `E,F` be complete right C-star modules over a nonunital algebra `B` with star-compatible
coefficient order. Suppose complex-linear maps `e : X → E` and `f : X → F` have dense ranges and
satisfy `⟨f x, f y⟩_B = ⟨e x, e y⟩_B` for every `x,y` in the complex module `X`. There is a
unique unitary `U : E ≃ F` with `U (e x) = f x`. Its adjoint sends `f x` back to `e x`. Only an
additive group and a complex-module structure are imposed on `X`.
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

/-- **Unitary determined by dense linear realizations.** For complete right C-star modules, dense
complex-linear maps `e : X → E`, `f : X → F` with `⟨f x,f y⟩_B = ⟨e x,e y⟩_B` determine a
unitary `U` satisfying `U (e x) = f x`. -/
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

/-- **Unitary extension on the dense image.** For dense linear maps with equal coefficient Gram
forms, `ofDenseLinearMaps e f he hf hinner (e x) = f x`. -/
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

/-- **Adjoint on the second dense image.** For the unitary determined by dense maps `e,f` with
equal Gram forms, `U* (f x) = e x`. -/
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

/-- **Uniqueness of a dense unitary extension.** For dense linear maps `e,f` with equal Gram
forms, every unitary satisfying `U (e x) = f x` for all `x` equals `ofDenseLinearMaps e f he
hf hinner`. -/
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
