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

public import MathlibExt.Analysis.CStarAlgebra.Homotopy
public import MathlibExt.Analysis.CStarAlgebra.Unitization

/-!
# Unitization preserves point-norm homotopy

The canonical unitization of a point-norm homotopy fixes the scalar
coordinate at every time.
-/

@[expose] public section

open scoped CStarAlgebra

namespace NonUnitalStarAlgHom.Homotopic

universe u v

private def continuousMapEvalStarAlgHom
    {C : Type v} [CStarAlgebra C] (t : unitInterval) :
    C(unitInterval, C) →⋆ₐ[ℂ] C where
  toFun f := f t
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

@[simp]
private theorem continuousMapEvalStarAlgHom_apply
    {C : Type v} [CStarAlgebra C] (t : unitInterval)
    (f : C(unitInterval, C)) :
    continuousMapEvalStarAlgHom t f = f t :=
  rfl

/-- **Unitization preserves point-norm homotopy.** For nonunital complex C*-algebras `A,B` and
point-norm homotopic nonunital star homomorphisms `φ,ψ : A → B`, their unitized maps are point-norm
homotopic between the complex unitizations. The induced homotopy keeps the scalar coordinate fixed. -/
theorem unitization
    {A : Type u} {B : Type v}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    {phi psi : A →⋆ₙₐ[ℂ] B} (h : phi.Homotopic psi) :
    (Unitization.starMap phi).toNonUnitalStarAlgHom.Homotopic
      (Unitization.starMap psi).toNonUnitalStarAlgHom := by
  obtain ⟨F, h0, h1⟩ :=
    h.postcomp (Unitization.inrNonUnitalStarAlgHom ℂ B)
  let ev0 : C(unitInterval, Unitization ℂ B) →⋆ₐ[ℂ] Unitization ℂ B :=
    continuousMapEvalStarAlgHom 0
  let ev1 : C(unitInterval, Unitization ℂ B) →⋆ₐ[ℂ] Unitization ℂ B :=
    continuousMapEvalStarAlgHom 1
  have hLift (a : A) :
      Unitization.starLift F (Unitization.inr a) = F a := by
    have hs := Unitization.starLift_symm_apply_apply
      (Unitization.starLift F) a
    have hback : Unitization.starLift.symm (Unitization.starLift F) = F :=
      Equiv.symm_apply_apply Unitization.starLift F
    rw [hback] at hs
    exact hs.symm
  have heq0 : ev0.comp (Unitization.starLift F) = Unitization.starMap phi := by
    apply Unitization.starAlgHom_ext
    apply NonUnitalStarAlgHom.ext
    intro a
    calc
      ((ev0.comp (Unitization.starLift F)).toNonUnitalStarAlgHom.comp
          (Unitization.inrNonUnitalStarAlgHom ℂ A)) a =
          ev0 (Unitization.starLift F (Unitization.inr a)) := rfl
      _ = ev0 (F a) := by rw [hLift]
      _ = F a 0 := by simp [ev0]
      _ = Unitization.inr (phi a) := by simpa using h0 a
      _ = ((Unitization.starMap phi).toNonUnitalStarAlgHom.comp
          (Unitization.inrNonUnitalStarAlgHom ℂ A)) a := by simp
  have heq1 : ev1.comp (Unitization.starLift F) = Unitization.starMap psi := by
    apply Unitization.starAlgHom_ext
    apply NonUnitalStarAlgHom.ext
    intro a
    calc
      ((ev1.comp (Unitization.starLift F)).toNonUnitalStarAlgHom.comp
          (Unitization.inrNonUnitalStarAlgHom ℂ A)) a =
          ev1 (Unitization.starLift F (Unitization.inr a)) := rfl
      _ = ev1 (F a) := by rw [hLift]
      _ = F a 1 := by simp [ev1]
      _ = Unitization.inr (psi a) := by simpa using h1 a
      _ = ((Unitization.starMap psi).toNonUnitalStarAlgHom.comp
          (Unitization.inrNonUnitalStarAlgHom ℂ A)) a := by simp
  refine ⟨(Unitization.starLift F).toNonUnitalStarAlgHom, ?_, ?_⟩
  · intro x
    simpa [ev0] using DFunLike.congr_fun heq0 x
  · intro x
    simpa [ev1] using DFunLike.congr_fun heq1 x

end NonUnitalStarAlgHom.Homotopic
