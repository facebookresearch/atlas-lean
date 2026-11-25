/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.FunctorialCylinder

/-!
# Public clients for exact functorial cylinders

These clients use the native colimit and lifting APIs at independent
object, hom and small-colimit universes. A boundary-RLP map admits an
actual homotopy lift with both prescribed endpoints and its exact base map.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

universe w v u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.FunctorialCylinder

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
  (P : Precylinder (𝟭 C)) [P.IsExact.{w}]

/-- An actual chosen colimit is sent to a chosen colimit at the stated size. -/
noncomputable def mappedColimit {J : Type w} [Category.{w} J] (D : J ⥤ C)
    (c : Cocone D) (hc : IsColimit c) : IsColimit (P.I.mapCocone c) :=
  isColimitOfPreserves P.I hc

/-- Monomorphism preservation is available through the native cancellation API. -/
theorem map_detectsEquality {X Y Z : C} (i : X ⟶ Y) [Mono i]
    (f g : Z ⟶ P.I.obj X) (h : f ≫ P.I.map i = g ≫ P.I.map i) : f = g :=
  (cancel_mono (P.I.map i)).1 h

/-- Lifting the entire cylinder boundary retains both endpoint maps and the base. -/
theorem exists_lift_homotopy {X Z B : C} (p : Z ⟶ B)
    (hp : (MorphismProperty.monomorphisms C).rlp p)
    (f g : X ⟶ Z) (b : P.I.obj X ⟶ B)
    (hf : (P.app X).i₀ ≫ b = f ≫ p) (hg : (P.app X).i₁ ≫ b = g ≫ p) :
    ∃ H : P.I.obj X ⟶ Z,
      (P.app X).i₀ ≫ H = f ∧ (P.app X).i₁ ≫ H = g ∧ H ≫ p = b := by
  have : HasLiftingProperty (P.app X).i p :=
    hp _ (MorphismProperty.monomorphisms.infer_property _)
  let sq : CommSq (coprod.desc f g) (P.app X).i p b := ⟨by
    apply coprod.hom_ext
    · simpa only [coprod.inl_desc_assoc, Precylinder.inl_i_assoc] using hf.symm
    · simpa only [coprod.inr_desc_assoc, Precylinder.inr_i_assoc] using hg.symm⟩
  refine ⟨sq.lift, ?_, ?_, sq.fac_right⟩
  · have h := congrArg (fun k ↦ coprod.inl ≫ k) sq.fac_left
    simpa only [Precylinder.inl_i_assoc, coprod.inl_desc] using h
  · have h := congrArg (fun k ↦ coprod.inr ≫ k) sq.fac_left
    simpa only [Precylinder.inr_i_assoc, coprod.inr_desc] using h

end MathlibExtTest.AlgebraicTopology.ModelCategory.FunctorialCylinder
