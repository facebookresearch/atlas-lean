/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.Adjunction.TripleComposition

/-! # Public three-stage Hom, unit, and counit callers -/

set_option autoImplicit false
noncomputable section
universe uA vA uB vB uC vC uD vD
open CategoryTheory

namespace MathlibExtTest.TripleAdjunction

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}
  {L₃ : C ⥤ D} {R₃ : D ⥤ C}
  (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)

/-- Build both functions of the Hom equivalence from the three given stages. -/
def stagedHomEquiv (X : A) (Y : D) :
    ((L₁ ⋙ L₂ ⋙ L₃).obj X ⟶ Y) ≃ (X ⟶ (R₃ ⋙ R₂ ⋙ R₁).obj Y) :=
  (a₃.homEquiv (L₂.obj (L₁.obj X)) Y).trans
    ((a₂.homEquiv (L₁.obj X) (R₃.obj Y)).trans (a₁.homEquiv X (R₂.obj (R₃.obj Y))))

/-- The entire staged correspondence is the actual chosen composite Hom equivalence. -/
theorem stagedHomEquiv_eq (X : A) (Y : D) :
    stagedHomEquiv a₁ a₂ a₃ X Y = ((a₁.comp a₂).comp a₃).homEquiv X Y := by
  apply Equiv.ext
  intro f
  exact (Adjunction.TripleComposition.forward a₁ a₂ a₃ X Y f).symm

example (X : A) (Y : D) (g : X ⟶ (R₃ ⋙ R₂ ⋙ R₁).obj Y) :
    (((a₁.comp a₂).comp a₃).homEquiv X Y).symm g =
      (a₃.homEquiv (L₂.obj (L₁.obj X)) Y).symm
        ((a₂.homEquiv (L₁.obj X) (R₃.obj Y)).symm
          ((a₁.homEquiv X (R₂.obj (R₃.obj Y))).symm g)) :=
  Adjunction.TripleComposition.inverse a₁ a₂ a₃ X Y g

/-- All given unit and counit maps remain in the complete three-stage formulas. -/
theorem unit_counit_formulas (X : A) (Y : D) :
    ((a₁.comp a₂).comp a₃).unit.app X =
      a₁.unit.app X ≫ R₁.map (a₂.unit.app (L₁.obj X)) ≫
        R₁.map (R₂.map (a₃.unit.app (L₂.obj (L₁.obj X)))) ∧
    ((a₁.comp a₂).comp a₃).counit.app Y =
      L₃.map (L₂.map (a₁.counit.app (R₂.obj (R₃.obj Y)))) ≫
        L₃.map (a₂.counit.app (R₃.obj Y)) ≫ a₃.counit.app Y :=
  ⟨Adjunction.TripleComposition.unit a₁ a₂ a₃ X, Adjunction.TripleComposition.counit a₁ a₂ a₃ Y⟩

/-- Both complete source and target triangle identities hold for the actual composite. -/
theorem triangles (X : A) (Y : D) :
    (L₁ ⋙ L₂ ⋙ L₃).map (((a₁.comp a₂).comp a₃).unit.app X) ≫
      ((a₁.comp a₂).comp a₃).counit.app ((L₁ ⋙ L₂ ⋙ L₃).obj X) = 𝟙 _ ∧
    ((a₁.comp a₂).comp a₃).unit.app ((R₃ ⋙ R₂ ⋙ R₁).obj Y) ≫
      (R₃ ⋙ R₂ ⋙ R₁).map (((a₁.comp a₂).comp a₃).counit.app Y) = 𝟙 _ :=
  ⟨((a₁.comp a₂).comp a₃).left_triangle_components X,
    ((a₁.comp a₂).comp a₃).right_triangle_components Y⟩

example (X Y : A) (f : X ⟶ Y) :
    (((Adjunction.id (C := A)).comp (Adjunction.id (C := A))).comp
      (Adjunction.id (C := A))).homEquiv X Y f = f := by
  have h : ∀ g : X ⟶ Y, (Adjunction.id (C := A)).homEquiv X Y g = g :=
    fun g => ((Adjunction.id (C := A)).homEquiv_unit X Y g).trans (Category.id_comp g)
  exact (Adjunction.TripleComposition.forward (Adjunction.id (C := A))
    (Adjunction.id (C := A)) (Adjunction.id (C := A)) X Y f).trans
      ((h _).trans ((h _).trans (h f)))

#print axioms stagedHomEquiv
#print axioms stagedHomEquiv_eq
#print axioms unit_counit_formulas
#print axioms triangles
#print axioms CategoryTheory.Adjunction.TripleComposition.forward
#print axioms CategoryTheory.Adjunction.TripleComposition.inverse
#print axioms CategoryTheory.Adjunction.TripleComposition.unit
#print axioms CategoryTheory.Adjunction.TripleComposition.counit

end MathlibExtTest.TripleAdjunction
