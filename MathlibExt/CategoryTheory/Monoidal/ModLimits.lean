/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Limits of module objects

The forgetful functor from module objects over a monoid object to the
category acted on creates limits: the limit of the underlying objects carries
the action induced by the actions on the members of the diagram, and the limit
projections are module maps. No preservation of limits by the action is needed,
as for algebras over a monad.
-/

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.ModLimits

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open MonObj
open scoped MonoidalLeftAction

universe w w' v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalLeftAction C D]
  {A : C} [MonObj A]
  {J : Type w} [Category.{w'} J]

section Construction

variable (F : J ⥤ Mod D A)

/-- The action of the member `j` of the diagram, on its underlying object. -/
def smulAt (j : J) :
    A ⊙ₗ (F ⋙ Mod.forget (D := D) A).obj j ⟶ (F ⋙ Mod.forget (D := D) A).obj j :=
  γ[A, (F.obj j).X]

theorem smulAt_map {j j' : J} (φ : j ⟶ j') :
    smulAt F j ≫ (F ⋙ Mod.forget (D := D) A).map φ =
      A ⊴ₗ (F ⋙ Mod.forget (D := D) A).map φ ≫ smulAt F j' :=
  IsModHom.smul_hom (A := A) (f := (F.map φ).hom)

theorem one_smulAt (j : J) :
    η[A] ⊵ₗ (F ⋙ Mod.forget (D := D) A).obj j ≫ smulAt F j =
      (λₗ ((F ⋙ Mod.forget (D := D) A).obj j)).hom :=
  ModObj.one_smul (M := A) (F.obj j).X

theorem mul_smulAt (j : J) :
    μ[A] ⊵ₗ (F ⋙ Mod.forget (D := D) A).obj j ≫ smulAt F j =
      (αₗ A A ((F ⋙ Mod.forget (D := D) A).obj j)).hom ≫ A ⊴ₗ smulAt F j ≫ smulAt F j :=
  ModObj.mul_smul (M := A) (F.obj j).X

variable [HasLimit (F ⋙ Mod.forget (D := D) A)]

/-- The action on the limit of the underlying objects, induced by the actions on the
members of the diagram. -/
def limitSMul : A ⊙ₗ limit (F ⋙ Mod.forget (D := D) A) ⟶ limit (F ⋙ Mod.forget (D := D) A) :=
  limit.lift (F ⋙ Mod.forget (D := D) A)
    { pt := A ⊙ₗ limit (F ⋙ Mod.forget (D := D) A)
      π :=
        { app := fun j ↦ A ⊴ₗ limit.π (F ⋙ Mod.forget (D := D) A) j ≫ smulAt F j
          naturality := fun j j' φ ↦ by
            dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
            rw [Category.id_comp, Category.assoc, smulAt_map,
              ← MonoidalLeftAction.actionHomRight_comp_assoc, limit.w] } }

@[reassoc (attr := simp)]
theorem limitSMul_π (j : J) :
    limitSMul F ≫ limit.π (F ⋙ Mod.forget (D := D) A) j =
      A ⊴ₗ limit.π (F ⋙ Mod.forget (D := D) A) j ≫ smulAt F j :=
  limit.lift_π _ _

instance limitModObj : ModObj A (limit (F ⋙ Mod.forget (D := D) A)) where
  smul := limitSMul F
  one_smul := by
    apply limit.hom_ext
    intro j
    rw [Category.assoc, limitSMul_π, ← MonoidalLeftAction.action_exchange_assoc, one_smulAt,
      MonoidalLeftAction.actionUnitIso_hom_naturality]
  mul_smul := by
    apply limit.hom_ext
    intro j
    rw [Category.assoc, limitSMul_π, ← MonoidalLeftAction.action_exchange_assoc, mul_smulAt,
      MonoidalLeftAction.tensor_actionHomRight_assoc, Iso.inv_hom_id_assoc,
      Category.assoc, Category.assoc, limitSMul_π,
      ← MonoidalLeftAction.actionHomRight_comp_assoc A (limitSMul F), limitSMul_π,
      MonoidalLeftAction.actionHomRight_comp_assoc]

/-- The limit cone of module objects over the limit of the underlying objects. -/
def limitCone : Cone F where
  pt := ⟨limit (F ⋙ Mod.forget (D := D) A)⟩
  π :=
    { app := fun j ↦
        { hom := limit.π (F ⋙ Mod.forget (D := D) A) j
          isModHom := ⟨limitSMul_π F j⟩ }
      naturality := fun j j' φ ↦ by
        apply Mod.Hom.ext
        change 𝟙 _ ≫ limit.π (F ⋙ Mod.forget (D := D) A) j' =
          limit.π (F ⋙ Mod.forget (D := D) A) j ≫ (F ⋙ Mod.forget (D := D) A).map φ
        rw [Category.id_comp, limit.w] }

/-- The underlying map of the lift of a cone of module objects. -/
def liftHom (s : Cone F) : s.pt.X ⟶ limit (F ⋙ Mod.forget (D := D) A) :=
  limit.lift (F ⋙ Mod.forget (D := D) A) ((Mod.forget (D := D) A).mapCone s)

theorem liftHom_π (s : Cone F) (j : J) :
    liftHom F s ≫ limit.π (F ⋙ Mod.forget (D := D) A) j = (s.π.app j).hom :=
  limit.lift_π ((Mod.forget (D := D) A).mapCone s) j

theorem liftHom_isModHom (s : Cone F) :
    γ[A, s.pt.X] ≫ liftHom F s = A ⊴ₗ liftHom F s ≫ limitSMul F := by
  apply limit.hom_ext
  intro j
  have h1 := liftHom_π F s j
  rw [Category.assoc, h1, Category.assoc, limitSMul_π,
    ← MonoidalLeftAction.actionHomRight_comp_assoc, h1]
  exact IsModHom.smul_hom (A := A) (f := (s.π.app j).hom)

/-- It is a limit cone. -/
def limitConeIsLimit : IsLimit (limitCone F) where
  lift s :=
    { hom := liftHom F s
      isModHom := ⟨liftHom_isModHom F s⟩ }
  fac s j := by
    apply Mod.Hom.ext
    exact liftHom_π F s j
  uniq s m w := by
    apply Mod.Hom.ext
    apply limit.hom_ext
    intro j
    change m.hom ≫ limit.π (F ⋙ Mod.forget (D := D) A) j =
      liftHom F s ≫ limit.π (F ⋙ Mod.forget (D := D) A) j
    rw [liftHom_π]
    exact congrArg Mod.Hom.hom (w j)

instance hasLimit : HasLimit F := ⟨⟨⟨limitCone F, limitConeIsLimit F⟩⟩⟩

end Construction

instance hasLimitsOfShape [HasLimitsOfShape J D] : HasLimitsOfShape J (Mod D A) where
  has_limit _ := inferInstance

instance hasLimitsOfSize [HasLimitsOfSize.{w', w} D] : HasLimitsOfSize.{w', w} (Mod D A) where
  has_limits_of_shape _ _ := inferInstance

end MathlibExt.CategoryTheory.ModLimits
