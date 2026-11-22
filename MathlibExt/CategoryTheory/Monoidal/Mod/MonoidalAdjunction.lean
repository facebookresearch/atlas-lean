/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Mod.Functor
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# The original module lift of a monoidal adjunction

A genuine strong monoidal left adjoint transports modules by its actual
tensorator. The right adjoint transports modules by its actual lax maps and
restricts along the original monoid-adjunction unit. Both module Hom functions
are the original underlying adjunction functions, with linearity proved.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uC vC uD vD

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace CategoryTheory.Mod.MonoidalAdjunction

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
variable {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
variable {F : C ⥤ D} {R : D ⥤ C} [F.Monoidal] [R.LaxMonoidal]
variable (a : F ⊣ R) [a.IsMonoidal] (A : C) [MonObj A]

/-- The actual monoid map is the full unit of the original lifted monoid adjunction. -/
def unitMonoidHom : ({ X := A } : Mon C) ⟶
    (Functor.mapMon R).obj ((Functor.mapMon F).obj ({ X := A } : Mon C)) :=
  a.mapMon.unit.app ({ X := A } : Mon C)

/-- The whole monoid-adjunction unit has the original underlying unit component. -/
theorem unitMonoidHom_hom : (unitMonoidHom a A).hom = a.unit.app A := by
  change (𝟙 A) ≫ a.unit.app A ≫ 𝟙 (R.obj (F.obj A)) = a.unit.app A
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The full monoid-adjunction unit is an actual monoid homomorphism on its original carrier. -/
instance unitMonoidHom_isMonHom : IsMonHom (unitMonoidHom a A).hom :=
  (unitMonoidHom a A).isMonHom_hom

/-- The same full monoid unit on the explicitly typed original carrier. -/
def unitHom : A ⟶ R.obj (F.obj A) := (unitMonoidHom a A).hom

/-- The explicitly typed unit retains its actual monoid homomorphism property. -/
instance unitHom_isMonHom : IsMonHom (unitHom a A) := (unitMonoidHom a A).isMonHom_hom

/-- The explicitly typed unit is the original underlying adjunction unit. -/
theorem unitHom_original : unitHom a A = a.unit.app A := unitMonoidHom_hom a A

/-- The actual right module functor uses the original lax transport and unit monoid map. -/
def right : Mod D (F.obj A) ⥤ Mod C A := by
  exact Functor.mapMod R (F.obj A) ⋙ Mod.comap (unitHom a A)

/-- The complete right module carrier is the unchanged original right-adjoint image. -/
theorem right_obj (N : Mod D (F.obj A)) : ((right a A).obj N).X = R.obj N.X := rfl

/-- Every original right-module arrow is the original right-adjoint arrow. -/
theorem right_map {N N' : Mod D (F.obj A)} (f : N ⟶ N') :
    ((right a A).map f).hom = R.map f.hom := rfl

/-- The original right-module action retains the original unit and full lax tensorator. -/
theorem right_action (N : Mod D (F.obj A)) : ((right a A).obj N).mod.smul =
    (a.unit.app A ▷ R.obj N.X) ≫ Functor.LaxMonoidal.μ R (F.obj A) N.X ≫ R.map N.mod.smul := by
  change (unitHom a A ▷ R.obj N.X) ≫
    Functor.LaxMonoidal.μ R (F.obj A) N.X ≫ R.map N.mod.smul = _
  exact congrArg (fun f => (f ▷ R.obj N.X) ≫
    Functor.LaxMonoidal.μ R (F.obj A) N.X ≫ R.map N.mod.smul) (unitHom_original a A)

/-- The original left module action is the actual tensorator followed by the original action image. -/
theorem left_action (M : Mod C A) : ((Functor.mapMod F A).obj M).mod.smul =
    Functor.LaxMonoidal.μ F A M.X ≫ F.map M.mod.smul := rfl

/-- The tensor adjunct is computed from the complete original monoidal unit square. -/
theorem tensorHomEquiv (X : C) (N : Mod D (F.obj A)) (f : F.obj X ⟶ N.X) :
    a.homEquiv (A ⊗ X) N.X
      (Functor.OplaxMonoidal.δ F A X ≫ (F.obj A ◁ f) ≫ N.mod.smul) =
    (A ◁ a.homEquiv X N.X f) ≫ (a.unit.app A ▷ R.obj N.X) ≫
      Functor.LaxMonoidal.μ R (F.obj A) N.X ≫ R.map N.mod.smul := by
  let h : X ⟶ R.obj N.X := a.homEquiv X N.X f
  have hu : a.unit.app (A ⊗ X) ≫ R.map (Functor.OplaxMonoidal.δ F A X) =
      (a.unit.app A ⊗ₘ a.unit.app X) ≫ Functor.LaxMonoidal.μ R (F.obj A) (F.obj X) :=
    a.unit_app_tensor_comp_map_δ A X
  have hn : Functor.LaxMonoidal.μ R (F.obj A) (F.obj X) ≫ R.map (F.obj A ◁ f) =
      (R.obj (F.obj A) ◁ R.map f) ≫ Functor.LaxMonoidal.μ R (F.obj A) N.X :=
    (Functor.LaxMonoidal.μ_natural_right R (F.obj A) f).symm
  have ht : (a.unit.app A ⊗ₘ a.unit.app X) ≫ (R.obj (F.obj A) ◁ R.map f) =
      (A ◁ h) ≫ (a.unit.app A ▷ R.obj N.X) := by
    let uA : A ⟶ R.obj (F.obj A) := a.unit.app A
    let uX : X ⟶ R.obj (F.obj X) := a.unit.app X
    change (uA ⊗ₘ uX) ≫ (R.obj (F.obj A) ◁ R.map f) = (A ◁ h) ≫ (uA ▷ R.obj N.X)
    calc
      _ = (uA ⊗ₘ uX) ≫ (𝟙 (R.obj (F.obj A)) ⊗ₘ R.map f) :=
        congrArg (fun g => (uA ⊗ₘ uX) ≫ g) (id_tensorHom (R.obj (F.obj A)) (R.map f)).symm
      _ = (uA ≫ 𝟙 _) ⊗ₘ (uX ≫ R.map f) := tensorHom_comp_tensorHom _ _ _ _
      _ = uA ⊗ₘ (uX ≫ R.map f) :=
        congrArg (fun g => g ⊗ₘ (uX ≫ R.map f)) (Category.comp_id uA)
      _ = uA ⊗ₘ h :=
        congrArg (fun g => uA ⊗ₘ g) (a.homEquiv_unit X N.X f).symm
      _ = _ := tensorHom_def' _ _
  calc
    _ = a.unit.app (A ⊗ X) ≫ R.map (Functor.OplaxMonoidal.δ F A X) ≫
        R.map (F.obj A ◁ f) ≫ R.map N.mod.smul := by
      rw [a.homEquiv_unit, R.map_comp, R.map_comp]
    _ = (a.unit.app A ⊗ₘ a.unit.app X) ≫
        Functor.LaxMonoidal.μ R (F.obj A) (F.obj X) ≫ R.map (F.obj A ◁ f) ≫
          R.map N.mod.smul := by
      rw [← Category.assoc, ← Category.assoc, hu]
      simp only [Category.assoc]
    _ = (a.unit.app A ⊗ₘ a.unit.app X) ≫ (R.obj (F.obj A) ◁ R.map f) ≫
        Functor.LaxMonoidal.μ R (F.obj A) N.X ≫ R.map N.mod.smul := by
      rw [reassoc_of% hn]
    _ = (A ◁ h) ≫ (a.unit.app A ▷ R.obj N.X) ≫
        Functor.LaxMonoidal.μ R (F.obj A) N.X ≫ R.map N.mod.smul := by
      rw [← Category.assoc, ← Category.assoc, ht]
      simp only [Category.assoc]

/-- The forward module Hom function is the original underlying Hom function. -/
def toRight {M : Mod C A} {N : Mod D (F.obj A)}
    (f : (Functor.mapMod F A).obj M ⟶ N) : M ⟶ (right a A).obj N := by
  let f₀ : F.obj M.X ⟶ N.X := f.hom
  let h : M.X ⟶ R.obj N.X := a.homEquiv M.X N.X f₀
  refine Mod.Hom.mk' h ?_
  have hf₀ : ((Functor.mapMod F A).obj M).mod.smul ≫ f₀ =
      (F.obj A ◁ f₀) ≫ N.mod.smul := f.isModHom.smul_hom
  have hf : Functor.LaxMonoidal.μ F A M.X ≫ F.map M.mod.smul ≫ f₀ =
      (F.obj A ◁ f₀) ≫ N.mod.smul :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun g => g ≫ f₀) (left_action (F := F) A M)).symm.trans hf₀)
  have hf' : F.map M.mod.smul ≫ f₀ =
      Functor.OplaxMonoidal.δ F A M.X ≫ (F.obj A ◁ f₀) ≫ N.mod.smul := by
    have h₀ := congrArg (fun g => Functor.OplaxMonoidal.δ F A M.X ≫ g) hf
    rw [← Category.assoc, Functor.Monoidal.δ_μ, Category.id_comp] at h₀
    exact h₀
  have hlinear : M.mod.smul ≫ h = (A ◁ h) ≫ (a.unit.app A ▷ R.obj N.X) ≫
      Functor.LaxMonoidal.μ R (F.obj A) N.X ≫ R.map N.mod.smul :=
    ((a.homEquiv_naturality_left M.mod.smul f₀).symm.trans
      ((congrArg (a.homEquiv (A ⊗ M.X) N.X) hf').trans (tensorHomEquiv a A M.X N f₀)))
  exact hlinear.trans
    (congrArg (fun g => (A ◁ h) ≫ g) (right_action a A N).symm)

/-- The inverse module Hom function is the original underlying inverse Hom function. -/
def fromRight {M : Mod C A} {N : Mod D (F.obj A)} (h : M ⟶ (right a A).obj N) :
    (Functor.mapMod F A).obj M ⟶ N := by
  let h₀ : M.X ⟶ R.obj N.X := h.hom
  let f : F.obj M.X ⟶ N.X := (a.homEquiv M.X N.X).symm h₀
  have hlinear : Functor.LaxMonoidal.μ F A M.X ≫ F.map M.mod.smul ≫ f =
      (F.obj A ◁ f) ≫ N.mod.smul := by
    apply (cancel_epi (Functor.OplaxMonoidal.δ F A M.X)).1
    rw [← Category.assoc, ← Category.assoc, Functor.Monoidal.δ_μ, Category.id_comp]
    apply (a.homEquiv (A ⊗ M.X) N.X).injective
    have he : a.homEquiv M.X N.X f = h₀ := (a.homEquiv M.X N.X).apply_symm_apply h₀
    have hl : a.homEquiv (A ⊗ M.X) N.X (F.map M.mod.smul ≫ f) = M.mod.smul ≫ h₀ :=
      (a.homEquiv_naturality_left M.mod.smul f).trans (congrArg (fun g => M.mod.smul ≫ g) he)
    have hr : a.homEquiv (A ⊗ M.X) N.X
        (Functor.OplaxMonoidal.δ F A M.X ≫ (F.obj A ◁ f) ≫ N.mod.smul) =
        (A ◁ h₀) ≫ ((right a A).obj N).mod.smul :=
      (tensorHomEquiv a A M.X N f).trans
        ((congrArg (fun g => (A ◁ g) ≫ (a.unit.app A ▷ R.obj N.X) ≫
          Functor.LaxMonoidal.μ R (F.obj A) N.X ≫ R.map N.mod.smul) he).trans
            (congrArg (fun g => (A ◁ h₀) ≫ g) (right_action a A N).symm))
    exact hl.trans (h.isModHom.smul_hom.trans hr.symm)
  refine Mod.Hom.mk' f ?_
  exact (congrArg (fun g => g ≫ f) (left_action (F := F) A M)).trans
    ((Category.assoc _ _ _).trans hlinear)

/-- Both original underlying Hom functions are mutually inverse on full module morphisms. -/
def homEquiv (M : Mod C A) (N : Mod D (F.obj A)) :
    ((Functor.mapMod F A).obj M ⟶ N) ≃ (M ⟶ (right a A).obj N) where
  toFun := toRight a A
  invFun := fromRight a A
  left_inv f := by
    apply Mod.hom_ext
    exact (a.homEquiv M.X N.X).symm_apply_apply f.hom
  right_inv h := by
    apply Mod.hom_ext
    exact (a.homEquiv M.X N.X).apply_symm_apply h.hom

/-- Naturality in source module arrows retains the actual original mapMod arrows. -/
theorem homEquiv_naturality_left_symm {M M' : Mod C A} {N : Mod D (F.obj A)}
    (f : M ⟶ M') (h : M' ⟶ (right a A).obj N) :
    (homEquiv a A M N).symm (f ≫ h) =
      (Functor.mapMod F A).map f ≫ (homEquiv a A M' N).symm h := by
  apply Mod.hom_ext
  exact a.homEquiv_naturality_left_symm f.hom h.hom

/-- Naturality in target module arrows retains the original right-adjoint arrow. -/
theorem homEquiv_naturality_right {M : Mod C A} {N N' : Mod D (F.obj A)}
    (f : (Functor.mapMod F A).obj M ⟶ N) (g : N ⟶ N') :
    homEquiv a A M N' (f ≫ g) = homEquiv a A M N f ≫ (right a A).map g := by
  apply Mod.hom_ext
  exact a.homEquiv_naturality_right f.hom g.hom

/-- The complete module adjunction has the actual transported left functor and original unit restriction. -/
def adjunction : Functor.mapMod F A ⊣ right a A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv a A
      homEquiv_naturality_left_symm := homEquiv_naturality_left_symm a A
      homEquiv_naturality_right := homEquiv_naturality_right a A }

end CategoryTheory.Mod.MonoidalAdjunction
