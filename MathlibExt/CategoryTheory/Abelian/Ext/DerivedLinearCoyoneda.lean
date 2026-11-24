/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.Ext.DerivedCoyoneda
public import MathlibExt.CategoryTheory.Abelian.RightDerived.Linear
public import MathlibExt.CategoryTheory.Abelian.RightDerived.ResolutionComparison
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import MathlibExt.CategoryTheory.Linear.Yoneda.Limits
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits

/-!
# Right-derived linear Coyoneda and linear Ext

Deriving the linear Hom functor in its second argument gives linear Ext. Exact forgetting
compares the underlying additive groups with the preadditive Coyoneda comparison. Scalar
naturality and the Ext scalar formula establish linearity.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra

universe t u v

namespace CategoryTheory.Abelian

variable (R : Type t) [CommRing R]
  {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]

variable [HasInjectiveResolutions C] [HasExt.{v} C]

/-- Exact forgetting reaches the existing additive Coyoneda/Ext comparison. -/
def rightDerivedLinearCoyonedaForgetIso (X : C) (n : ℕ) :
    (((linearCoyoneda R C).obj (Opposite.op X)).rightDerived n) ⋙
        forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v} ≅
      extFunctorObj X n :=
  ((linearCoyoneda R C).obj (Opposite.op X)).rightDerivedCompIsoOfPreservesHomology
      (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}) n ≪≫
    rightDerivedCoyonedaIsoExtFunctorObj X n

/-- The comparison is R-linear, by naturality at r times the identity. -/
def rightDerivedLinearCoyonedaObjEquiv (X Y : C) (n : ℕ) :
    (((linearCoyoneda R C).obj (Opposite.op X)).rightDerived n).obj Y ≃ₗ[R]
      Ext X Y n := by
  let F := (linearCoyoneda R C).obj (Opposite.op X)
  let e := rightDerivedLinearCoyonedaForgetIso R X n
  let ea := (e.app Y).addCommGroupIsoToAddEquiv
  refine { ea with map_smul' := ?_ }
  intro r z
  have h := ConcreteCategory.congr_hom (e.hom.naturality (r • 𝟙 Y)) z
  have hr : ((F.rightDerived n).map (r • 𝟙 Y)).hom z = r • z := by
    rw [Functor.map_smul, Functor.map_id]
    rfl
  change ea (((F.rightDerived n).map (r • 𝟙 Y)).hom z) =
      (ea z).comp (Ext.mk₀ (r • 𝟙 Y)) (add_zero n) at h
  rw [hr] at h
  exact h.trans (Ext.smul_eq_comp_mk₀ (ea z) r).symm

/-- The linear comparison has exactly the original additive comparison's value. -/
@[simp]
theorem rightDerivedLinearCoyonedaObjEquiv_apply (X Y : C) (n : ℕ)
    (z : (((linearCoyoneda R C).obj (Opposite.op X)).rightDerived n).obj Y) :
    rightDerivedLinearCoyonedaObjEquiv R X Y n z =
      ((rightDerivedLinearCoyonedaForgetIso R X n).hom.app Y).hom z := rfl

/-- The comparison intertwines derived coefficient maps with Ext postcomposition. -/
theorem rightDerivedLinearCoyonedaObjEquiv_naturality
    (X : C) {Y Y' : C} (f : Y ⟶ Y') (n : ℕ)
    (z : (((linearCoyoneda R C).obj (Opposite.op X)).rightDerived n).obj Y) :
    rightDerivedLinearCoyonedaObjEquiv R X Y' n
        (((((linearCoyoneda R C).obj (Opposite.op X)).rightDerived n).map f).hom z) =
      (rightDerivedLinearCoyonedaObjEquiv R X Y n z).comp (Ext.mk₀ f) (add_zero n) := by
  let F := (linearCoyoneda R C).obj (Opposite.op X)
  let e := rightDerivedLinearCoyonedaForgetIso R X n
  let ea := (e.app Y).addCommGroupIsoToAddEquiv
  let ea' := (e.app Y').addCommGroupIsoToAddEquiv
  have h := ConcreteCategory.congr_hom (e.hom.naturality f) z
  change ea' (((F.rightDerived n).map f).hom z) =
      (ea z).comp (Ext.mk₀ f) (add_zero n) at h
  change ea' (((F.rightDerived n).map f).hom z) =
      (ea z).comp (Ext.mk₀ f) (add_zero n)
  exact h

/-- The linear Hom derived functor is naturally linear Ext. -/
def rightDerivedLinearCoyonedaIsoExtFunctorObj (X : C) (n : ℕ) :
    ((linearCoyoneda R C).obj (Opposite.op X)).rightDerived n ≅
      linearExtFunctorObj R X n := by
  let F : C ⥤ ModuleCat.{v} R :=
    ((linearCoyoneda R C).obj (Opposite.op X)).rightDerived n
  let G : C ⥤ ModuleCat.{v} R := linearExtFunctorObj R X n
  let eApp (Y : C) : F.obj Y ≅ G.obj Y :=
    (rightDerivedLinearCoyonedaObjEquiv R X Y n).toModuleIso
  have he : ∀ {Y Y' : C} (f : Y ⟶ Y'),
      F.map f ≫ (eApp Y').hom = (eApp Y).hom ≫ G.map f := by
    intro Y Y' f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change rightDerivedLinearCoyonedaObjEquiv R X Y' n ((F.map f).hom z) =
      (rightDerivedLinearCoyonedaObjEquiv R X Y n z).comp (Ext.mk₀ f) (add_zero n)
    exact rightDerivedLinearCoyonedaObjEquiv_naturality R X f n z
  exact NatIso.ofComponents (F := F) (G := G) eApp he

end CategoryTheory.Abelian
