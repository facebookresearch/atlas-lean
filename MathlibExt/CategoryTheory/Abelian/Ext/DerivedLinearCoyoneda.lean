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
# Right-derived linear Hom and linear Ext

Let `R` be commutative and `C` an `R`-linear abelian category with
injective resolutions and Ext in its hom-set universe. Right derivation
of the module-valued functor `Hom_C(X,-)` gives native Ext with its
coefficient-endomorphism scalar action. The comparison is `R`-linear,
is natural in the second object, and has the same values as the
underlying additive Coyoneda comparison. The ring carrier and the
category object and hom-set universes are independent.
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

/-- Let `R` be a commutative ring and `C` an `R`-linear abelian
category with hom-set universe `v`, injective resolutions, and
Ext in universe `v`. For `X : C`, forgetting scalars from the degree-`n`
right-derived module-valued Hom functor gives a natural additive-group
isomorphism to `Y ↦ Ext^n(X,Y)`. -/
def rightDerivedLinearCoyonedaForgetIso (X : C) (n : ℕ) :
    (((linearCoyoneda R C).obj (Opposite.op X)).rightDerived n) ⋙
        forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v} ≅
      extFunctorObj X n :=
  ((linearCoyoneda R C).obj (Opposite.op X)).rightDerivedCompIsoOfPreservesHomology
      (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}) n ≪≫
    rightDerivedCoyonedaIsoExtFunctorObj X n

/- Linearity follows from naturality at scalar multiples of identity morphisms. -/

/-- Let `R` be a commutative ring and `C` an `R`-linear abelian
category with hom-set universe `v`, injective resolutions, and
Ext in universe `v`. For `X,Y : C`, there is a canonical `R`-linear equivalence
`R^nHom_C(X,-)(Y) ≃ₗ[R] Ext^n(X,Y)`. -/
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

/-- Let `R` be a commutative ring and `C` an `R`-linear abelian
category with hom-set universe `v`, injective resolutions, and
Ext in universe `v`. The linear derived-Hom-to-Ext equivalence at `X,Y,n` has the
same value on every element as its underlying additive-group
comparison. -/
@[simp]
theorem rightDerivedLinearCoyonedaObjEquiv_apply (X Y : C) (n : ℕ)
    (z : (((linearCoyoneda R C).obj (Opposite.op X)).rightDerived n).obj Y) :
    rightDerivedLinearCoyonedaObjEquiv R X Y n z =
      ((rightDerivedLinearCoyonedaForgetIso R X n).hom.app Y).hom z := rfl

/-- Let `R` be a commutative ring and `C` an `R`-linear abelian
category with hom-set universe `v`, injective resolutions, and
Ext in universe `v`. For `f : Y → Y′`, the linear equivalences at `X,Y` and
`X,Y′` intertwine the derived coefficient map with Ext postcomposition
by the degree-zero class of `f`. -/
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

/-- Let `R` be a commutative ring and `C` an `R`-linear abelian
category with hom-set universe `v`, injective resolutions, and
Ext in universe `v`. For fixed `X`, the linear equivalences form a natural
isomorphism of module-valued functors
`R^nHom_C(X,-) ≅ Ext^n(X,-)`. -/
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
