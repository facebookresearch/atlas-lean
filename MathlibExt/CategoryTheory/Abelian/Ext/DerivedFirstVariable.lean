/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.Ext.ProjectiveLinearComparison
public import MathlibExt.CategoryTheory.Abelian.Ext.DerivedLinearCoyoneda

/-!
# Derived linear Hom and the projective Ext construction

For a commutative ring `R` and an `R`-linear abelian category `C`
with enough projectives, injective resolutions and Ext in its hom-set
universe, right derivation of `Hom_C(X,-)` as an `R`-module-valued
functor is naturally isomorphic to the projective first-variable
Ext construction. The comparison factors through native linear Ext,
with the same cocycle representatives and coefficient maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

universe r v u

namespace CategoryTheory.Abelian

variable (R : Type r) [CommRing R]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
variable [EnoughProjectives C] [HasInjectiveResolutions C] [HasExt.{v} C]

/-- Let `R` be a commutative ring and `C` an `R`-linear abelian
category with enough projectives, hom-set universe `v`, and Ext
in universe `v`. Suppose `C` also has injective resolutions. For `X : C`, the module-valued functor obtained by right
 deriving `Hom_C(X,-)` in degree `n` is naturally isomorphic to the
projective first-variable Ext functor at `X`. -/
def rightDerivedLinearCoyonedaIsoFirstVariableExt (X : C) (n : ℕ) :
    ((linearCoyoneda R C).obj (op X)).rightDerived n ≅
      (_root_.Ext R C n).obj (op X) :=
  rightDerivedLinearCoyonedaIsoExtFunctorObj R X n ≪≫
    (firstVariableLinearExtIso R X n).symm

/-- Let `R` be a commutative ring and `C` an `R`-linear abelian
category with enough projectives, hom-set universe `v`, and Ext
in universe `v`. Suppose `C` also has injective resolutions. The forward comparison to projective first-variable Ext,
followed by its comparison to native linear Ext, equals the canonical
right-derived linear-Hom-to-Ext comparison at every `X,Y,n`. -/
@[reassoc]
theorem rightDerivedLinearCoyonedaIsoFirstVariableExt_hom_comp
    (X Y : C) (n : ℕ) :
    (rightDerivedLinearCoyonedaIsoFirstVariableExt R X n).hom.app Y ≫
        (firstVariableLinearExtIso R X n).hom.app Y =
      (rightDerivedLinearCoyonedaIsoExtFunctorObj R X n).hom.app Y := by
  change
    ((rightDerivedLinearCoyonedaIsoExtFunctorObj R X n).hom.app Y ≫
      (firstVariableLinearExtIso R X n).inv.app Y) ≫
        (firstVariableLinearExtIso R X n).hom.app Y =
      (rightDerivedLinearCoyonedaIsoExtFunctorObj R X n).hom.app Y
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

end CategoryTheory.Abelian
