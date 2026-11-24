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
# Right-derived linear Hom and the existing first-variable Ext functor

The comparison passes through the derived-category Ext module. Both comparison factors have
cocycle representatives and proved naturality. The two Ext implementations are connected by a
constructed natural isomorphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

universe r v u

namespace CategoryTheory.Abelian

variable (R : Type r) [CommRing R]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
variable [EnoughProjectives C] [HasInjectiveResolutions C] [HasExt.{v} C]

/-- Right-derived linear Hom computes the existing first-variable Ext functor. -/
def rightDerivedLinearCoyonedaIsoFirstVariableExt (X : C) (n : ℕ) :
    ((linearCoyoneda R C).obj (op X)).rightDerived n ≅
      (_root_.Ext R C n).obj (op X) :=
  rightDerivedLinearCoyonedaIsoExtFunctorObj R X n ≪≫
    (firstVariableLinearExtIso R X n).symm

/--
The bridge agrees with the Ext comparison after applying the constructed comparison for the old
first-variable model.
-/
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
