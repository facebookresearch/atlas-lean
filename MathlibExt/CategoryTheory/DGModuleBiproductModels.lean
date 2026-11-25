/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.DGModuleConeShiftModels
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Actual DG-module biproducts

Every value is the native cochain biproduct. Its homogeneous action is
the actual block-diagonal action of the two given modules, and all four
inclusion/projection maps are fixed on those same blocks.

References: Keller, Deriving DG categories, §§2--3; Brav--Dyckerhoff,
arXiv:1606.00619v1, §6.2.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.DGModuleBiproductModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open CochainComplex.HomComplex

universe u
variable {k : Type u} [Field k]

/-- The actual block-diagonal homogeneous action of two DG modules. -/
def biproductActionDegree {C : DGCat k} (M N : RightModule k C)
    (x y : Cᵒᵖ) (p r : ℤ) (a : DGHom k p x y) :
    (M.toEnrichedFunctor.obj x ⊞ N.toEnrichedFunctor.obj x).X r ⟶
      (M.toEnrichedFunctor.obj y ⊞ N.toEnrichedFunctor.obj y).X (r + p) :=
  (biprod.fst : M.toEnrichedFunctor.obj x ⊞ N.toEnrichedFunctor.obj x ⟶ M.toEnrichedFunctor.obj x).f r ≫
      (M.toEnrichedFunctor.dgMap p a : Cochain _ _ p).v r (r + p) rfl ≫
      (biprod.inl : M.toEnrichedFunctor.obj y ⟶ M.toEnrichedFunctor.obj y ⊞ N.toEnrichedFunctor.obj y).f (r + p) +
    (biprod.snd : M.toEnrichedFunctor.obj x ⊞ N.toEnrichedFunctor.obj x ⟶ N.toEnrichedFunctor.obj x).f r ≫
      (N.toEnrichedFunctor.dgMap p a : Cochain _ _ p).v r (r + p) rfl ≫
      (biprod.inr : N.toEnrichedFunctor.obj y ⟶ M.toEnrichedFunctor.obj y ⊞ N.toEnrichedFunctor.obj y).f (r + p)

/-- The full module biproduct has every action and all four structural maps fixed. -/
structure ModuleBiproductModel {C : DGCat k} (M N : RightModule k C) where
  module : RightModule k C
  valueIso : ∀ x : Cᵒᵖ, module.toEnrichedFunctor.obj x ≅ M.toEnrichedFunctor.obj x ⊞ N.toEnrichedFunctor.obj x
  action_eq : ∀ (x y : Cᵒᵖ) (p r : ℤ) (a : DGHom k p x y),
    (module.toEnrichedFunctor.dgMap p a : Cochain _ _ p).v r (r + p) rfl ≫
      (valueIso y).hom.f (r + p) = (valueIso x).hom.f r ≫ biproductActionDegree M N x y p r a
  inl : M ⟶ module
  inr : N ⟶ module
  fst : module ⟶ M
  snd : module ⟶ N
  inl_eq : ∀ x : Cᵒᵖ,
    moduleComponent inl x ≫ (valueIso x).hom = biprod.inl
  inr_eq : ∀ x : Cᵒᵖ,
    moduleComponent inr x ≫ (valueIso x).hom = biprod.inr
  fst_eq : ∀ x : Cᵒᵖ,
    moduleComponent fst x = (valueIso x).hom ≫ biprod.fst
  snd_eq : ∀ x : Cᵒᵖ,
    moduleComponent snd x = (valueIso x).hom ≫ biprod.snd

/-- The biproduct of actual projective modules retains its projective lifting property. -/
structure CofibrantBiproductModel {C : DGCat k} (M N : DGDerivedModules k C)
    extends ModuleBiproductModel M.obj N.obj where
  cofibrant : IsCofibrantModule module

/-- The actual map of module biproducts is fixed on both source inclusions. -/
structure ModuleBiproductMapModel {C : DGCat k} {M N M' N' : RightModule k C}
    (P : ModuleBiproductModel M N) (Q : ModuleBiproductModel M' N') (f : M ⟶ M') (g : N ⟶ N') where
  map : P.module ⟶ Q.module
  inl_eq : P.inl ≫ map = f ≫ Q.inl
  inr_eq : P.inr ≫ map = g ≫ Q.inr

end MathlibExt.CategoryTheory.DGModuleBiproductModels
