/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
/-
Copyright (c) 2026 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

-- BACKPORT: Near-verbatim full-file copy of PR #42860 head
-- `4d9c97ac1bb4deb8ce8e6005aca99087372c2d77`,
-- path `Mathlib/Algebra/Category/Grp/Monoidal.lean`,
-- blob `8b91310c9117182a71ccf3d0cd58569c7f94830f`, authors Junyan Xu.
-- See `BACKPORTS.md` for copied surface, adaptations, and upgrade-removal steps.

public import MathlibExt.Algebra.Category.Grp.ZModuleEquivalenceCompat
public import MathlibExt.LinearAlgebra.TensorProduct.BasicCompat
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# The symmetric monoidal structure on abelian groups

The category `AddCommGrpCat.{u}` of abelian groups in the universe `u` is equipped with the
monoidal structure given by the tensor product over `ℤ`, with unit the (universe-lifted) copy
`ULift.{u} ℤ` of `ℤ`.

The construction follows the pattern used for `ModuleCat.monoidalCategory`: the data of the
monoidal structure (tensor product, unit, associator and unitors) is given explicitly, and the
axioms are transported, via `CategoryTheory.Monoidal.induced`, along the faithful functor
`AddCommGrpCat.toModuleCatULiftInt : AddCommGrpCat.{u} ⥤ ModuleCat.{u} (ULift.{u} ℤ)`, which is
in fact an equivalence of categories. The braiding and the symmetry, as well as the monoidal
closed structure, are then obtained by transport along this equivalence.
-/

universe u

open CategoryTheory MonoidalCategory TensorProduct

@[expose] public section

/-- Additive maps on a tensor product are equal when they agree on pure tensors. -/
private theorem TensorProduct.extAdd {R : Type*} [CommSemiring R] {M N P₂ : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P₂] [Module R M] [Module R N]
    {F : Type*} [FunLike F (M ⊗[R] N) P₂] [AddMonoidHomClass F (M ⊗[R] N) P₂]
    {g h : F} (H : ∀ (x : M) (y : N), g (x ⊗ₜ y) = h (x ⊗ₜ y)) : g = h := by
  apply DFunLike.ext _ _ fun t ↦ t.inductionOn H fun x y ha hb ↦ by
    simp only [map_add, ha, hb]

/-- Additive maps on a threefold tensor product are equal when they agree on pure tensors. -/
private theorem TensorProduct.ext_threefoldAdd {R R₂ : Type*} [CommSemiring R]
    [CommSemiring R₂] {M N M₂ P₃ : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid M₂] [AddCommMonoid P₃]
    [Module R M] [Module R N] [Module R₂ M₂]
    [Module R₂ M] [SMulCommClass R R₂ M]
    {F : Type*} [FunLike F (M ⊗[R] N ⊗[R₂] M₂) P₃]
    [AddMonoidHomClass F (M ⊗[R] N ⊗[R₂] M₂) P₃]
    {g h : F} (H : ∀ (x : M) (y : N) (z : M₂), g (x ⊗ₜ y ⊗ₜ z) = h (x ⊗ₜ y ⊗ₜ z)) :
    g = h := by
  apply TensorProduct.extAdd
  intro xy z
  induction xy using TensorProduct.inductionOn with
  | tmul m n => exact H m n z
  | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]

namespace AddCommGrpCat

/-- The data of the monoidal structure on abelian groups: the tensor product over `ℤ`, with
unit the universe-lifted copy `ULift ℤ` of `ℤ`. -/
noncomputable instance monoidalCategoryStruct : MonoidalCategoryStruct Ab.{u} where
  tensorObj M N := of (M ⊗[ℤ] N)
  whiskerLeft M _ _ f := ofHom (f.hom.toIntLinearMap.lTensor M)
  whiskerRight f N := ofHom (f.hom.toIntLinearMap.rTensor N)
  tensorHom f g := ofHom (TensorProduct.map f.hom.toIntLinearMap g.hom.toIntLinearMap)
  tensorUnit := of (ULift.{u} ℤ)
  associator M N K := (TensorProduct.assoc ℤ M N K).toAddEquiv.toAddCommGrpIso
  leftUnitor M := ((TensorProduct.congr ULift.moduleEquiv (LinearEquiv.refl ℤ M)).trans
    (TensorProduct.lid ℤ M)).toAddEquiv.toAddCommGrpIso
  rightUnitor M := ((TensorProduct.congr (LinearEquiv.refl ℤ M) ULift.moduleEquiv).trans
    (TensorProduct.rid ℤ M)).toAddEquiv.toAddCommGrpIso

/-- The functor sending an abelian group to the corresponding module over `ULift.{u} ℤ`,
which is an equivalence of categories.

This is the reverse of
`ModuleCat.uliftIntAddCommGrpEquivalence` (same composition of the
integer-module equivalence and restriction of scalars, opposite direction).
-/
@[implicit_reducible, simps! functor inverse]
noncomputable def toModuleCatULiftInt : Ab.{u} ≌ ModuleCat.{u} (ULift.{u} ℤ) :=
  ModuleCat.intEquivalence.symm.trans
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv ULift.ringEquiv)

/-- Extensionality for morphisms out of the image of a tensor product of abelian groups. -/
lemma toModuleCatULiftInt_tensor_ext {X Y : Ab.{u}} {W : ModuleCat.{u} (ULift.{u} ℤ)}
    {f g : toModuleCatULiftInt.functor.obj (X ⊗ Y) ⟶ W}
    (h : ∀ (x : X) (y : Y), f.hom (x ⊗ₜ y) = g.hom (x ⊗ₜ y)) : f = g := by
  apply ModuleCat.hom_ext
  apply TensorProduct.extAdd
  exact h

/-- The data needed to induce the monoidal structure on `Ab` from the one on
`ModuleCat (ULift ℤ)`. -/
noncomputable def inducingFunctorData :
    Monoidal.InducingFunctorData toModuleCatULiftInt.functor where
  μIso X Y := (TensorProduct.equivOfCompatibleSMul ℤ (ULift ℤ) (ULift ℤ) X Y).toModuleIso
  εIso := .refl _
  whiskerLeft_eq _ _ _ _ := toModuleCatULiftInt_tensor_ext fun _ _ ↦ rfl
  whiskerRight_eq _ _ := toModuleCatULiftInt_tensor_ext fun _ _ ↦ rfl
  tensorHom_eq _ _ := toModuleCatULiftInt_tensor_ext fun _ _ ↦ rfl
  associator_eq X Y Z := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext_threefoldAdd (R := ℤ) (R₂ := ℤ)
    intro x y z
    rfl
  leftUnitor_eq _ := toModuleCatULiftInt_tensor_ext fun _ _ ↦ rfl
  rightUnitor_eq _ := toModuleCatULiftInt_tensor_ext fun _ _ ↦ rfl

/-- The monoidal structure on the category of abelian groups, given by the tensor product
over `ℤ`. -/
noncomputable instance monoidalCategoryCompat : MonoidalCategory Ab.{u} :=
  Monoidal.induced toModuleCatULiftInt.functor inducingFunctorData

noncomputable instance : toModuleCatULiftInt.{u}.functor.Monoidal :=
  Monoidal.fromInducedMonoidal _ inducingFunctorData

noncomputable instance braidedCategoryCompat : BraidedCategory Ab.{u} :=
  .ofFaithful toModuleCatULiftInt.functor
    (fun M N ↦ (TensorProduct.comm ℤ M N).toAddEquiv.toAddCommGrpIso)
    fun X Y ↦ by
      apply ModuleCat.hom_ext
      apply TensorProduct.extAdd
      intro x y; rfl

noncomputable instance symmetricCategoryCompat : SymmetricCategory Ab.{u} where
  symmetry _ _ := by
    apply AddCommGrpCat.hom_ext
    apply TensorProduct.extAdd (R := ℤ)
    intro x y; rfl

/-- The category of abelian groups is monoidal closed. -/
noncomputable instance monoidalClosed : MonoidalClosed Ab.{u} where
  closed M :=
  { rightAdj := coyoneda.obj (.op M)
    adj := .mkOfHomEquiv
      { homEquiv N P := ((β_ M N).homFromEquiv.trans <| ConcreteCategory.homEquiv.trans
          liftAddEquivInt.symm.toEquiv).trans ConcreteCategory.homEquiv.symm
        homEquiv_naturality_left_symm _ _ := by
          apply AddCommGrpCat.hom_ext
          apply TensorProduct.extAdd (R := ℤ)
          intro m n
          rfl
        homEquiv_naturality_right _ _ := rfl } }

lemma tensorObj_def (M N : Ab.{u}) : (M ⊗ N : Ab.{u}) = of (M ⊗[ℤ] N) :=
  rfl

lemma tensorUnit_def : (𝟙_ Ab.{u}) = of (ULift.{u} ℤ) := rfl

variable {M₁ M₂ M₃ M₄ : Ab.{u}}

@[simp] lemma whiskerLeft_apply (M : Ab.{u}) (f : M₁ ⟶ M₂) (m : M) (x : M₁) :
    (M ◁ f) (m ⊗ₜ x) = m ⊗ₜ f x := rfl

@[simp] lemma whiskerRight_apply (f : M₁ ⟶ M₂) (M : Ab.{u}) (x : M₁) (m : M) :
    (f ▷ M) (x ⊗ₜ m) = f x ⊗ₜ m := rfl

@[simp] lemma tensorHom_apply (f : M₁ ⟶ M₂) (g : M₃ ⟶ M₄) (x : M₁) (y : M₃) :
    (f ⊗ₘ g) (x ⊗ₜ y) = f x ⊗ₜ g y := rfl

@[simp] lemma associator_hom_apply (x : M₁) (y : M₂) (z : M₃) :
    (α_ M₁ M₂ M₃).hom ((x ⊗ₜ y) ⊗ₜ z) = x ⊗ₜ (y ⊗ₜ z) := rfl

@[simp] lemma leftUnitor_hom_apply (a : ULift.{u} ℤ) (x : M₁) :
    (λ_ M₁).hom (a ⊗ₜ x) = a.down • x := rfl

@[simp] lemma rightUnitor_hom_apply (x : M₁) (a : ULift.{u} ℤ) :
    (ρ_ M₁).hom (x ⊗ₜ a) = a.down • x := rfl

/-- The braiding of additive groups swaps the factors of a pure tensor. -/
@[simp] lemma braiding_hom_apply (x : M₁) (y : M₂) :
    (β_ M₁ M₂).hom (x ⊗ₜ y) = y ⊗ₜ x := rfl

@[simp] lemma braiding_inv_apply (x : M₁) (y : M₂) :
    (β_ M₁ M₂).inv (y ⊗ₜ x) = x ⊗ₜ y := rfl

@[simp] lemma ihom_obj (M N : Ab.{u}) : (ihom M).obj N = of (M →+ N) := rfl

/-- The tensor monoidal structure on additive groups. -/
@[nolint defsWithUnderscore]
noncomputable abbrev instMonoidalCategoryAb_mathlibExt : MonoidalCategory Ab.{u} :=
  monoidalCategoryCompat

/-- The tensor braiding on additive groups. -/
@[nolint defsWithUnderscore]
noncomputable abbrev instBraidedCategoryAb_mathlibExt : BraidedCategory Ab.{u} :=
  braidedCategoryCompat

/-- The tensor symmetry on additive groups. -/
@[nolint defsWithUnderscore]
noncomputable abbrev instSymmetricCategoryAb_mathlibExt : SymmetricCategory Ab.{u} :=
  symmetricCategoryCompat

attribute [deprecated monoidalCategoryCompat (since := "2026-11-09")]
  instMonoidalCategoryAb_mathlibExt
attribute [deprecated braidedCategoryCompat (since := "2026-11-09")]
  instBraidedCategoryAb_mathlibExt
attribute [deprecated symmetricCategoryCompat (since := "2026-11-09")]
  instSymmetricCategoryAb_mathlibExt

end AddCommGrpCat

end
