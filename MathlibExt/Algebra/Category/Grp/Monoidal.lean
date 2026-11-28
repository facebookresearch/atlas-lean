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

-- BACKPORT: Integer-tensor structure adapted from Mathlib PR #42860 head
-- `4d9c97ac1bb4deb8ce8e6005aca99087372c2d77`,
-- path `Mathlib/Algebra/Category/Grp/Monoidal.lean`,
-- blob `8b91310c9117182a71ccf3d0cd58569c7f94830f`, authors Junyan Xu.
-- Imports, private extensionality proofs, instance names and documentation are adapted.
-- The braiding spelling is corrected. See `BACKPORTS.md` for the removal condition.

public import MathlibExt.Algebra.Category.Grp.ZModuleEquivalenceCompat
public import MathlibExt.LinearAlgebra.TensorProduct.BasicCompat
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Integer tensor products and internal Hom of abelian groups

The category `Ab` of abelian groups in a fixed universe is symmetric
monoidal under tensor product over `ℤ`, with unit the copy of `ℤ` in
that universe. The braiding sends `x ⊗ y` to `y ⊗ x`. The equivalence
with modules over the same-universe copy of `ℤ` respects tensor products
and equips `Ab` with the corresponding monoidal closed structure.
-/

universe u

open CategoryTheory MonoidalCategory TensorProduct

@[expose] public section

/-- For a commutative semiring `R` and `R`-modules `M`, `N`, additive
maps from `M ⊗[R] N` to an additive commutative monoid `P` are equal
if their values agree on every pure tensor `x ⊗ y`. -/
private theorem TensorProduct.extAdd {R : Type*} [CommSemiring R] {M N P₂ : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P₂] [Module R M] [Module R N]
    {F : Type*} [FunLike F (M ⊗[R] N) P₂] [AddMonoidHomClass F (M ⊗[R] N) P₂]
    {g h : F} (H : ∀ (x : M) (y : N), g (x ⊗ₜ y) = h (x ⊗ₜ y)) : g = h := by
  apply DFunLike.ext _ _ fun t ↦ t.inductionOn H fun x y ha hb ↦ by
    simp only [map_add, ha, hb]

/-- For commutative semirings `R`, `R₂`, modules `M`, `N`, `M₂` with
the commuting actions needed for `(M ⊗[R] N) ⊗[R₂] M₂`, two
additive maps to `P₃` are equal if they agree on every
`(x ⊗ y) ⊗ z`. No linearity of these two maps is required. -/
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

/-- In the category `Ab` of abelian groups in universe `u`, tensor
product over `ℤ`, the same-universe copy of `ℤ` as unit, and the
integer tensor associator and unit maps form the monoidal structure data. -/
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

/-- An abelian group in universe `u` has its unique module structure
over the copy of `ℤ` in universe `u`. This gives an equivalence
`Ab ≌ ModuleCat (ULift.{u} ℤ)` with the inverse forgetting that integer action. -/
@[implicit_reducible, simps! functor inverse]
noncomputable def toModuleCatULiftInt : Ab.{u} ≌ ModuleCat.{u} (ULift.{u} ℤ) :=
  ModuleCat.intEquivalence.symm.trans
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv ULift.ringEquiv)

/-- For abelian groups `X`, `Y` and a module `W` over the same-universe
copy of `ℤ`, two module morphisms from the image of `X ⊗ Y` to `W`
are equal if they agree on each pure tensor `x ⊗ y`. -/
lemma toModuleCatULiftInt_tensor_ext {X Y : Ab.{u}} {W : ModuleCat.{u} (ULift.{u} ℤ)}
    {f g : toModuleCatULiftInt.functor.obj (X ⊗ Y) ⟶ W}
    (h : ∀ (x : X) (y : Y), f.hom (x ⊗ₜ y) = g.hom (x ⊗ₜ y)) : f = g := by
  apply ModuleCat.hom_ext
  apply TensorProduct.extAdd
  exact h

/-- The equivalence from abelian groups in universe `u` to modules over
the same-universe copy of `ℤ` preserves the specified tensor and
unit maps. These comparisons induce the integer-tensor monoidal
structure on `Ab`. -/
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

/-- The category `Ab` of abelian groups in universe `u` is monoidal
with tensor product over `ℤ`, unit `ULift.{u} ℤ`, and the tensor
associativity and unit isomorphisms. These maps satisfy the monoidal coherence laws. -/
noncomputable instance monoidalCategoryCompat : MonoidalCategory Ab.{u} :=
  Monoidal.induced toModuleCatULiftInt.functor inducingFunctorData

noncomputable instance : toModuleCatULiftInt.{u}.functor.Monoidal :=
  Monoidal.fromInducedMonoidal _ inducingFunctorData

/-- The integer tensor braiding of abelian groups exchanges the two factors and is
compatible with the tensor associator and unitors. -/
noncomputable instance braidedCategoryCompat : BraidedCategory Ab.{u} :=
  .ofFaithful toModuleCatULiftInt.functor
    (fun M N ↦ (TensorProduct.comm ℤ M N).toAddEquiv.toAddCommGrpIso)
    fun X Y ↦ by
      apply ModuleCat.hom_ext
      apply TensorProduct.extAdd
      intro x y; rfl

/-- The integer tensor braiding of abelian groups is symmetric: exchanging the factors
twice gives the identity. -/
noncomputable instance symmetricCategoryCompat : SymmetricCategory Ab.{u} where
  symmetry _ _ := by
    apply AddCommGrpCat.hom_ext
    apply TensorProduct.extAdd (R := ℤ)
    intro x y; rfl

/-- The integer-tensor monoidal category `Ab` is closed: tensoring with
each abelian group has a right adjoint given by its internal additive
Hom group. The corresponding tensor–Hom adjunction respects the monoidal structure. -/
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

/-- For abelian groups `M₁`, `M₂` in the fixed universe, the forward
braiding `M₁ ⊗ M₂ → M₂ ⊗ M₁` sends the pure tensor `x ⊗ y`
to `y ⊗ x`. -/
@[simp] lemma braiding_hom_apply (x : M₁) (y : M₂) :
    (β_ M₁ M₂).hom (x ⊗ₜ y) = y ⊗ₜ x := rfl

@[simp] lemma braiding_inv_apply (x : M₁) (y : M₂) :
    (β_ M₁ M₂).inv (y ⊗ₜ x) = x ⊗ₜ y := rfl

@[simp] lemma ihom_obj (M N : Ab.{u}) : (ihom M).obj N = of (M →+ N) := rfl


end AddCommGrpCat

end
