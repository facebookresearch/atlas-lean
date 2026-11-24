/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Monoidal.RightModuleRelativeTensorCoherence
public import MathlibExt.CategoryTheory.Monoidal.RightModuleFreeCoefficient

/-!
# Complete one-free and two-free right-module tensor comparisons

The comparisons use the stock right-module category, the selected Mod relative
quotient, and the existing RightModuleFree.functor and adjunction. Their complete
Hom functions, naturalities, and CoreMonoidal/Braided laws retain these operators.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory MonObj MonoidalOpposite
open CategoryTheory.CommutativeModuleConversion
open CategoryTheory.CommutativeModuleConversion.RightModule
open scoped CategoryTheory.MonObj

namespace CategoryTheory.RightModuleFree

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
variable (M : C) [MonObj M]


/-- Whole maps from the existing free object are determined by its original generator. -/
theorem free_hom_ext (P : C) (Y : RightModule M) (f g : freeObject M P ⟶ Y)
    (h : freeGenerator M P ≫ f.hom = freeGenerator M P ≫ g.hom) : f = g := by
  apply (freeHomEquiv M P Y).injective
  exact (congrFun (freeHomEquiv_toFun M P Y) f).trans
    (h.trans (congrFun (freeHomEquiv_toFun M P Y) g).symm)

section Symmetric

variable [SymmetricCategory C] [IsCommMonObj M]
variable [HasCoequalizers C]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The transported tensor product `tensorMonoidal M` on right modules, as a local instance. -/
local instance : MonoidalCategory (RightModule M) := tensorMonoidal M
/-- The transported symmetric structure `tensorSymmetric M` on right modules, as a local
instance. -/
local instance : SymmetricCategory (RightModule M) := tensorSymmetric M

/-- The actual contraction from a free first factor and a module second factor. -/
def freeLeftTensorCoefficient (P : C) (Y : RightModule M) :
    (P ⊗ M) ⊗ Y.X ⟶ P ⊗ Y.X :=
  (α_ P M Y.X).hom ≫ (P ◁ leftAction M Y)

omit [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
/-- The contraction balances the complete original free and module actions. -/
theorem freeLeftTensorCoefficient_balanced (P : C) (Y : RightModule M) :
    ((freeObject M P).action ▷ Y.X) ≫ freeLeftTensorCoefficient M P Y =
      (α_ (P ⊗ M) M Y.X).hom ≫
        ((P ⊗ M) ◁ leftAction M Y) ≫ freeLeftTensorCoefficient M P Y := by
  change (((α_ P M M).hom ≫ (P ◁ μ[M])) ▷ Y.X) ≫
      (α_ P M Y.X).hom ≫ (P ◁ leftAction M Y) =
    (α_ (P ⊗ M) M Y.X).hom ≫ ((P ⊗ M) ◁ leftAction M Y) ≫
      (α_ P M Y.X).hom ≫ (P ◁ leftAction M Y)
  simp only [comp_whiskerRight, Category.assoc]
  rw [associator_naturality_middle_assoc, associator_naturality_right_assoc]
  rw [← whiskerLeft_comp, leftAction_mul M Y]
  simp only [whiskerLeft_comp]
  slice_lhs 1 3 => rw [pentagon]
  simp only [Category.assoc]

omit [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
/-- The contraction is right-linear by the actual commuting-actions equation. -/
theorem freeLeftTensorCoefficient_right_linear (P : C) (Y : RightModule M) :
    (α_ (P ⊗ M) Y.X M).hom ≫ ((P ⊗ M) ◁ Y.action) ≫
        freeLeftTensorCoefficient M P Y =
      (freeLeftTensorCoefficient M P Y ▷ M) ≫
        (coefficientTensor M P Y).action := by
  change (α_ (P ⊗ M) Y.X M).hom ≫ ((P ⊗ M) ◁ Y.action) ≫
      (α_ P M Y.X).hom ≫ (P ◁ leftAction M Y) =
    (((α_ P M Y.X).hom ≫ (P ◁ leftAction M Y)) ▷ M) ≫
      (α_ P Y.X M).hom ≫ (P ◁ Y.action)
  simp only [comp_whiskerRight, Category.assoc]
  rw [associator_naturality_right_assoc, associator_naturality_middle_assoc]
  slice_rhs 3 4 => rw [← whiskerLeft_comp, leftAction_comm M Y]
  simp only [whiskerLeft_comp]
  slice_rhs 1 3 => rw [pentagon]
  simp only [Category.assoc]

/-- The full forward one-free map is the actual balanced right-linear descent. -/
def freeLeftTensorHom (P : C) (Y : RightModule M) :
    freeObject M P ⊗ Y ⟶ coefficientTensor M P Y :=
  relativeTensorDesc M (freeObject M P) Y (coefficientTensor M P Y)
    (freeLeftTensorCoefficient M P Y)
    (freeLeftTensorCoefficient_balanced M P Y)
    (freeLeftTensorCoefficient_right_linear M P Y)

/-- Projection of the entire one-free forward map is the original contraction. -/
@[reassoc]
theorem freeLeftTensorHom_π (P : C) (Y : RightModule M) :
    relativeTensorπ M (freeObject M P) Y ≫ (freeLeftTensorHom M P Y).hom =
      freeLeftTensorCoefficient M P Y :=
  relativeTensorDesc_π M (freeObject M P) Y (coefficientTensor M P Y)
    (freeLeftTensorCoefficient M P Y)
    (freeLeftTensorCoefficient_balanced M P Y)
    (freeLeftTensorCoefficient_right_linear M P Y)

/-- The actual generator in the first factor gives the entire one-free inverse. -/
def freeLeftTensorInv (P : C) (Y : RightModule M) :
    coefficientTensor M P Y ⟶ freeObject M P ⊗ Y :=
  Mod.Hom.mk' ((freeGenerator M P ▷ Y.X) ≫ relativeTensorπ M (freeObject M P) Y) (by
    change ((α_ P Y.X M).hom ≫ (P ◁ Y.action)) ≫
        ((freeGenerator M P ▷ Y.X) ≫ relativeTensorπ M (freeObject M P) Y) =
      (((freeGenerator M P ▷ Y.X) ≫ relativeTensorπ M (freeObject M P) Y) ▷ M) ≫
        (freeObject M P ⊗ Y).action
    simp only [comp_whiskerRight, Category.assoc]
    rw [relativeTensorπ_action, associator_naturality_left_assoc, ← whisker_exchange_assoc])

/-- The whole one-free inverse carrier map is the original generator and quotient. -/
@[simp]
theorem freeLeftTensorInv_hom (P : C) (Y : RightModule M) :
    (freeLeftTensorInv M P Y).hom =
      (freeGenerator M P ▷ Y.X) ≫ relativeTensorπ M (freeObject M P) Y := rfl

omit [IsCommMonObj M] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
/-- Original unit insertion followed by contraction is the entire coefficient identity. -/
theorem freeLeftTensorCoefficient_generator (P : C) (Y : RightModule M) :
    (freeGenerator M P ▷ Y.X) ≫ freeLeftTensorCoefficient M P Y = 𝟙 (P ⊗ Y.X) := by
  change (((ρ_ P).inv ≫ (P ◁ η[M])) ▷ Y.X) ≫
    ((α_ P M Y.X).hom ≫ (P ◁ leftAction M Y)) = 𝟙 (P ⊗ Y.X)
  simp only [comp_whiskerRight, Category.assoc]
  rw [associator_naturality_middle_assoc, ← whiskerLeft_comp, leftAction_one M Y]
  monoidal

/-- Generator-action and the original balancing equation recover the entire projection. -/
theorem freeLeftTensorCoefficient_inv_π (P : C) (Y : RightModule M) :
    freeLeftTensorCoefficient M P Y ≫ (freeLeftTensorInv M P Y).hom =
      relativeTensorπ M (freeObject M P) Y := by
  let δ : (P ⊗ M) ⊗ Y.X ⟶ ((P ⊗ M) ⊗ M) ⊗ Y.X :=
    ((freeGenerator M P ▷ M) ▷ Y.X)
  have hδ : δ ≫ ((freeObject M P).action ▷ Y.X) = 𝟙 ((P ⊗ M) ⊗ Y.X) := by
    dsimp only [δ]
    erw [← comp_whiskerRight, freeGenerator_action, id_whiskerRight]
  have hδ' :
      δ ≫ (α_ (P ⊗ M) M Y.X).hom ≫ ((P ⊗ M) ◁ leftAction M Y) ≫
          relativeTensorπ M (freeObject M P) Y =
        freeLeftTensorCoefficient M P Y ≫ (freeLeftTensorInv M P Y).hom := by
    dsimp only [δ, freeLeftTensorCoefficient, freeLeftTensorInv]
    erw [associator_naturality_left_assoc, ← whisker_exchange_assoc]
    simp only [Category.assoc]
    rfl
  calc
    _ = δ ≫ (α_ (P ⊗ M) M Y.X).hom ≫ ((P ⊗ M) ◁ leftAction M Y) ≫
        relativeTensorπ M (freeObject M P) Y := hδ'.symm
    _ = δ ≫ ((freeObject M P).action ▷ Y.X) ≫
        relativeTensorπ M (freeObject M P) Y := by
      erw [relativeTensorπ_balance]
      rfl
    _ = _ := by erw [← Category.assoc, hδ, Category.id_comp]

/-- The actual one-free contraction and generator maps are inverse module isomorphisms. -/
def freeLeftTensorIso (P : C) (Y : RightModule M) :
    freeObject M P ⊗ Y ≅ coefficientTensor M P Y where
  hom := freeLeftTensorHom M P Y
  inv := freeLeftTensorInv M P Y
  hom_inv_id := by
    apply relativeTensor_hom_ext M (freeObject M P) Y
    simp only [Mod.comp_hom', Mod.id_hom']
    erw [← Category.assoc, freeLeftTensorHom_π, freeLeftTensorCoefficient_inv_π,
      Category.comp_id]
  inv_hom_id := by
    apply Mod.hom_ext
    simp only [Mod.comp_hom', Mod.id_hom', freeLeftTensorInv_hom]
    erw [Category.assoc, freeLeftTensorHom_π, freeLeftTensorCoefficient_generator]

/-- The entire one-free forward comparison retains its actual projection characteristic. -/
@[reassoc]
theorem freeLeftTensorIso_hom_π (P : C) (Y : RightModule M) :
    relativeTensorπ M (freeObject M P) Y ≫ (freeLeftTensorIso M P Y).hom.hom =
      freeLeftTensorCoefficient M P Y :=
  freeLeftTensorHom_π M P Y

/-- The entire one-free inverse comparison is the original generator and projection. -/
@[simp]
theorem freeLeftTensorIso_inv (P : C) (Y : RightModule M) :
    (freeLeftTensorIso M P Y).inv.hom =
      (freeGenerator M P ▷ Y.X) ≫ relativeTensorπ M (freeObject M P) Y := rfl

omit [IsCommMonObj M] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
/-- Both entire contraction inputs preserve the original coefficient tensor map. -/
@[reassoc]
theorem freeLeftTensorCoefficient_naturality {P P' : C} {Y Y' : RightModule M}
    (f : P ⟶ P') (g : Y ⟶ Y') :
    ((f ▷ M) ⊗ₘ g.hom) ≫ freeLeftTensorCoefficient M P' Y' =
      freeLeftTensorCoefficient M P Y ≫ (f ⊗ₘ g.hom) := by
  have ha :
      ((f ▷ M) ⊗ₘ g.hom) ≫ (α_ P' M Y'.X).hom =
        (α_ P M Y.X).hom ≫ (f ⊗ₘ (M ◁ g.hom)) := by
    simpa only [tensorHom_id, id_tensorHom] using
      associator_naturality f (𝟙 M) g.hom
  dsimp only [freeLeftTensorCoefficient]
  rw [← Category.assoc, ha, Category.assoc]
  rw [← id_tensorHom P' (leftAction M Y'), tensorHom_comp_tensorHom, Category.comp_id]
  rw [← leftAction_hom M g]
  have ht : (P ◁ leftAction M Y) ≫ (f ⊗ₘ g.hom) =
      f ⊗ₘ (leftAction M Y ≫ g.hom) := by
    rw [← id_tensorHom P (leftAction M Y), tensorHom_comp_tensorHom, Category.id_comp]
  exact (congrArg (fun k => (α_ P M Y.X).hom ≫ k) ht).symm.trans
    (Category.assoc (α_ P M Y.X).hom (P ◁ leftAction M Y) (f ⊗ₘ g.hom)).symm

/-- The complete one-free forward family is natural under every coefficient and module map. -/
@[reassoc]
theorem freeLeftTensorIso_naturality {P P' : C} {Y Y' : RightModule M}
    (f : P ⟶ P') (g : Y ⟶ Y') :
    relativeTensorMap M (freeMap M f) g ≫ (freeLeftTensorIso M P' Y').hom =
      (freeLeftTensorIso M P Y).hom ≫ coefficientTensorMap M f g := by
  apply relativeTensor_hom_ext M (freeObject M P) Y
  simp only [Mod.comp_hom', coefficientTensorMap_hom]
  rw [← Category.assoc, relativeTensorMap_π, Category.assoc,
    freeLeftTensorIso_hom_π, ← Category.assoc, freeLeftTensorIso_hom_π]
  exact freeLeftTensorCoefficient_naturality M f g

/-- The entire one-free inverse family is natural under every coefficient and module map. -/
@[reassoc]
theorem freeLeftTensorIso_inv_naturality {P P' : C} {Y Y' : RightModule M}
    (f : P ⟶ P') (g : Y ⟶ Y') :
    coefficientTensorMap M f g ≫ (freeLeftTensorIso M P' Y').inv =
      (freeLeftTensorIso M P Y).inv ≫ relativeTensorMap M (freeMap M f) g := by
  apply (cancel_mono (freeLeftTensorIso M P' Y').hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [freeLeftTensorIso_naturality M f g]
  simp only [Iso.inv_hom_id_assoc]

/-- The actual one-free family is a functor of both original input arrows. -/
def freeLeftTensorPairFunctor : C × RightModule M ⥤ RightModule M where
  obj P := freeObject M P.1 ⊗ P.2
  map f := relativeTensorMap M (freeMap M f.1) f.2
  map_id P := by
    change (functor M).map (𝟙 P.1) ⊗ₘ (𝟙 P.2) = 𝟙 _
    rw [Functor.map_id, id_tensorHom_id]
  map_comp f g := by
    change relativeTensorMap M (freeMap M (f.1 ≫ g.1)) (f.2 ≫ g.2) = _
    rw [freeMap_comp, relativeTensorMap_comp]

/-- The complete one-free isomorphism is an actual natural isomorphism of both-input functors. -/
def freeLeftTensorNatIso :
    freeLeftTensorPairFunctor M ≅ coefficientTensorPairFunctor M :=
  NatIso.ofComponents (fun P => freeLeftTensorIso M P.1 P.2)
    (by intro P Q f; exact freeLeftTensorIso_naturality M f.1 f.2)

/-- The entire one-free Hom equivalence is given by the actual inverse and forward maps. -/
def freeLeftTensorHomEquiv (P : C) (Y Z : RightModule M) :
    (freeObject M P ⊗ Y ⟶ Z) ≃ (coefficientTensor M P Y ⟶ Z) where
  toFun f := (freeLeftTensorIso M P Y).inv ≫ f
  invFun f := (freeLeftTensorIso M P Y).hom ≫ f
  left_inv f := by
    change (freeLeftTensorIso M P Y).hom ≫ ((freeLeftTensorIso M P Y).inv ≫ f) = f
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  right_inv f := by
    change (freeLeftTensorIso M P Y).inv ≫ ((freeLeftTensorIso M P Y).hom ≫ f) = f
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The full forward one-free Hom function is original generator restriction. -/
theorem freeLeftTensorHomEquiv_toFun (P : C) (Y Z : RightModule M) :
    (freeLeftTensorHomEquiv M P Y Z).toFun =
      (fun f => (freeLeftTensorIso M P Y).inv ≫ f) := rfl

/-- The full inverse one-free Hom function is original descent before the entire module arrow. -/
theorem freeLeftTensorHomEquiv_invFun (P : C) (Y Z : RightModule M) :
    (freeLeftTensorHomEquiv M P Y Z).invFun =
      (fun f => (freeLeftTensorIso M P Y).hom ≫ f) := rfl

/-- The full forward Hom carrier function retains generator, quotient and whole target map. -/
theorem freeLeftTensorHomEquiv_hom (P : C) (Y Z : RightModule M) :
    (fun f : freeObject M P ⊗ Y ⟶ Z => (freeLeftTensorHomEquiv M P Y Z f).hom) =
      (fun f => (freeGenerator M P ▷ Y.X) ≫
        relativeTensorπ M (freeObject M P) Y ≫ f.hom) := by
  funext f
  change (freeLeftTensorIso M P Y).inv.hom ≫ f.hom = _
  rw [freeLeftTensorIso_inv, Category.assoc]

/-- Both complete source arrows are respected by the forward one-free Hom function. -/
theorem freeLeftTensorHomEquiv_naturality_left
    {P P' : C} {Y Y' : RightModule M} (Z : RightModule M)
    (f : P' ⟶ P) (g : Y' ⟶ Y) (h : freeObject M P ⊗ Y ⟶ Z) :
    freeLeftTensorHomEquiv M P' Y' Z
        (relativeTensorMap M (freeMap M f) g ≫ h) =
      coefficientTensorMap M f g ≫ freeLeftTensorHomEquiv M P Y Z h := by
  change (freeLeftTensorIso M P' Y').inv ≫
      relativeTensorMap M (freeMap M f) g ≫ h =
    coefficientTensorMap M f g ≫ (freeLeftTensorIso M P Y).inv ≫ h
  simpa only [Category.assoc] using
    congrArg (fun k => k ≫ h) (freeLeftTensorIso_inv_naturality M f g).symm

/-- Every complete target arrow is respected by the forward one-free Hom function. -/
theorem freeLeftTensorHomEquiv_naturality_right
    (P : C) (Y : RightModule M) {Z Z' : RightModule M}
    (h : freeObject M P ⊗ Y ⟶ Z) (f : Z ⟶ Z') :
    freeLeftTensorHomEquiv M P Y Z' (h ≫ f) =
      freeLeftTensorHomEquiv M P Y Z h ≫ f := by
  change (freeLeftTensorIso M P Y).inv ≫ (h ≫ f) =
    ((freeLeftTensorIso M P Y).inv ≫ h) ≫ f
  exact (Category.assoc _ _ _).symm

/-- Both complete source arrows are respected by the inverse one-free Hom function. -/
theorem freeLeftTensorHomEquiv_inv_naturality_left
    {P P' : C} {Y Y' : RightModule M} (Z : RightModule M)
    (f : P' ⟶ P) (g : Y' ⟶ Y) (h : coefficientTensor M P Y ⟶ Z) :
    (freeLeftTensorHomEquiv M P' Y' Z).symm (coefficientTensorMap M f g ≫ h) =
      relativeTensorMap M (freeMap M f) g ≫ (freeLeftTensorHomEquiv M P Y Z).symm h := by
  change (freeLeftTensorIso M P' Y').hom ≫ coefficientTensorMap M f g ≫ h =
    relativeTensorMap M (freeMap M f) g ≫ (freeLeftTensorIso M P Y).hom ≫ h
  simpa only [Category.assoc] using
    congrArg (fun k => k ≫ h) (freeLeftTensorIso_naturality M f g).symm

/-- Every complete target arrow is respected by the inverse one-free Hom function. -/
theorem freeLeftTensorHomEquiv_inv_naturality_right
    (P : C) (Y : RightModule M) {Z Z' : RightModule M}
    (h : coefficientTensor M P Y ⟶ Z) (f : Z ⟶ Z') :
    (freeLeftTensorHomEquiv M P Y Z').symm (h ≫ f) =
      (freeLeftTensorHomEquiv M P Y Z).symm h ≫ f := by
  change (freeLeftTensorIso M P Y).hom ≫ (h ≫ f) =
    ((freeLeftTensorIso M P Y).hom ≫ h) ≫ f
  exact (Category.assoc _ _ _).symm

omit [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
/-- The actual free left action moves the original coefficient past the monoid once. -/
theorem freeObject_leftAction (Q : C) :
    leftAction M (freeObject M Q) =
      (α_ M Q M).inv ≫ ((β_ M Q).hom ▷ M) ≫
        (α_ Q M M).hom ≫ (Q ◁ μ[M]) := by
  change (β_ M (Q ⊗ M)).hom ≫ (α_ Q M M).hom ≫ (Q ◁ μ[M]) =
    (α_ M Q M).inv ≫ ((β_ M Q).hom ▷ M) ≫
      (α_ Q M M).hom ≫ (Q ◁ μ[M])
  rw [BraidedCategory.braiding_tensor_right_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← whiskerLeft_comp, IsCommMonObj.mul_comm]

/-- The two-free comparison is the actual one-free comparison followed by the associator. -/
def freeTensorIso (P Q : C) :
    freeObject M P ⊗ freeObject M Q ≅ freeObject M (P ⊗ Q) :=
  freeLeftTensorIso M P (freeObject M Q) ≪≫ coefficientFreeIso M P Q

/-- The entire forward two-free map has the actual contraction and inverse associator value. -/
@[reassoc]
theorem freeTensorIso_hom_π_coefficient (P Q : C) :
    relativeTensorπ M (freeObject M P) (freeObject M Q) ≫
        (freeTensorIso M P Q).hom.hom =
      freeLeftTensorCoefficient M P (freeObject M Q) ≫ (α_ P Q M).inv := by
  simp only [freeTensorIso, Iso.trans_hom, Mod.comp_hom', coefficientFreeIso_hom]
  erw [← Category.assoc, freeLeftTensorIso_hom_π]
  rfl

/-- The complete original two-free forward equation at the original coefficient and quotient. -/
def FreeTensorHomFormula (P Q : C) : Prop :=
  relativeTensorπ M (freeObject M P) (freeObject M Q) ≫
      (freeTensorIso M P Q).hom.hom =
    tensorμ P M Q M ≫ ((P ⊗ Q) ◁ μ[M])

/-- The entire forward two-free map multiplies the two actual monoid factors. -/
@[reassoc]
theorem freeTensorIso_hom_π (P Q : C) :
    FreeTensorHomFormula M P Q := by
  change relativeTensorπ M (freeObject M P) (freeObject M Q) ≫
      (freeTensorIso M P Q).hom.hom =
    tensorμ P M Q M ≫ ((P ⊗ Q) ◁ μ[M])
  have h : freeLeftTensorCoefficient M P (freeObject M Q) ≫ (α_ P Q M).inv =
      tensorμ P M Q M ≫ ((P ⊗ Q) ◁ μ[M]) := by
    let θ : M ⊗ (Q ⊗ M) ⟶ Q ⊗ M := leftAction M (freeObject M Q)
    have hθ : θ = (α_ M Q M).inv ≫ ((β_ M Q).hom ▷ M) ≫
        (α_ Q M M).hom ≫ (Q ◁ μ[M]) := freeObject_leftAction M Q
    change ((α_ P M (Q ⊗ M)).hom ≫ (P ◁ θ)) ≫ (α_ P Q M).inv = _
    rw [hθ]
    simp only [whiskerLeft_comp, Category.assoc]
    rw [associator_inv_naturality_right]
    unfold tensorμ
    simp only [Category.assoc]
  exact (freeTensorIso_hom_π_coefficient M P Q).trans h

/-- The complete original two-free inverse equation retains its entire generator and quotient. -/
def FreeTensorInvFormula (P Q : C) : Prop :=
  (freeTensorIso M P Q).inv.hom =
    (α_ P Q M).hom ≫ (freeGenerator M P ▷ (Q ⊗ M)) ≫
      relativeTensorπ M (freeObject M P) (freeObject M Q)

/-- The entire two-free inverse is the original first-factor generator and quotient. -/
@[simp]
theorem freeTensorIso_inv (P Q : C) :
    FreeTensorInvFormula M P Q := by
  change (freeTensorIso M P Q).inv.hom =
    (α_ P Q M).hom ≫ (freeGenerator M P ▷ (Q ⊗ M)) ≫
      relativeTensorπ M (freeObject M P) (freeObject M Q)
  simp only [freeTensorIso, Iso.trans_inv, Mod.comp_hom',
    coefficientFreeIso_inv, freeLeftTensorIso_inv]
  rfl

/-- The entire original pair of generators followed by the actual balanced projection. -/
def tensorFreeGenerator (P Q : C) :
    P ⊗ Q ⟶ (freeObject M P ⊗ freeObject M Q).X :=
  (freeGenerator M P ⊗ₘ freeGenerator M Q) ≫
    relativeTensorπ M (freeObject M P) (freeObject M Q)

/-- The actual inverse two-free comparison has the complete pair-generator characteristic. -/
@[reassoc]
theorem freeTensorIso_inv_generator (P Q : C) :
    freeGenerator M (P ⊗ Q) ≫ (freeTensorIso M P Q).inv.hom =
      tensorFreeGenerator M P Q := by
  let gp : P ⟶ P ⊗ M := freeGenerator M P
  let gq : Q ⟶ Q ⊗ M := freeGenerator M Q
  let gpq : P ⊗ Q ⟶ (P ⊗ Q) ⊗ M := freeGenerator M (P ⊗ Q)
  let p : (P ⊗ M) ⊗ (Q ⊗ M) ⟶ (freeObject M P ⊗ freeObject M Q).X :=
    relativeTensorπ M (freeObject M P) (freeObject M Q)
  have hg : gpq ≫ (α_ P Q M).hom = P ◁ gq := freeGenerator_associator M P Q
  erw [freeTensorIso_inv]
  change gpq ≫ (α_ P Q M).hom ≫ (gp ▷ (Q ⊗ M)) ≫ p = (gp ⊗ₘ gq) ≫ p
  rw [← Category.assoc, ← Category.assoc, hg, Category.assoc, ← tensorHom_def'_assoc]

/-- The actual two-free inverse is the entire free extension of its original generators. -/
theorem freeTensorIso_inv_extend (P Q : C) :
    (freeTensorIso M P Q).inv =
      extendFree M (P ⊗ Q) (freeObject M P ⊗ freeObject M Q)
        (tensorFreeGenerator M P Q) := by
  apply free_hom_ext M (P ⊗ Q) (freeObject M P ⊗ freeObject M Q)
  rw [freeTensorIso_inv_generator, freeGenerator_extend]

/-- The actual forward two-free comparison preserves the whole original generator. -/
@[reassoc]
theorem freeTensorIso_generator (P Q : C) :
    tensorFreeGenerator M P Q ≫ (freeTensorIso M P Q).hom.hom =
      freeGenerator M (P ⊗ Q) := by
  have hi : (freeTensorIso M P Q).inv.hom ≫ (freeTensorIso M P Q).hom.hom =
      𝟙 ((P ⊗ Q) ⊗ M) := congrArg Mod.Hom.hom (freeTensorIso M P Q).inv_hom_id
  erw [← freeTensorIso_inv_generator, Category.assoc, hi, Category.comp_id]

/-- The complete two-free equation for both original coefficient arrows. -/
def FreeTensorNaturalityFormula {P P' Q Q' : C} (f : P ⟶ P') (g : Q ⟶ Q') : Prop :=
  relativeTensorMap M (freeMap M f) (freeMap M g) ≫ (freeTensorIso M P' Q').hom =
    (freeTensorIso M P Q).hom ≫ freeMap M (f ⊗ₘ g)

/-- The entire two-free forward family is natural under both coefficient arrows. -/
@[reassoc]
theorem freeTensorIso_naturality {P P' Q Q' : C} (f : P ⟶ P') (g : Q ⟶ Q') :
    FreeTensorNaturalityFormula M f g := by
  change relativeTensorMap M (freeMap M f) (freeMap M g) ≫ (freeTensorIso M P' Q').hom =
    (freeTensorIso M P Q).hom ≫ freeMap M (f ⊗ₘ g)
  simp only [freeTensorIso, Iso.trans_hom]
  rw [← Category.assoc, freeLeftTensorIso_naturality M f (freeMap M g), Category.assoc,
    coefficientFreeIso_naturality M f g]
  rw [Category.assoc]

/-- The entire two-free inverse family is natural under both coefficient arrows. -/
@[reassoc]
theorem freeTensorIso_inv_naturality {P P' Q Q' : C} (f : P ⟶ P') (g : Q ⟶ Q') :
    freeMap M (f ⊗ₘ g) ≫ (freeTensorIso M P' Q').inv =
      (freeTensorIso M P Q).inv ≫ relativeTensorMap M (freeMap M f) (freeMap M g) := by
  apply (cancel_mono (freeTensorIso M P' Q').hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [freeTensorIso_naturality M f g]
  simp only [Iso.inv_hom_id_assoc]

/-- The complete original pair generator is natural under both coefficient arrows. -/
@[reassoc]
theorem tensorFreeGenerator_naturality {P P' Q Q' : C}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    (f ⊗ₘ g) ≫ tensorFreeGenerator M P' Q' =
      tensorFreeGenerator M P Q ≫
        (relativeTensorMap M (freeMap M f) (freeMap M g)).hom := by
  let gp : P ⟶ P ⊗ M := freeGenerator M P
  let gq : Q ⟶ Q ⊗ M := freeGenerator M Q
  let gp' : P' ⟶ P' ⊗ M := freeGenerator M P'
  let gq' : Q' ⟶ Q' ⊗ M := freeGenerator M Q'
  let p : (P ⊗ M) ⊗ (Q ⊗ M) ⟶ (freeObject M P ⊗ freeObject M Q).X :=
    relativeTensorπ M (freeObject M P) (freeObject M Q)
  let p' : (P' ⊗ M) ⊗ (Q' ⊗ M) ⟶ (freeObject M P' ⊗ freeObject M Q').X :=
    relativeTensorπ M (freeObject M P') (freeObject M Q')
  have hp : p ≫ (relativeTensorMap M (freeMap M f) (freeMap M g)).hom =
      ((f ▷ M) ⊗ₘ (g ▷ M)) ≫ p' := relativeTensorMap_π M (freeMap M f) (freeMap M g)
  have hgp : gp ≫ (f ▷ M) = f ≫ gp' := freeGenerator_naturality M f
  have hgq : gq ≫ (g ▷ M) = g ≫ gq' := freeGenerator_naturality M g
  change (f ⊗ₘ g) ≫ ((gp' ⊗ₘ gq') ≫ p') =
    ((gp ⊗ₘ gq) ≫ p) ≫ (relativeTensorMap M (freeMap M f) (freeMap M g)).hom
  symm
  calc
    _ = (gp ⊗ₘ gq) ≫ ((f ▷ M) ⊗ₘ (g ▷ M)) ≫ p' := by rw [Category.assoc, hp]
    _ = ((gp ≫ (f ▷ M)) ⊗ₘ (gq ≫ (g ▷ M))) ≫ p' := by
      rw [← Category.assoc, tensorHom_comp_tensorHom]
    _ = ((f ≫ gp') ⊗ₘ (g ≫ gq')) ≫ p' := by rw [hgp, hgq]
    _ = (f ⊗ₘ g) ≫ ((gp' ⊗ₘ gq') ≫ p') := by
      rw [← tensorHom_comp_tensorHom, Category.assoc]

/-- The full two-free source is a functor on both original coefficient objects. -/
def freeTensorPairFunctor : C × C ⥤ RightModule M where
  obj P := freeObject M P.1 ⊗ freeObject M P.2
  map f := relativeTensorMap M (freeMap M f.1) (freeMap M f.2)
  map_id P := by
    change (functor M).map (𝟙 P.1) ⊗ₘ (functor M).map (𝟙 P.2) = 𝟙 _
    rw [Functor.map_id, Functor.map_id, id_tensorHom_id]
  map_comp f g := by
    change relativeTensorMap M (freeMap M (f.1 ≫ g.1))
      (freeMap M (f.2 ≫ g.2)) = _
    rw [freeMap_comp, freeMap_comp, relativeTensorMap_comp]

/-- The full free-on-tensor target is a functor on both original coefficients. -/
def tensorFreePairFunctor : C × C ⥤ RightModule M where
  obj P := freeObject M (P.1 ⊗ P.2)
  map f := freeMap M (f.1 ⊗ₘ f.2)
  map_id P := by
    change (functor M).map ((𝟙 P.1) ⊗ₘ (𝟙 P.2)) = 𝟙 _
    rw [id_tensorHom_id, Functor.map_id]
  map_comp f g := by
    change freeMap M ((f.1 ≫ g.1) ⊗ₘ (f.2 ≫ g.2)) = _
    rw [← tensorHom_comp_tensorHom, freeMap_comp]

/-- The complete two-free family is an actual natural isomorphism of both-input functors. -/
def freeTensorNatIso : freeTensorPairFunctor M ≅ tensorFreePairFunctor M :=
  NatIso.ofComponents (fun P => freeTensorIso M P.1 P.2)
    (by intro P Q f; exact freeTensorIso_naturality M f.1 f.2)

/-- The full two-free Hom equivalence uses the original generator pair and actual extension. -/
def freeTensorHomEquiv (P Q : C) (Z : RightModule M) :
    (freeObject M P ⊗ freeObject M Q ⟶ Z) ≃ (P ⊗ Q ⟶ Z.X) where
  toFun f := tensorFreeGenerator M P Q ≫ f.hom
  invFun f := (freeTensorIso M P Q).hom ≫ extendFree M (P ⊗ Q) Z f
  left_inv f := by
    change (freeTensorIso M P Q).hom ≫
      extendFree M (P ⊗ Q) Z (tensorFreeGenerator M P Q ≫ f.hom) = f
    have hg : tensorFreeGenerator M P Q ≫ f.hom =
        freeGenerator M (P ⊗ Q) ≫ ((freeTensorIso M P Q).inv ≫ f).hom := by
      rw [Mod.comp_hom', ← Category.assoc, freeTensorIso_inv_generator]
    rw [hg, extendFree_generator, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  right_inv f := by
    change tensorFreeGenerator M P Q ≫
      ((freeTensorIso M P Q).hom ≫ extendFree M (P ⊗ Q) Z f).hom = f
    rw [Mod.comp_hom', ← Category.assoc, freeTensorIso_generator, freeGenerator_extend]

/-- The entire forward two-free Hom function is the original pair-generator restriction. -/
theorem freeTensorHomEquiv_toFun (P Q : C) (Z : RightModule M) :
    (freeTensorHomEquiv M P Q Z).toFun =
      (fun f => tensorFreeGenerator M P Q ≫ f.hom) := rfl

/-- The entire inverse two-free Hom function is the actual tensor isomorphism and extension. -/
theorem freeTensorHomEquiv_invFun (P Q : C) (Z : RightModule M) :
    (freeTensorHomEquiv M P Q Z).invFun =
      (fun f => (freeTensorIso M P Q).hom ≫ extendFree M (P ⊗ Q) Z f) := rfl

/-- Both complete source arrows are respected by the forward two-free Hom function. -/
theorem freeTensorHomEquiv_naturality_left {P P' Q Q' : C} (Z : RightModule M)
    (f : P' ⟶ P) (g : Q' ⟶ Q) (h : freeObject M P ⊗ freeObject M Q ⟶ Z) :
    freeTensorHomEquiv M P' Q' Z
        (relativeTensorMap M (freeMap M f) (freeMap M g) ≫ h) =
      (f ⊗ₘ g) ≫ freeTensorHomEquiv M P Q Z h := by
  change tensorFreeGenerator M P' Q' ≫
      (relativeTensorMap M (freeMap M f) (freeMap M g)).hom ≫ h.hom =
    (f ⊗ₘ g) ≫ tensorFreeGenerator M P Q ≫ h.hom
  rw [← tensorFreeGenerator_naturality_assoc M f g]

/-- Every complete target arrow is respected by the forward two-free Hom function. -/
theorem freeTensorHomEquiv_naturality_right (P Q : C) {Z Z' : RightModule M}
    (h : freeObject M P ⊗ freeObject M Q ⟶ Z) (f : Z ⟶ Z') :
    freeTensorHomEquiv M P Q Z' (h ≫ f) =
      freeTensorHomEquiv M P Q Z h ≫ f.hom := by
  change tensorFreeGenerator M P Q ≫ h.hom ≫ f.hom =
    (tensorFreeGenerator M P Q ≫ h.hom) ≫ f.hom
  exact (Category.assoc _ _ _).symm

/-- Both complete source arrows are respected by the inverse two-free Hom function. -/
theorem freeTensorHomEquiv_inv_naturality_left {P P' Q Q' : C} (Z : RightModule M)
    (f : P' ⟶ P) (g : Q' ⟶ Q) (h : P ⊗ Q ⟶ Z.X) :
    (freeTensorHomEquiv M P' Q' Z).symm ((f ⊗ₘ g) ≫ h) =
      relativeTensorMap M (freeMap M f) (freeMap M g) ≫
        (freeTensorHomEquiv M P Q Z).symm h := by
  have he :
      extendFree M (P' ⊗ Q') Z ((f ⊗ₘ g) ≫ h) =
        freeMap M (f ⊗ₘ g) ≫ extendFree M (P ⊗ Q) Z h :=
    freeHomEquiv_naturality_left M (f ⊗ₘ g) Z h
  change (freeTensorIso M P' Q').hom ≫ extendFree M (P' ⊗ Q') Z ((f ⊗ₘ g) ≫ h) =
    relativeTensorMap M (freeMap M f) (freeMap M g) ≫
      (freeTensorIso M P Q).hom ≫ extendFree M (P ⊗ Q) Z h
  rw [he]
  simpa only [Category.assoc] using
    congrArg (fun k => k ≫ extendFree M (P ⊗ Q) Z h)
      (freeTensorIso_naturality M f g).symm

/-- Every complete target arrow is respected by the inverse two-free Hom function. -/
theorem freeTensorHomEquiv_inv_naturality_right (P Q : C) {Z Z' : RightModule M}
    (h : P ⊗ Q ⟶ Z.X) (f : Z ⟶ Z') :
    (freeTensorHomEquiv M P Q Z').symm (h ≫ f.hom) =
      (freeTensorHomEquiv M P Q Z).symm h ≫ f := by
  change (freeTensorIso M P Q).hom ≫ extendFree M (P ⊗ Q) Z' (h ≫ f.hom) =
    ((freeTensorIso M P Q).hom ≫ extendFree M (P ⊗ Q) Z h) ≫ f
  rw [extendFree_naturality_right, Category.assoc]

/-- Whole maps from a tensor of two free modules are determined by the original generators. -/
theorem freeTensor_hom_ext (P Q : C) (Z : RightModule M)
    (f g : freeObject M P ⊗ freeObject M Q ⟶ Z)
    (h : tensorFreeGenerator M P Q ≫ f.hom = tensorFreeGenerator M P Q ≫ g.hom) :
    f = g :=
  (freeTensorHomEquiv M P Q Z).injective h

/-- The entire regular right module is the actual transported tensor unit. -/
def regularTensorUnitIso : regularObject M ≅ 𝟙_ (RightModule M) :=
  isoOfCarrier M (regularObject M) (𝟙_ (RightModule M)) (Iso.refl M) (by
    change μ[M] ≫ 𝟙 M = (𝟙 M ▷ M) ≫ (β_ M M).hom ≫ μ[M]
    simp only [Category.comp_id, id_whiskerRight, Category.id_comp]
    exact (IsCommMonObj.mul_comm M).symm)

/-- The complete regular-to-unit map has the original carrier identity. -/
@[simp]
theorem regularTensorUnitIso_hom : (regularTensorUnitIso M).hom.hom = 𝟙 M := rfl

/-- The complete unit-to-regular map has the original carrier identity. -/
@[simp]
theorem regularTensorUnitIso_inv : (regularTensorUnitIso M).inv.hom = 𝟙 M := rfl

/-- The actual free-unit comparison uses the proved regular-unit comparison. -/
def freeTensorUnitIso : freeObject M (𝟙_ C) ≅ 𝟙_ (RightModule M) :=
  freeUnitRegularIso M ≪≫ regularTensorUnitIso M

/-- The entire free-unit forward carrier arrow is the actual left unitor. -/
theorem freeTensorUnitIso_hom : (freeTensorUnitIso M).hom.hom = (λ_ M).hom := by
  change (λ_ M).hom ≫ 𝟙 M = (λ_ M).hom
  exact Category.comp_id _

/-- The entire free-unit inverse carrier arrow is the actual inverse left unitor. -/
theorem freeTensorUnitIso_inv : (freeTensorUnitIso M).inv.hom = (λ_ M).inv := by
  change 𝟙 M ≫ (λ_ M).inv = (λ_ M).inv
  exact Category.id_comp _

/-- The whole original free-unit generator has the actual monoid-unit characteristic. -/
@[reassoc]
theorem freeTensorUnitIso_generator :
    freeGenerator M (𝟙_ C) ≫ (freeTensorUnitIso M).hom.hom = η[M] := by
  rw [freeTensorUnitIso_hom]
  exact freeUnitRegularIso_generator M

/-- The actual two-free generator characteristic stated with both original generators. -/
@[reassoc]
theorem freeTensorIso_generator_π (P Q : C) :
    (freeGenerator M P ⊗ₘ freeGenerator M Q) ≫
        relativeTensorπ M (freeObject M P) (freeObject M Q) ≫
          (freeTensorIso M P Q).hom.hom = freeGenerator M (P ⊗ Q) := by
  simpa only [tensorFreeGenerator, Category.assoc] using freeTensorIso_generator M P Q

/-- The actual nested two-free isomorphisms identify the full triple-free source. -/
def freeTripleIso (P Q R : C) :
    (freeObject M P ⊗ freeObject M Q) ⊗ freeObject M R ≅
      freeObject M ((P ⊗ Q) ⊗ R) :=
  whiskerRightIso (freeTensorIso M P Q) (freeObject M R) ≪≫
    freeTensorIso M (P ⊗ Q) R

/-- The original three generators enter the actual two nested balanced quotients. -/
def tripleFreeGenerator (P Q R : C) :
    (P ⊗ Q) ⊗ R ⟶ ((freeObject M P ⊗ freeObject M Q) ⊗ freeObject M R).X :=
  ((freeGenerator M P ⊗ₘ freeGenerator M Q) ⊗ₘ freeGenerator M R) ≫
    (relativeTensorπ M (freeObject M P) (freeObject M Q) ▷ (freeObject M R).X) ≫
      relativeTensorπ M (freeObject M P ⊗ freeObject M Q) (freeObject M R)

/-- The nested actual two-free comparisons preserve the whole triple generator. -/
@[reassoc]
theorem tripleFreeGenerator_iso (P Q R : C) :
    tripleFreeGenerator M P Q R ≫ (freeTripleIso M P Q R).hom.hom =
      freeGenerator M ((P ⊗ Q) ⊗ R) := by
  have hg :
      ((freeGenerator M P ⊗ₘ freeGenerator M Q) ⊗ₘ freeGenerator M R) ≫
          (relativeTensorπ M (freeObject M P) (freeObject M Q) ▷ (freeObject M R).X) ≫
            ((freeTensorIso M P Q).hom.hom ▷ (freeObject M R).X) =
        freeGenerator M (P ⊗ Q) ⊗ₘ freeGenerator M R := by
    erw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
      Category.comp_id, tensorHom_comp_tensorHom, Category.comp_id]
    simpa only [Category.assoc] using
      congrArg (fun f => f ⊗ₘ freeGenerator M R) (freeTensorIso_generator_π M P Q)
  change (((freeGenerator M P ⊗ₘ freeGenerator M Q) ⊗ₘ freeGenerator M R) ≫
      (relativeTensorπ M (freeObject M P) (freeObject M Q) ▷ (freeObject M R).X) ≫
        relativeTensorπ M (freeObject M P ⊗ freeObject M Q) (freeObject M R)) ≫
          (((freeTensorIso M P Q).hom ▷ freeObject M R).hom ≫
            (freeTensorIso M (P ⊗ Q) R).hom.hom) = _
  erw [Category.assoc, Category.assoc, relativeTensorWhiskerRight_π_assoc, reassoc_of% hg]
  exact freeTensorIso_generator_π M (P ⊗ Q) R

/-- The actual inverse triple-free isomorphism retains the entire original generator. -/
@[reassoc]
theorem freeTripleIso_inv_generator (P Q R : C) :
    freeGenerator M ((P ⊗ Q) ⊗ R) ≫ (freeTripleIso M P Q R).inv.hom =
      tripleFreeGenerator M P Q R := by
  have hi : (freeTripleIso M P Q R).hom.hom ≫ (freeTripleIso M P Q R).inv.hom =
      𝟙 (((freeObject M P ⊗ freeObject M Q) ⊗ freeObject M R).X) :=
    congrArg Mod.Hom.hom (freeTripleIso M P Q R).hom_inv_id
  rw [← tripleFreeGenerator_iso, Category.assoc, hi, Category.comp_id]

/-- Whole triple-free module arrows are determined by their original three generators. -/
theorem freeTriple_hom_ext (P Q R : C) (Z : RightModule M)
    (f g : (freeObject M P ⊗ freeObject M Q) ⊗ freeObject M R ⟶ Z)
    (h : tripleFreeGenerator M P Q R ≫ f.hom = tripleFreeGenerator M P Q R ≫ g.hom) :
    f = g := by
  apply (cancel_epi (freeTripleIso M P Q R).inv).1
  apply free_hom_ext M ((P ⊗ Q) ⊗ R) Z
  change freeGenerator M ((P ⊗ Q) ⊗ R) ≫ (freeTripleIso M P Q R).inv.hom ≫ f.hom =
    freeGenerator M ((P ⊗ Q) ⊗ R) ≫ (freeTripleIso M P Q R).inv.hom ≫ g.hom
  simpa only [← Category.assoc, freeTripleIso_inv_generator] using h

/-- The actual associator and second pair contraction have the full triple characteristic. -/
theorem tripleFreeGenerator_right_path (P Q R : C) :
    tripleFreeGenerator M P Q R ≫
        (α_ (freeObject M P) (freeObject M Q) (freeObject M R)).hom.hom ≫
          (freeObject M P ◁ (freeTensorIso M Q R).hom).hom ≫
            (freeTensorIso M P (Q ⊗ R)).hom.hom =
      (α_ P Q R).hom ≫ freeGenerator M (P ⊗ (Q ⊗ R)) := by
  have hr :
      (freeGenerator M Q ⊗ₘ freeGenerator M R) ≫
          (relativeTensorπ M (freeObject M Q) (freeObject M R) ≫
            (freeTensorIso M Q R).hom.hom) = freeGenerator M (Q ⊗ R) := by
    simpa only [Category.assoc] using freeTensorIso_generator_π M Q R
  dsimp only [tripleFreeGenerator]
  erw [Category.assoc, Category.assoc,
    relativeTensorAssociator_hom_π_assoc M (freeObject M P) (freeObject M Q) (freeObject M R),
    associator_naturality_assoc,
    relativeTensorWhiskerLeft_π_assoc, ← whiskerLeft_comp_assoc]
  erw [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.comp_id, hr]
  erw [freeTensorIso_generator_π]

/-- The complete free tensorator obeys the actual ambient and quotient associators. -/
theorem freeTensor_associativity (P Q R : C) :
    (freeTensorIso M P Q).hom ▷ freeObject M R ≫
        (freeTensorIso M (P ⊗ Q) R).hom ≫ freeMap M (α_ P Q R).hom =
      (α_ (freeObject M P) (freeObject M Q) (freeObject M R)).hom ≫
        freeObject M P ◁ (freeTensorIso M Q R).hom ≫
          (freeTensorIso M P (Q ⊗ R)).hom := by
  apply freeTriple_hom_ext M P Q R (freeObject M (P ⊗ (Q ⊗ R)))
  let gSrc : (P ⊗ Q) ⊗ R ⟶ ((P ⊗ Q) ⊗ R) ⊗ M :=
    freeGenerator M ((P ⊗ Q) ⊗ R)
  let gTgt : P ⊗ (Q ⊗ R) ⟶ (P ⊗ (Q ⊗ R)) ⊗ M :=
    freeGenerator M (P ⊗ (Q ⊗ R))
  let a : ((P ⊗ Q) ⊗ R) ⊗ M ⟶ (P ⊗ (Q ⊗ R)) ⊗ M := (α_ P Q R).hom ▷ M
  have hn : gSrc ≫ a = (α_ P Q R).hom ≫ gTgt :=
    freeGenerator_naturality M (α_ P Q R).hom
  let r : (P ⊗ Q) ⊗ R ⟶ (P ⊗ (Q ⊗ R)) ⊗ M :=
    tripleFreeGenerator M P Q R ≫
      (α_ (freeObject M P) (freeObject M Q) (freeObject M R)).hom.hom ≫
        (freeObject M P ◁ (freeTensorIso M Q R).hom).hom ≫
          (freeTensorIso M P (Q ⊗ R)).hom.hom
  have hr : (α_ P Q R).hom ≫ gTgt = r := (tripleFreeGenerator_right_path M P Q R).symm
  change _ = r
  calc
    _ = (tripleFreeGenerator M P Q R ≫ (freeTripleIso M P Q R).hom.hom) ≫
        a := by
      change tripleFreeGenerator M P Q R ≫
          (((freeTensorIso M P Q).hom ▷ freeObject M R).hom ≫
            (freeTensorIso M (P ⊗ Q) R).hom.hom ≫ a) = _
      exact (congrArg (fun k => tripleFreeGenerator M P Q R ≫ k)
        (Category.assoc
          ((freeTensorIso M P Q).hom ▷ freeObject M R).hom
          (freeTensorIso M (P ⊗ Q) R).hom.hom
          a).symm).trans
        (Category.assoc (tripleFreeGenerator M P Q R)
          (((freeTensorIso M P Q).hom ▷ freeObject M R).hom ≫
            (freeTensorIso M (P ⊗ Q) R).hom.hom)
          a).symm
    _ = gSrc ≫ a := by
      erw [tripleFreeGenerator_iso]
      rfl
    _ = (α_ P Q R).hom ≫ gTgt :=
      hn
    _ = r := hr

/-- The actual free unit and tensorator obey the entire left-unit equation. -/
theorem freeTensor_left_unitality (P : C) :
    (λ_ (freeObject M P)).hom =
      (freeTensorUnitIso M).inv ▷ freeObject M P ≫
        (freeTensorIso M (𝟙_ C) P).hom ≫ freeMap M (λ_ P).hom := by
  apply (cancel_epi ((freeTensorUnitIso M).hom ▷ freeObject M P)).1
  simp only [← comp_whiskerRight_assoc, Iso.hom_inv_id,
    id_whiskerRight, Category.id_comp]
  apply freeTensor_hom_ext M (𝟙_ C) P (freeObject M P)
  change tensorFreeGenerator M (𝟙_ C) P ≫
      ((freeTensorUnitIso M).hom ▷ freeObject M P).hom ≫ (λ_ (freeObject M P)).hom.hom =
    tensorFreeGenerator M (𝟙_ C) P ≫ (freeTensorIso M (𝟙_ C) P).hom.hom ≫
      ((λ_ P).hom ▷ M)
  erw [freeTensorIso_generator_assoc, freeGenerator_naturality]
  erw [tensorFreeGenerator]
  erw [Category.assoc, relativeTensorWhiskerRight_π_assoc,
    relativeTensorLeftUnitor_hom_π]
  erw [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.comp_id,
    freeTensorUnitIso_generator]
  change (η[M] ⊗ₘ freeGenerator M P) ≫ leftAction M (freeObject M P) =
    (λ_ P).hom ≫ freeGenerator M P
  erw [tensorHom_def', Category.assoc, leftAction_one, leftUnitor_naturality]

/-- The actual free unit and tensorator obey the entire right-unit equation. -/
theorem freeTensor_right_unitality (P : C) :
    (ρ_ (freeObject M P)).hom =
      freeObject M P ◁ (freeTensorUnitIso M).inv ≫
        (freeTensorIso M P (𝟙_ C)).hom ≫ freeMap M (ρ_ P).hom := by
  apply (cancel_epi (freeObject M P ◁ (freeTensorUnitIso M).hom)).1
  simp only [← whiskerLeft_comp_assoc, Iso.hom_inv_id,
    whiskerLeft_id, Category.id_comp]
  apply freeTensor_hom_ext M P (𝟙_ C) (freeObject M P)
  change tensorFreeGenerator M P (𝟙_ C) ≫
      (freeObject M P ◁ (freeTensorUnitIso M).hom).hom ≫ (ρ_ (freeObject M P)).hom.hom =
    tensorFreeGenerator M P (𝟙_ C) ≫ (freeTensorIso M P (𝟙_ C)).hom.hom ≫
      ((ρ_ P).hom ▷ M)
  erw [freeTensorIso_generator_assoc, freeGenerator_naturality]
  erw [tensorFreeGenerator]
  erw [Category.assoc, relativeTensorWhiskerLeft_π_assoc,
    relativeTensorRightUnitor_hom_π]
  erw [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.comp_id,
    freeTensorUnitIso_generator]
  change (freeGenerator M P ⊗ₘ η[M]) ≫ (freeObject M P).action =
    (ρ_ P).hom ≫ freeGenerator M P
  erw [tensorHom_def, Category.assoc, (freeObject M P).one_action, rightUnitor_naturality]

/-- The whole free functor is monoidal through the actual proved unit and tensor isomorphisms. -/
def freeTensorCoreMonoidal : (functor M).CoreMonoidal where
  εIso := (freeTensorUnitIso M).symm
  μIso := freeTensorIso M
  μIso_hom_natural_left f Q := by
    change freeMap M f ▷ freeObject M Q ≫ (freeTensorIso M _ Q).hom =
      (freeTensorIso M _ Q).hom ≫ freeMap M (f ▷ Q)
    simpa only [relativeTensorMap, freeMap_id, tensorHom_id] using
      (show relativeTensorMap M (freeMap M f) (freeMap M (𝟙 Q)) ≫
          (freeTensorIso M _ Q).hom =
        (freeTensorIso M _ Q).hom ≫ freeMap M (f ⊗ₘ 𝟙 Q) from
        freeTensorIso_naturality M f (𝟙 Q))
  μIso_hom_natural_right P f := by
    change freeObject M P ◁ freeMap M f ≫ (freeTensorIso M P _).hom =
      (freeTensorIso M P _).hom ≫ freeMap M (P ◁ f)
    simpa only [relativeTensorMap, freeMap_id, id_tensorHom] using
      (show relativeTensorMap M (freeMap M (𝟙 P)) (freeMap M f) ≫
          (freeTensorIso M P _).hom =
        (freeTensorIso M P _).hom ≫ freeMap M (𝟙 P ⊗ₘ f) from
        freeTensorIso_naturality M (𝟙 P) f)
  associativity := freeTensor_associativity M
  left_unitality := freeTensor_left_unitality M
  right_unitality := freeTensor_right_unitality M

/-- The actual proved CoreMonoidal data gives the complete free functor structure. -/
@[instance_reducible]
def freeTensorMonoidal : (functor M).Monoidal :=
  (freeTensorCoreMonoidal M).toMonoidal

/-- The complete literal free tensorator equation under the original whole monoidal data. -/
def FreeTensoratorFormula (P Q : C) : Prop :=
  letI := freeTensorMonoidal M
  Functor.LaxMonoidal.μ (functor M) P Q = (freeTensorIso M P Q).hom

/-- The original entire free tensorator is the hom of its original complete two-free Iso. -/
theorem freeTensorator (P Q : C) : FreeTensoratorFormula M P Q := rfl

/-- The whole free tensorator respects the actual ambient and quotient braidings. -/
theorem freeTensor_braiding (P Q : C) :
    (β_ (freeObject M P) (freeObject M Q)).hom ≫ (freeTensorIso M Q P).hom =
      (freeTensorIso M P Q).hom ≫ freeMap M (β_ P Q).hom := by
  apply freeTensor_hom_ext M P Q (freeObject M (Q ⊗ P))
  change tensorFreeGenerator M P Q ≫ (β_ (freeObject M P) (freeObject M Q)).hom.hom ≫
      (freeTensorIso M Q P).hom.hom =
    tensorFreeGenerator M P Q ≫ (freeTensorIso M P Q).hom.hom ≫ ((β_ P Q).hom ▷ M)
  erw [freeTensorIso_generator_assoc, freeGenerator_naturality]
  erw [tensorFreeGenerator]
  erw [Category.assoc, relativeTensorBraiding_hom_π_assoc,
    BraidedCategory.braiding_naturality_assoc, freeTensorIso_generator_π]

/-- The complete free functor respects the braiding with the proved monoidal data. -/
@[instance_reducible]
def freeTensorBraided : (functor M).Braided where
  toMonoidal := freeTensorMonoidal M
  braided P Q := by
    change (freeTensorIso M P Q).hom ≫ freeMap M (β_ P Q).hom =
      (β_ (freeObject M P) (freeObject M Q)).hom ≫ (freeTensorIso M Q P).hom
    exact (freeTensor_braiding M P Q).symm

end Symmetric
end CategoryTheory.RightModuleFree
