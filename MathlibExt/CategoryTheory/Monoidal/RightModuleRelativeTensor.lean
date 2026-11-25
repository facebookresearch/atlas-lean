/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Monoidal.RightModuleEquivalenceFunctions
public import MathlibExt.CategoryTheory.Monoidal.Mod.RelativeTensor
public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.CategoryTheory.Monoidal.Braided.Transport

/-!
# Relative tensor and whole quotient functions on the stock right-module category

The tensor is the existing Mod.relativeTensor transported once through the
original CommutativeModuleConversion.moduleEquivalence. Its carrier, projection,
action, descended maps, and both whole Hom functions use the same selected
coequalizer. The conversion comparisons retain the original unit and counit.
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

section Braided

variable [BraidedCategory C]

/-- Every original right-module arrow preserves its converted left action. -/
@[reassoc]
theorem leftAction_hom {X Y : RightModule M} (f : X ⟶ Y) :
    leftAction M X ≫ f.hom = (M ◁ f.hom) ≫ leftAction M Y := by
  change ((β_ M X.X).hom ≫ X.action) ≫ f.hom =
    (M ◁ f.hom) ≫ (β_ M Y.X).hom ≫ Y.action
  rw [Category.assoc, CommutativeModuleConversion.RightModule.comm f,
    BraidedCategory.braiding_naturality_right_assoc]

end Braided

section Symmetric

variable [SymmetricCategory C] [IsCommMonObj M]

/-- The original monoid and commutativity instance give the actual commutative monoid. -/
abbrev scalarCommMon : CommMon C := { X := M }

/-- The actual left module obtained from every complete right action. -/
abbrev leftModule (X : RightModule M) : Mod C M :=
  CommutativeModuleConversion.toLeft M X

/-- The actual converted module retains the complete original object. -/
@[simp]
theorem leftModule_X (X : RightModule M) : (leftModule M X).X = X.X := rfl

/-- The converted left module has exactly the positive-braiding left action. -/
theorem leftModule_smul (X : RightModule M) :
    (leftModule M X).mod.smul = leftAction M X := rfl

/-- The two actual braidings recover the original entire right action. -/
theorem leftModule_braidedRightAction (X : RightModule M) :
    Mod.braidedRightAction (scalarCommMon M) (leftModule M X) = X.action := by
  change (β_ X.X M).hom ≫ (β_ M X.X).hom ≫ X.action = X.action
  rw [SymmetricCategory.symmetry_assoc]

/-- The actual left and right actions commute on every complete right module. -/
@[reassoc]
theorem leftAction_comm (X : RightModule M) :
    (leftAction M X ▷ M) ≫ X.action =
      (α_ M X.X M).hom ≫ (M ◁ X.action) ≫ leftAction M X := by
  have h := Mod.smul_braidedRightAction (scalarCommMon M) (leftModule M X)
  rw [leftModule_braidedRightAction] at h
  exact h

/-- A full balanced arrow that is right-linear in the actual second-factor action. -/
structure BalancedRightLinearMap (X Y Z : RightModule M) where
  /-- The underlying map `X.X ⊗ Y.X ⟶ Z.X` of carriers. -/
  hom : X.X ⊗ Y.X ⟶ Z.X
  balanced : (X.action ▷ Y.X) ≫ hom =
    (α_ X.X M Y.X).hom ≫ (X.X ◁ leftAction M Y) ≫ hom
  right_linear :
    (α_ X.X Y.X M).hom ≫ (X.X ◁ Y.action) ≫ hom =
      (hom ▷ M) ≫ Z.action

namespace BalancedRightLinearMap

variable {M}

omit [IsCommMonObj M] in
/-- Equality of entire underlying arrows identifies balanced right-linear maps. -/
@[ext]
theorem ext {X Y Z : RightModule M}
    {f g : BalancedRightLinearMap M X Y Z} (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

end BalancedRightLinearMap

section Tensor

variable [HasCoequalizers C]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The stock right-module tensor is the single transport of the existing relative tensor. -/
@[instance_reducible]
def tensorMonoidal : MonoidalCategory (RightModule M) := by
  letI : MonoidalCategory (Mod C M) := Mod.instMonoidalCategory (scalarCommMon M)
  exact Monoidal.transport (CommutativeModuleConversion.moduleEquivalence M)

/-- Its symmetry is the original relative symmetry under the same conversion. -/
@[instance_reducible]
def tensorSymmetric : @SymmetricCategory (RightModule M) _ (tensorMonoidal M) := by
  letI : MonoidalCategory (Mod C M) := Mod.instMonoidalCategory (scalarCommMon M)
  letI : SymmetricCategory (Mod C M) := Mod.instSymmetricCategory (scalarCommMon M)
  exact Monoidal.Transported.instSymmetricCategory
    (CommutativeModuleConversion.moduleEquivalence M)

/-- The transported tensor product `tensorMonoidal M` on right modules, as a local instance. -/
local instance : MonoidalCategory (RightModule M) := tensorMonoidal M
/-- The transported symmetric structure `tensorSymmetric M` on right modules, as a local
instance. -/
local instance : SymmetricCategory (RightModule M) := tensorSymmetric M

/-- The selected tensor object belongs to the original stock module category. -/
abbrev tensorObject (X Y : RightModule M) : RightModule M := X ⊗ Y

/-- The whole tensor object is the original conversion of the selected left relative tensor. -/
theorem tensorObject_eq (X Y : RightModule M) :
    tensorObject M X Y = CommutativeModuleConversion.toRight M
      (((Mod.relativeTensor (scalarCommMon M)).obj (leftModule M X)).obj
        (leftModule M Y)) := rfl

/-- The whole tensor unit is the original conversion of the regular left module. -/
theorem tensorUnit_eq : (𝟙_ (RightModule M)) =
    CommutativeModuleConversion.toRight M (Mod.regular M) := rfl

/-- The whole tensor-map function uses both original conversion maps. -/
theorem tensorHom_eq {X X' Y Y' : RightModule M} (f : X ⟶ X') (g : Y ⟶ Y') :
    f ⊗ₘ g = CommutativeModuleConversion.toRightMap M
      (Mod.relativeTensorMap (scalarCommMon M)
        (CommutativeModuleConversion.toLeftMap M f)
        (CommutativeModuleConversion.toLeftMap M g)) := rfl

/-- The original balancing projection into the actual complete tensor object. -/
def relativeTensorπ (X Y : RightModule M) :
    X.X ⊗ Y.X ⟶
      (@MonoidalCategoryStruct.tensorObj (RightModule M) _
        (tensorMonoidal M).toMonoidalCategoryStruct X Y).X :=
  Mod.relativeTensorπ (scalarCommMon M) (leftModule M X) (leftModule M Y)

/-- The first actual balancing arrow. -/
def balanceFirst (X Y : RightModule M) :
    (X.X ⊗ M) ⊗ Y.X ⟶ X.X ⊗ Y.X :=
  X.action ▷ Y.X

/-- The second actual balancing arrow. -/
def balanceSecond (X Y : RightModule M) :
    (X.X ⊗ M) ⊗ Y.X ⟶ X.X ⊗ Y.X :=
  (α_ X.X M Y.X).hom ≫ (X.X ◁ leftAction M Y)

/-- The actual projection balances the entire original two action arrows. -/
@[reassoc]
theorem relativeTensorπ_balance (X Y : RightModule M) :
    (X.action ▷ Y.X) ≫ relativeTensorπ M X Y =
      (α_ X.X M Y.X).hom ≫ (X.X ◁ leftAction M Y) ≫ relativeTensorπ M X Y := by
  have h := Mod.relativeTensorπ_balance_rightAction
    (scalarCommMon M) (leftModule M X) (leftModule M Y)
  rw [leftModule_braidedRightAction] at h
  exact h

/-- The actual complete quotient has the second factor's original right action. -/
@[reassoc]
theorem relativeTensorπ_action (X Y : RightModule M) :
    (relativeTensorπ M X Y ▷ M) ≫ (X ⊗ Y).action =
      (α_ X.X Y.X M).hom ≫ (X.X ◁ Y.action) ≫ relativeTensorπ M X Y := by
  have h := Mod.relativeTensorπ_rightAction
    (scalarCommMon M) (leftModule M X) (leftModule M Y)
  rw [leftModule_braidedRightAction] at h
  exact h

/-- The actual complete projection is epi. -/
theorem relativeTensorπ_epi (X Y : RightModule M) : Epi (relativeTensorπ M X Y) :=
  Mod.relativeTensorπ_epi (scalarCommMon M) (leftModule M X) (leftModule M Y)

/-- Right tensoring preserves this actual projection by the stated size-colimit preservation. -/
theorem relativeTensorπ_whiskerRight_epi (X Y : RightModule M) (Z : C) :
    Epi (relativeTensorπ M X Y ▷ Z) :=
  Mod.relativeTensorπ_whiskerRight_epi
    (scalarCommMon M) (leftModule M X) (leftModule M Y) Z

/-- Left tensoring preserves this actual projection by the stated size-colimit preservation. -/
theorem relativeTensorπ_whiskerLeft_epi (X Y : RightModule M) (Z : C) :
    Epi (Z ◁ relativeTensorπ M X Y) :=
  Mod.relativeTensorπ_whiskerLeft_epi
    (scalarCommMon M) (leftModule M X) (leftModule M Y) Z

/-- Two actual right tensor functors preserve the same projection. -/
theorem relativeTensorπ_whiskerRight_whiskerRight_epi
    (X Y : RightModule M) (Z W : C) :
    Epi ((relativeTensorπ M X Y ▷ Z) ▷ W) :=
  Mod.relativeTensorπ_whiskerRight_whiskerRight_epi
    (scalarCommMon M) (leftModule M X) (leftModule M Y) Z W

/-- The quotient carrier is identified with the coequalizer of the original right actions. -/
theorem relativeTensor_carrier (X Y : RightModule M) :
    (X ⊗ Y).X = coequalizer (balanceFirst M X Y) (balanceSecond M X Y) := by
  change coequalizer
      (Mod.braidedRightAction (scalarCommMon M) (leftModule M X) ▷ Y.X)
      ((α_ X.X M Y.X).hom ≫ (X.X ◁ leftAction M Y)) =
    coequalizer (X.action ▷ Y.X)
      ((α_ X.X M Y.X).hom ≫ (X.X ◁ leftAction M Y))
  rw [leftModule_braidedRightAction]

/-- Descend an entire balanced carrier arrow through the actual chosen quotient. -/
def relativeTensorCarrierDesc (X Y : RightModule M) (Z : C)
    (f : X.X ⊗ Y.X ⟶ Z)
    (hbal : (X.action ▷ Y.X) ≫ f =
      (α_ X.X M Y.X).hom ≫ (X.X ◁ leftAction M Y) ≫ f) :
    (X ⊗ Y).X ⟶ Z := by
  change coequalizer
      (Mod.relativeTensorFirstMap (scalarCommMon M) (leftModule M X) (leftModule M Y))
      (Mod.relativeTensorSecondMap (scalarCommMon M) (leftModule M X) (leftModule M Y)) ⟶ Z
  exact coequalizer.desc f (by
    unfold Mod.relativeTensorFirstMap Mod.relativeTensorSecondMap
    change (Mod.braidedRightAction (scalarCommMon M) (leftModule M X) ▷ Y.X) ≫ f =
      ((α_ X.X M Y.X).hom ≫ (X.X ◁ (leftModule M Y).mod.smul)) ≫ f
    rw [leftModule_braidedRightAction, leftModule_smul]
    change (X.action ▷ Y.X) ≫ f =
      ((α_ X.X M Y.X).hom ≫ (X.X ◁ leftAction M Y)) ≫ f
    exact hbal.trans (Category.assoc _ _ _).symm)

/-- The entire carrier descent has its original projection value. -/
@[reassoc]
theorem relativeTensorCarrierDesc_π (X Y : RightModule M) (Z : C)
    (f : X.X ⊗ Y.X ⟶ Z)
    (hbal : (X.action ▷ Y.X) ≫ f =
      (α_ X.X M Y.X).hom ≫ (X.X ◁ leftAction M Y) ≫ f) :
    relativeTensorπ M X Y ≫ relativeTensorCarrierDesc M X Y Z f hbal = f := by
  unfold relativeTensorCarrierDesc relativeTensorπ
  exact coequalizer.π_desc _ _

/-- Entire carrier maps from this quotient agree when their projections agree. -/
theorem relativeTensorCarrier_hom_ext (X Y : RightModule M) (Z : C)
    (f g : (X ⊗ Y).X ⟶ Z)
    (h : relativeTensorπ M X Y ≫ f = relativeTensorπ M X Y ≫ g) : f = g := by
  let _ : Epi (relativeTensorπ M X Y) := relativeTensorπ_epi M X Y
  exact (cancel_epi (relativeTensorπ M X Y)).1 h

/-- The actual cofork for the complete original balancing arrows. -/
def relativeTensorCofork (X Y : RightModule M) :
    Cofork (balanceFirst M X Y) (balanceSecond M X Y) :=
  Cofork.ofπ (relativeTensorπ M X Y)
    (by simpa only [balanceFirst, balanceSecond, Category.assoc]
      using relativeTensorπ_balance M X Y)

/-- The original-action cofork is colimiting on the actual tensor carrier. -/
def relativeTensorCoforkIsColimit (X Y : RightModule M) :
    IsColimit (relativeTensorCofork M X Y) := by
  refine Cofork.IsColimit.mk (relativeTensorCofork M X Y)
    (fun s => relativeTensorCarrierDesc M X Y s.pt s.π
      (by simpa only [balanceFirst, balanceSecond, Category.assoc] using s.condition))
    (fun s => relativeTensorCarrierDesc_π M X Y s.pt s.π _) ?_
  intro s m hm
  apply relativeTensorCarrier_hom_ext M X Y
  exact hm.trans (relativeTensorCarrierDesc_π M X Y s.pt s.π _).symm

/-- Descend the original balanced right-linear arrow to an entire right-module map. -/
def relativeTensorDesc (X Y Z : RightModule M)
    (f : X.X ⊗ Y.X ⟶ Z.X)
    (hbal : (X.action ▷ Y.X) ≫ f =
      (α_ X.X M Y.X).hom ≫ (X.X ◁ leftAction M Y) ≫ f)
    (hlin : (α_ X.X Y.X M).hom ≫ (X.X ◁ Y.action) ≫ f =
      (f ▷ M) ≫ Z.action) : X ⊗ Y ⟶ Z := by
  let d := relativeTensorCarrierDesc M X Y Z.X f hbal
  refine Mod.Hom.mk' d ?_
  change (X ⊗ Y).action ≫ d = (d ▷ M) ≫ Z.action
  let _ : Epi (relativeTensorπ M X Y ▷ M) :=
    relativeTensorπ_whiskerRight_epi M X Y M
  apply (cancel_epi (relativeTensorπ M X Y ▷ M)).1
  calc
    _ = (α_ X.X Y.X M).hom ≫ (X.X ◁ Y.action) ≫
        relativeTensorπ M X Y ≫ d := by
      rw [← Category.assoc, relativeTensorπ_action]
      simp only [Category.assoc]
    _ = (α_ X.X Y.X M).hom ≫ (X.X ◁ Y.action) ≫ f := by
      rw [relativeTensorCarrierDesc_π]
    _ = (f ▷ M) ≫ Z.action := hlin
    _ = _ := by
      rw [← comp_whiskerRight_assoc, relativeTensorCarrierDesc_π]

/-- The entire module descent retains the full original projection value. -/
@[reassoc]
theorem relativeTensorDesc_π (X Y Z : RightModule M)
    (f : X.X ⊗ Y.X ⟶ Z.X)
    (hbal : (X.action ▷ Y.X) ≫ f =
      (α_ X.X M Y.X).hom ≫ (X.X ◁ leftAction M Y) ≫ f)
    (hlin : (α_ X.X Y.X M).hom ≫ (X.X ◁ Y.action) ≫ f =
      (f ▷ M) ≫ Z.action) :
    relativeTensorπ M X Y ≫ (relativeTensorDesc M X Y Z f hbal hlin).hom = f :=
  relativeTensorCarrierDesc_π M X Y Z.X f hbal

/-- Entire module arrows from the actual tensor are determined after projection. -/
theorem relativeTensor_hom_ext (X Y Z : RightModule M) (f g : X ⊗ Y ⟶ Z)
    (h : relativeTensorπ M X Y ≫ f.hom = relativeTensorπ M X Y ≫ g.hom) : f = g := by
  apply Mod.hom_ext
  exact relativeTensorCarrier_hom_ext M X Y Z.X f.hom g.hom h

/-- The whole tensor arrow restricts to its original balanced right-linear carrier map. -/
def relativeTensorRestrict (X Y Z : RightModule M) (f : X ⊗ Y ⟶ Z) :
    BalancedRightLinearMap M X Y Z where
  hom := relativeTensorπ M X Y ≫ f.hom
  balanced := by
    simpa only [Category.assoc] using
      congrArg (fun h => h ≫ f.hom) (relativeTensorπ_balance M X Y)
  right_linear := by
    calc
      _ = (relativeTensorπ M X Y ▷ M) ≫ (X ⊗ Y).action ≫ f.hom :=
        (relativeTensorπ_action_assoc M X Y f.hom).symm
      _ = (relativeTensorπ M X Y ▷ M) ≫ (f.hom ▷ M) ≫ Z.action := by
        rw [CommutativeModuleConversion.RightModule.comm f]
      _ = _ := by rw [comp_whiskerRight]; simp only [Category.assoc]

/-- The whole balanced-map inverse function is the actual proved module descent. -/
def relativeTensorDescBalanced (X Y Z : RightModule M)
    (f : BalancedRightLinearMap M X Y Z) : X ⊗ Y ⟶ Z :=
  relativeTensorDesc M X Y Z f.hom f.balanced f.right_linear

/-- Projection of the full balanced-map inverse function returns its entire arrow. -/
@[reassoc]
theorem relativeTensorDescBalanced_π (X Y Z : RightModule M)
    (f : BalancedRightLinearMap M X Y Z) :
    relativeTensorπ M X Y ≫ (relativeTensorDescBalanced M X Y Z f).hom = f.hom :=
  relativeTensorDesc_π M X Y Z f.hom f.balanced f.right_linear

/-- Both entire functions recover every original module arrow. -/
theorem relativeTensorDesc_restrict (X Y Z : RightModule M) (f : X ⊗ Y ⟶ Z) :
    relativeTensorDescBalanced M X Y Z (relativeTensorRestrict M X Y Z f) = f := by
  apply relativeTensor_hom_ext M X Y
  exact relativeTensorDescBalanced_π M X Y Z (relativeTensorRestrict M X Y Z f)

/-- Both entire functions recover every original balanced right-linear map. -/
theorem relativeTensorRestrict_desc (X Y Z : RightModule M)
    (f : BalancedRightLinearMap M X Y Z) :
    relativeTensorRestrict M X Y Z (relativeTensorDescBalanced M X Y Z f) = f := by
  apply BalancedRightLinearMap.ext
  exact relativeTensorDescBalanced_π M X Y Z f

/-- The full right-module tensor Hom equivalence with both proved original functions. -/
def relativeTensorHomEquiv (X Y Z : RightModule M) :
    (X ⊗ Y ⟶ Z) ≃ BalancedRightLinearMap M X Y Z where
  toFun := relativeTensorRestrict M X Y Z
  invFun := relativeTensorDescBalanced M X Y Z
  left_inv := relativeTensorDesc_restrict M X Y Z
  right_inv := relativeTensorRestrict_desc M X Y Z

/-- The entire forward Hom function is the actual projection function. -/
theorem relativeTensorHomEquiv_toFun (X Y Z : RightModule M) :
    (relativeTensorHomEquiv M X Y Z).toFun = relativeTensorRestrict M X Y Z := rfl

/-- The entire inverse Hom function is the actual balanced descent function. -/
theorem relativeTensorHomEquiv_invFun (X Y Z : RightModule M) :
    (relativeTensorHomEquiv M X Y Z).invFun = relativeTensorDescBalanced M X Y Z := rfl

/-- The carrier of the full tensor-Hom forward function is projection followed by the map. -/
theorem relativeTensorHomEquiv_hom (X Y Z : RightModule M) (f : X ⊗ Y ⟶ Z) :
    (relativeTensorHomEquiv M X Y Z f).hom = relativeTensorπ M X Y ≫ f.hom := rfl

/-- The full tensor-Hom inverse function is the original balanced descent. -/
theorem relativeTensorHomEquiv_symm (X Y Z : RightModule M)
    (f : BalancedRightLinearMap M X Y Z) :
    (relativeTensorHomEquiv M X Y Z).symm f = relativeTensorDescBalanced M X Y Z f := rfl

/-- The actual tensor map induced by two complete right-linear morphisms. -/
def relativeTensorMap {X X' Y Y' : RightModule M}
    (f : X ⟶ X') (g : Y ⟶ Y') : X ⊗ Y ⟶ X' ⊗ Y' := f ⊗ₘ g

/-- Both complete tensor-map inputs retain their full projection values. -/
@[reassoc]
theorem relativeTensorMap_π {X X' Y Y' : RightModule M}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    relativeTensorπ M X Y ≫ (relativeTensorMap M f g).hom =
      (f.hom ⊗ₘ g.hom) ≫ relativeTensorπ M X' Y' := by
  have h := Mod.relativeTensorMap_π (scalarCommMon M)
    (CommutativeModuleConversion.toLeftMap M f)
    (CommutativeModuleConversion.toLeftMap M g)
  rw [CommutativeModuleConversion.toLeftMap_hom,
    CommutativeModuleConversion.toLeftMap_hom] at h
  unfold relativeTensorMap
  rw [tensorHom_eq, CommutativeModuleConversion.toRightMap_hom]
  exact h

/-- The actual tensor map has both original identity inputs. -/
@[simp]
theorem relativeTensorMap_id (X Y : RightModule M) :
    relativeTensorMap M (𝟙 X) (𝟙 Y) = 𝟙 (X ⊗ Y) :=
  id_tensorHom_id X Y

/-- The actual tensor map respects both full input composites. -/
theorem relativeTensorMap_comp
    {X X' X'' Y Y' Y'' : RightModule M}
    (f : X ⟶ X') (f' : X' ⟶ X'') (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    relativeTensorMap M (f ≫ f') (g ≫ g') =
      relativeTensorMap M f g ≫ relativeTensorMap M f' g' :=
  (tensorHom_comp_tensorHom f g f' g').symm

/-- Precompose every entire balanced map with both original module arrows. -/
def BalancedRightLinearMap.precompose
    {X X' Y Y' Z : RightModule M} (f : X' ⟶ X) (g : Y' ⟶ Y)
    (h : BalancedRightLinearMap M X Y Z) : BalancedRightLinearMap M X' Y' Z :=
  relativeTensorRestrict M X' Y' Z
    (relativeTensorMap M f g ≫ relativeTensorDescBalanced M X Y Z h)

/-- The complete precomposition value is the original pair tensor followed by the map. -/
theorem BalancedRightLinearMap.precompose_hom
    {X X' Y Y' Z : RightModule M} (f : X' ⟶ X) (g : Y' ⟶ Y)
    (h : BalancedRightLinearMap M X Y Z) :
    (h.precompose M f g).hom = (f.hom ⊗ₘ g.hom) ≫ h.hom := by
  change relativeTensorπ M X' Y' ≫
      (relativeTensorMap M f g).hom ≫ (relativeTensorDescBalanced M X Y Z h).hom = _
  rw [← Category.assoc, relativeTensorMap_π, Category.assoc,
    relativeTensorDescBalanced_π]

/-- Postcompose every entire balanced map with an original target module arrow. -/
def BalancedRightLinearMap.postcompose {X Y Z Z' : RightModule M}
    (h : BalancedRightLinearMap M X Y Z) (f : Z ⟶ Z') :
    BalancedRightLinearMap M X Y Z' :=
  relativeTensorRestrict M X Y Z' (relativeTensorDescBalanced M X Y Z h ≫ f)

/-- The whole postcomposition value is the original map followed by the target arrow. -/
theorem BalancedRightLinearMap.postcompose_hom {X Y Z Z' : RightModule M}
    (h : BalancedRightLinearMap M X Y Z) (f : Z ⟶ Z') :
    (h.postcompose M f).hom = h.hom ≫ f.hom := by
  change relativeTensorπ M X Y ≫
      (relativeTensorDescBalanced M X Y Z h).hom ≫ f.hom = _
  rw [← Category.assoc, relativeTensorDescBalanced_π]

/-- The entire forward Hom family is natural in both source modules. -/
theorem relativeTensorHomEquiv_naturality_left
    {X X' Y Y' Z : RightModule M} (f : X' ⟶ X) (g : Y' ⟶ Y)
    (h : X ⊗ Y ⟶ Z) :
    relativeTensorHomEquiv M X' Y' Z (relativeTensorMap M f g ≫ h) =
      (relativeTensorHomEquiv M X Y Z h).precompose M f g := by
  apply BalancedRightLinearMap.ext
  rw [BalancedRightLinearMap.precompose_hom]
  change relativeTensorπ M X' Y' ≫ (relativeTensorMap M f g).hom ≫ h.hom = _
  rw [← Category.assoc, relativeTensorMap_π, Category.assoc]
  rfl

/-- The entire forward Hom family is natural in the target module. -/
theorem relativeTensorHomEquiv_naturality_right
    {X Y Z Z' : RightModule M} (h : X ⊗ Y ⟶ Z) (f : Z ⟶ Z') :
    relativeTensorHomEquiv M X Y Z' (h ≫ f) =
      (relativeTensorHomEquiv M X Y Z h).postcompose M f := by
  apply BalancedRightLinearMap.ext
  rw [BalancedRightLinearMap.postcompose_hom]
  change relativeTensorπ M X Y ≫ h.hom ≫ f.hom =
    (relativeTensorπ M X Y ≫ h.hom) ≫ f.hom
  exact (Category.assoc _ _ _).symm

/-- The entire inverse Hom family is natural in both source modules. -/
theorem relativeTensorDesc_naturality_left
    {X X' Y Y' Z : RightModule M} (f : X' ⟶ X) (g : Y' ⟶ Y)
    (h : BalancedRightLinearMap M X Y Z) :
    relativeTensorDescBalanced M X' Y' Z (h.precompose M f g) =
      relativeTensorMap M f g ≫ relativeTensorDescBalanced M X Y Z h :=
  relativeTensorDesc_restrict M X' Y' Z _

/-- The entire inverse Hom family is natural in the target module. -/
theorem relativeTensorDesc_naturality_right {X Y Z Z' : RightModule M}
    (h : BalancedRightLinearMap M X Y Z) (f : Z ⟶ Z') :
    relativeTensorDescBalanced M X Y Z' (h.postcompose M f) =
      relativeTensorDescBalanced M X Y Z h ≫ f :=
  relativeTensorDesc_restrict M X Y Z' _

/-- The actual tensor braiding retains the entire ambient braiding after projection. -/
@[reassoc]
theorem relativeTensorBraiding_hom_π (X Y : RightModule M) :
    relativeTensorπ M X Y ≫ (β_ X Y).hom.hom =
      (β_ X.X Y.X).hom ≫ relativeTensorπ M Y X := by
  have hb : (β_ X Y).hom = CommutativeModuleConversion.toRightMap M
      (Mod.relativeTensorBraiding (scalarCommMon M)
        (leftModule M X) (leftModule M Y)).hom := rfl
  rw [hb, CommutativeModuleConversion.toRightMap_hom]
  exact Mod.relativeTensorBraiding_hom_π
    (scalarCommMon M) (leftModule M X) (leftModule M Y)

/-- The monoidal structure on `Mod C M` given by the scalar commutative monoid of `M`, as a
local instance. -/
@[nolint defsWithUnderscore]
local instance : MonoidalCategory (Mod C M) :=
  Mod.instMonoidalCategory (scalarCommMon M)

/-- The original equivalence inverse is monoidal for the single transported tensor. -/
@[instance_reducible]
def inverseConversionMonoidal :
    (CommutativeModuleConversion.moduleEquivalence M).inverse.Monoidal :=
  inferInstanceAs
    (Monoidal.equivalenceTransported
      (CommutativeModuleConversion.moduleEquivalence M)).inverse.Monoidal

/-- The monoidal structure `inverseConversionMonoidal M` on the inverse of the module
equivalence, as a local instance. -/
local instance : (CommutativeModuleConversion.moduleEquivalence M).inverse.Monoidal :=
  inverseConversionMonoidal M

/-- The original equivalence forward functor has the corresponding complete monoidal structure. -/
@[instance_reducible]
def conversionMonoidal :
    (CommutativeModuleConversion.moduleEquivalence M).functor.Monoidal :=
  inferInstanceAs
    (Monoidal.equivalenceTransported
      (CommutativeModuleConversion.moduleEquivalence M)).functor.Monoidal

/-- The actual inverse tensorator retains the original equivalence unit. -/
def tensorLeftIso (X Y : RightModule M) :
    leftModule M X ⊗ leftModule M Y ≅ leftModule M (X ⊗ Y) :=
  Functor.Monoidal.μIso (CommutativeModuleConversion.moduleEquivalence M).inverse X Y

/-- The whole inverse tensorator is the original unit on the complete left tensor. -/
theorem tensorLeftIso_eq (X Y : RightModule M) :
    tensorLeftIso M X Y = (CommutativeModuleConversion.moduleEquivalence M).unitIso.app
      (leftModule M X ⊗ leftModule M Y) := by
  apply Iso.ext
  rfl

/-- Its complete forward carrier map is the original unit carrier map. -/
theorem tensorLeftIso_hom (X Y : RightModule M) :
    (tensorLeftIso M X Y).hom.hom = 𝟙 (X ⊗ Y).X := by
  rw [tensorLeftIso_eq]
  exact CommutativeModuleConversion.moduleEquivalence_unit_hom M _

/-- Its complete inverse carrier map is the original inverse-unit carrier map. -/
theorem tensorLeftIso_inv (X Y : RightModule M) :
    (tensorLeftIso M X Y).inv.hom = 𝟙 (X ⊗ Y).X := by
  rw [tensorLeftIso_eq]
  exact CommutativeModuleConversion.moduleEquivalence_unit_inv M _

/-- Both complete input arrows are retained by the actual inverse tensorator. -/
@[reassoc]
theorem tensorLeftIso_naturality {X X' Y Y' : RightModule M}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (CommutativeModuleConversion.toLeftMap M f ⊗ₘ
        CommutativeModuleConversion.toLeftMap M g) ≫ (tensorLeftIso M X' Y').hom =
      (tensorLeftIso M X Y).hom ≫ CommutativeModuleConversion.toLeftMap M (f ⊗ₘ g) :=
  Functor.LaxMonoidal.μ_natural (CommutativeModuleConversion.moduleEquivalence M).inverse f g

/-- Both complete input arrows are retained by the inverse of the tensorator. -/
@[reassoc]
theorem tensorLeftIso_inv_naturality {X X' Y Y' : RightModule M}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (tensorLeftIso M X Y).inv ≫
        (CommutativeModuleConversion.toLeftMap M f ⊗ₘ
          CommutativeModuleConversion.toLeftMap M g) =
      CommutativeModuleConversion.toLeftMap M (f ⊗ₘ g) ≫ (tensorLeftIso M X' Y').inv := by
  apply (cancel_mono (tensorLeftIso M X' Y').hom).1
  simp only [Category.assoc, tensorLeftIso_naturality, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- Projection through the actual tensorator is the same selected quotient projection. -/
@[reassoc]
theorem tensorLeftIso_π (X Y : RightModule M) :
    Mod.relativeTensorπ (scalarCommMon M) (leftModule M X) (leftModule M Y) ≫
      (tensorLeftIso M X Y).hom.hom = relativeTensorπ M X Y := by
  rw [tensorLeftIso_hom]
  exact Category.comp_id _

/-- The whole converted tensor-Hom forward function retains the original tensorator. -/
def tensorLeftRestrict (X Y Z : RightModule M) (f : X ⊗ Y ⟶ Z) :
    leftModule M X ⊗ leftModule M Y ⟶ leftModule M Z :=
  (tensorLeftIso M X Y).hom ≫ CommutativeModuleConversion.toLeftMap M f

/-- The whole converted tensor-Hom inverse function retains both actual counit transports. -/
def tensorLeftRestore (X Y Z : RightModule M)
    (f : leftModule M X ⊗ leftModule M Y ⟶ leftModule M Z) : X ⊗ Y ⟶ Z :=
  CommutativeModuleConversion.restoreRightHom M (X ⊗ Y) Z ((tensorLeftIso M X Y).inv ≫ f)

/-- Both whole converted functions recover the original right tensor arrow. -/
theorem tensorLeftRestore_restrict (X Y Z : RightModule M) (f : X ⊗ Y ⟶ Z) :
    tensorLeftRestore M X Y Z (tensorLeftRestrict M X Y Z f) = f := by
  unfold tensorLeftRestore tensorLeftRestrict
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  exact CommutativeModuleConversion.restoreRightHom_forward M f

/-- Both whole converted functions recover the original left tensor arrow. -/
theorem tensorLeftRestrict_restore (X Y Z : RightModule M)
    (f : leftModule M X ⊗ leftModule M Y ⟶ leftModule M Z) :
    tensorLeftRestrict M X Y Z (tensorLeftRestore M X Y Z f) = f := by
  unfold tensorLeftRestrict tensorLeftRestore
  rw [CommutativeModuleConversion.forward_restoreRightHom, ← Category.assoc,
    Iso.hom_inv_id, Category.id_comp]

/-- The whole tensor Hom equivalence uses the original equivalence and its actual tensorator. -/
def tensorLeftHomEquiv (X Y Z : RightModule M) :
    (X ⊗ Y ⟶ Z) ≃ (leftModule M X ⊗ leftModule M Y ⟶ leftModule M Z) where
  toFun := tensorLeftRestrict M X Y Z
  invFun := tensorLeftRestore M X Y Z
  left_inv := tensorLeftRestore_restrict M X Y Z
  right_inv := tensorLeftRestrict_restore M X Y Z

/-- The entire forward family is original conversion after the tensorator. -/
theorem tensorLeftHomEquiv_toFun (X Y Z : RightModule M) :
    (tensorLeftHomEquiv M X Y Z).toFun = tensorLeftRestrict M X Y Z := rfl

/-- The entire inverse family is original recovery after the inverse tensorator. -/
theorem tensorLeftHomEquiv_invFun (X Y Z : RightModule M) :
    (tensorLeftHomEquiv M X Y Z).invFun = tensorLeftRestore M X Y Z := rfl

end Tensor
end Symmetric
end CategoryTheory.RightModuleFree
