/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.ScalarCircleHoFunctor
import MathlibExt.AlgebraicTopology.ModelCategory.DerivedSuspensionLoopAdjunction

/-!
# Generic ordinary suspension Hom groups from the original framing

The actual original closed framing Hom equivalence identifies each full
ordinary suspension Hom set with the scalar circle Hom of its genuine
mapping object. The earned scalar group then supplies the group structure.
Both original coefficient arguments retain their complete Ho map functions
through the full closed-Hom naturalities. No group on the generic model's
Hom sets or ordinary stability conclusion is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe w u v

open CategoryTheory Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.OrdinarySuspensionHomGroups

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasZeroObject C]
  [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ)

local notation "d" => GeneratedFunctorialReplacements.fromGeneration g
local notation "Σ" => DerivedSuspensionLoopAdjunction.suspension d

/-- The genuine original mapping object on both complete ordinary-Ho arguments. -/
def mapping (X Y : HomotopyCategory C) : PointedFramingAction.PointedSpaceHo.{v} :=
  ((PointedFramingAction.mappingHo d).obj (Opposite.op X)).obj Y

/-- The actual original tensor-action carrier at the circle is the same ordinary suspension functor. -/
def actionCircleIso : (PointedFramingAction.tensorAction d).obj
    (PointedFramingAction.pointedProjection.obj DerivedSuspensionLoopAdjunction.circle) ≅ Σ :=
  eqToIso (PointedFramingAction.tensorAction_obj d DerivedSuspensionLoopAdjunction.circle)

/-- Both original closed Hom functions are retained after the earned suspension carrier comparison. -/
def homEquiv (X Y : HomotopyCategory C) :
    ((Σ).obj X ⟶ Y) ≃
      (PointedFramingAction.pointedProjection.obj DerivedSuspensionLoopAdjunction.circle ⟶ mapping g X Y) :=
  (Iso.homCongr ((actionCircleIso g).app X).symm (Iso.refl Y)).trans
    (PointedFramingAction.closedHomEquiv d X
      (PointedFramingAction.pointedProjection.obj DerivedSuspensionLoopAdjunction.circle) Y)

/-- Every original Ho target arrow preserves the complete suspension/HFC Hom function. -/
theorem homEquiv_target (X : HomotopyCategory C) {Y Y' : HomotopyCategory C}
    (f : Y ⟶ Y') (h : (Σ).obj X ⟶ Y) :
    homEquiv g X Y' (h ≫ f) = homEquiv g X Y h ≫
      ((PointedFramingAction.mappingHo d).obj (Opposite.op X)).map f := by
  simp only [homEquiv, Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv,
    Iso.refl_hom, Category.comp_id]
  dsimp only [mapping]
  simpa only [Category.assoc] using PointedFramingAction.closedHomEquiv_target d X
    (PointedFramingAction.pointedProjection.obj DerivedSuspensionLoopAdjunction.circle) f
      (((actionCircleIso g).app X).hom ≫ h)

/-- Every original Ho source arrow preserves the complete suspension/HFC Hom function. -/
theorem homEquiv_source {X X' : HomotopyCategory C} (f : X ⟶ X') (Y : HomotopyCategory C)
    (h : (Σ).obj X' ⟶ Y) :
    homEquiv g X Y ((Σ).map f ≫ h) = homEquiv g X' Y h ≫
      ((PointedFramingAction.mappingHo d).map f.op).app Y := by
  simp only [homEquiv, Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv,
    Iso.refl_hom, Category.comp_id]
  have hn := (actionCircleIso g).hom.naturality f
  change ((PointedFramingAction.tensorAction d).obj
      (PointedFramingAction.pointedProjection.obj DerivedSuspensionLoopAdjunction.circle)).map f ≫
        ((actionCircleIso g).app X').hom = ((actionCircleIso g).app X).hom ≫ (Σ).map f at hn
  rw [← Category.assoc, ← hn, Category.assoc]
  exact PointedFramingAction.closedHomEquiv_source d f
    (PointedFramingAction.pointedProjection.obj DerivedSuspensionLoopAdjunction.circle) Y
      (((actionCircleIso g).app X').hom ≫ h)

/-- The group on the full original ordinary suspension Hom set comes from the genuine scalar HFC group. -/
@[instance_reducible]
def group (X Y : HomotopyCategory C) : Group ((Σ).obj X ⟶ Y) :=
  letI := ScalarCircleHoFunctor.group.{0, v} (mapping g X Y)
  EquivTransport.group (homEquiv g X Y)

/-- The full original target postcomposition function is an earned group homomorphism. -/
def postcompose (X : HomotopyCategory C) {Y Y' : HomotopyCategory C} (f : Y ⟶ Y') :
    letI := group g X Y
    letI := group g X Y'
    ((Σ).obj X ⟶ Y) →* ((Σ).obj X ⟶ Y') := by
  letI := group g X Y
  letI := group g X Y'
  letI := ScalarCircleHoFunctor.group.{0, v} (mapping g X Y)
  letI := ScalarCircleHoFunctor.group.{0, v} (mapping g X Y')
  exact EquivTransport.map (homEquiv g X Y) (homEquiv g X Y') (fun h => h ≫ f)
    (ScalarCircleHoFunctor.postcompose.{0, v}
      (((PointedFramingAction.mappingHo d).obj (Opposite.op X)).map f))
    (fun h => by
      rw [ScalarCircleHoFunctor.postcompose_apply]
      exact homEquiv_target g X f h)

/-- The full original source precomposition function is an earned group homomorphism. -/
def precompose {X X' : HomotopyCategory C} (f : X ⟶ X') (Y : HomotopyCategory C) :
    letI := group g X' Y
    letI := group g X Y
    ((Σ).obj X' ⟶ Y) →* ((Σ).obj X ⟶ Y) := by
  letI := group g X' Y
  letI := group g X Y
  letI := ScalarCircleHoFunctor.group.{0, v} (mapping g X' Y)
  letI := ScalarCircleHoFunctor.group.{0, v} (mapping g X Y)
  exact EquivTransport.map (homEquiv g X' Y) (homEquiv g X Y) (fun h => (Σ).map f ≫ h)
    (ScalarCircleHoFunctor.postcompose.{0, v} (((PointedFramingAction.mappingHo d).map f.op).app Y))
    (fun h => by
      rw [ScalarCircleHoFunctor.postcompose_apply]
      exact homEquiv_source g f Y h)

/-- The entire target group-map function retains the original Ho composition. -/
theorem postcompose_apply (X : HomotopyCategory C) {Y Y' : HomotopyCategory C} (f : Y ⟶ Y')
    (h : (Σ).obj X ⟶ Y) : postcompose g X f h = h ≫ f := rfl

/-- The entire source group-map function retains the original ordinary suspension map. -/
theorem precompose_apply {X X' : HomotopyCategory C} (f : X ⟶ X') (Y : HomotopyCategory C)
    (h : (Σ).obj X' ⟶ Y) : precompose g f Y h = (Σ).map f ≫ h := rfl

end HomotopicalAlgebra.OrdinarySuspensionHomGroups
