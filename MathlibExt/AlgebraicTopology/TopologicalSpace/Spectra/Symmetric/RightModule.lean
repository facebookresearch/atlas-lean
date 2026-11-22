/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.SphereOperatorCategory
public import MathlibExt.CategoryTheory.Monoidal.CommutativeModuleConversion

/-!
# Right sphere modules and symmetric operator diagrams

Commutativity of the sphere Day monoid and the braiding identify its left and right
modules, giving an equivalence between right sphere modules and symmetric operator
diagrams. Component formulas retain every module level and describe the right
coefficient action and its conversion to the left action through both value and index
braidings.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalOpposite
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalClosed
open scoped CategoryTheory.MonoidalCategory.ExternalProduct

namespace PointedCGWH.SymmetricRightModulePresentation

attribute [local instance] copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal
  sphereSequenceMonObj sphereSequenceIsCommMonObj
  MonoidalLeftAction.monoidalOppositeLeftAction

local notation "I" => Operad.SmallFinBijGroupoid

/-- Actual right modules over the original native sphere Day monoid. -/
abbrev RightSphereModule :=
  CommutativeModuleConversion.RightModule sphereSequence.{u, v}

/-- The original computed sphere braiding and commutativity give the full conversion. -/
def sphereModuleEquivalence :
    CategoryTheory.Mod (SymmetricSequence.{u, v}) sphereSequence.{u, v} ≌
      RightSphereModule.{u, v} :=
  CommutativeModuleConversion.moduleEquivalence sphereSequence.{u, v}

/-- Original right modules act on the entire native J Hom through the proved conversion. -/
def rightModuleToOperator : RightSphereModule.{u, v} ⥤
    EnrichedFunctorCat PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v} :=
  sphereModuleEquivalence.{u, v}.inverse ⋙ SymmetricModulePresentation.moduleToOperator.{u, v}

/-- Every genuine operator functor yields the actual original right-module data. -/
def operatorToRightModule :
    EnrichedFunctorCat PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v} ⥤
      RightSphereModule.{u, v} :=
  SymmetricModulePresentation.operatorToModule.{u, v} ⋙ sphereModuleEquivalence.{u, v}.functor

/-- The full right sphere modules and native J functors have actual inverse functors. -/
def rightModuleOperatorEquivalence : RightSphereModule.{u, v} ≌
    EnrichedFunctorCat PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v} :=
  sphereModuleEquivalence.{u, v}.symm.trans
    SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}

/-- The comparison retains every entire original module level. -/
theorem rightModuleToOperator_obj (M : RightSphereModule.{u, v}) (n : I) :
    ((rightModuleToOperator.{u, v}).obj M).toEnrichedFunctor.obj
        (symmetricOperatorObj.{u, v} n) = M.X.functor.obj n := rfl

/-- Every original right-module morphism retains its whole level transformation. -/
theorem rightModuleToOperator_component {M N : RightSphereModule.{u, v}}
    (f : M ⟶ N) (n : I) :
    EnrichedFunctorCat.component ((rightModuleToOperator.{u, v}).map f)
        (symmetricOperatorObj.{u, v} n) = f.hom.natTrans.app n := by
  change (EnrichedFunctorCat.component
      (SymmetricModulePresentation.toOperatorMorphism
        (CommutativeModuleConversion.toLeftMap sphereSequence.{u, v} f))
      (symmetricOperatorObj.{u, v} n) : M.X.functor.obj n ⟶ N.X.functor.obj n) =
    f.hom.natTrans.app n
  rw [SymmetricModulePresentation.toOperatorMorphism_component]
  rw [CommutativeModuleConversion.toLeftMap_hom]
  rfl

/-- The full original coefficient-right pair transformation. -/
def pairTransformation (M : RightSphereModule.{u, v}) :
    M.X.functor ⊠ sphereSequence.{u, v}.functor ⟶ tensor I ⋙ M.X.functor :=
  DayFunctor.η M.X sphereSequence.{u, v} ≫ Functor.whiskerLeft (tensor I)
    (ModObj.smul (M := mop sphereSequence.{u, v}) (X := M.X)).natTrans

/-- The complete native right pair action keeps the source index first. -/
def pairAction (M : RightSphereModule.{u, v}) (n a : I) :
    M.X.functor.obj n ⊗ sphereSequence.{u, v}.functor.obj a ⟶ M.X.functor.obj (n ⊗ a) :=
  (pairTransformation M).app (n, a)

/-- All original index and coefficient arrows satisfy the full pair square. -/
theorem pairAction_naturality (M : RightSphereModule.{u, v})
    {n n' a a' : I} (f : n ⟶ n') (g : a ⟶ a') :
    (M.X.functor.map f ⊗ₘ sphereSequence.{u, v}.functor.map g) ≫ pairAction M n' a' =
      pairAction M n a ≫ M.X.functor.map (f ⊗ₘ g) :=
  (pairTransformation M).naturality (show (n, a) ⟶ (n', a') from (f, g))

/-- Every original coefficient-right generator retains its full labelled action. -/
def arrowAction (M : RightSphereModule.{u, v}) (n a k : I) (f : n ⊗ a ⟶ k) :
    M.X.functor.obj n ⊗ sphereSequence.{u, v}.functor.obj a ⟶ M.X.functor.obj k :=
  pairAction M n a ≫ M.X.functor.map f

/-- The native Day braid has its complete source-index and value-braid generator formula. -/
theorem dayBraiding_generator (P Q : SymmetricSequence.{u, v}) (a n : I) :
    (DayFunctor.η P Q).app (a, n) ≫ (β_ P Q).hom.natTrans.app (a ⊗ n) =
      (β_ (P.functor.obj a) (Q.functor.obj n)).hom ≫
        (DayFunctor.η Q P).app (n, a) ≫ (Q ⊗ P).functor.map (β_ n a).hom := by
  let _ : DayConvolution P.functor Q.functor :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolution I PointedCGWH.{u, v}
      (SymmetricSequence.{u, v}) P Q
  let _ : DayConvolution Q.functor P.functor :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolution I PointedCGWH.{u, v}
      (SymmetricSequence.{u, v}) Q P
  change (DayConvolution.unit P.functor Q.functor).app (a, n) ≫
      (DayConvolution.braiding P.functor Q.functor).hom.app (a ⊗ n) = _
  exact DayConvolution.unit_app_braiding_hom_app P.functor Q.functor a n

/-- Both native braids recover the complete coefficient-first action from right modules. -/
theorem leftPairAction (M : RightSphereModule.{u, v}) (a n : I) :
    SymmetricModulePresentation.pairAction
        (CommutativeModuleConversion.toLeft sphereSequence.{u, v} M) a n =
      (β_ (sphereSequence.{u, v}.functor.obj a) (M.X.functor.obj n)).hom ≫
        pairAction M n a ≫ M.X.functor.map (β_ n a).hom := by
  let r : M.X ⊗ sphereSequence.{u, v} ⟶ M.X :=
    ModObj.smul (M := mop sphereSequence.{u, v}) (X := M.X)
  have hB := dayBraiding_generator sphereSequence.{u, v} M.X a n
  have hNat := r.natTrans.naturality (β_ n a).hom
  dsimp only [SymmetricModulePresentation.pairAction,
    SymmetricModulePresentation.pairTransformation]
  rw [CommutativeModuleConversion.toLeft_smul]
  dsimp only [CommutativeModuleConversion.leftAction]
  change (DayFunctor.η sphereSequence.{u, v} M.X).app (a, n) ≫
      (β_ sphereSequence.{u, v} M.X).hom.natTrans.app (a ⊗ n) ≫
      r.natTrans.app (a ⊗ n) = _
  rw [← Category.assoc, hB]
  simp only [Category.assoc]
  rw [hNat]
  rfl

end PointedCGWH.SymmetricRightModulePresentation
