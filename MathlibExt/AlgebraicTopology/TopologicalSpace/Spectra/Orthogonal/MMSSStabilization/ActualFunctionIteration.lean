/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.FunctionIteration
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.OriginalSequentialFunctionChart

/-!
# Actual orthogonal function iterates and the original free-sphere arrows

Every functor below is the original translated right-module mapping end carried
through the canonical native/source equivalence. The complete free-sphere
tensor comparisons supply its powers. The free-source evaluation comparisons
retain the actual native operator actions and every original coefficient map.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory BraidedCategory Limits
open CategoryTheory.Enriched
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open PointedCGWH.Spectra.Orthogonal FunctionSpectrum
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration

/-- The canonical source smash tensor on native orthogonal spectra. -/
local instance : MonoidalCategory CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmash.monoidalCategory.{u, v}
/-- The native internal Hom structure for the canonical source smash on orthogonal spectra. -/
local instance : MonoidalClosed CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmashClosed.monoidalClosed.{u, v}

/-- The whole actual first Mapping_R functor is the original canonical closed function. -/
def stabilizationFunctionIhomIso :
    stabilizationFunction.{u, v} ≅ ihom (NativePowers.sphereFree.{u, v} 1) :=
  eqToIso ((mappingFunctor_eq_original (NativePowers.sphereFree 1)).trans
    (CanonicalSourceSmashClosed.ihom_eq (NativePowers.sphereFree 1)).symm)

/-- Both maps identify the complete original free-sphere Mapping_R in every degree. -/
def freeSphereIhomIso (n : ℕ) :
    ihom (NativePowers.sphereFree.{u, v} n) ≅
      mappingFunctor (NativePowers.sphereFree.{u, v} n) :=
  eqToIso ((CanonicalSourceSmashClosed.ihom_eq (NativePowers.sphereFree n)).trans
    (mappingFunctor_eq_original (NativePowers.sphereFree n)).symm)

/-- Every actual R power is the original complete F_n(S^n) mapping-end functor. -/
def functionFreeSphereIterationIso (n : ℕ) :
    Functor.Iteration.iterate stabilizationFunction.{u, v} n ≅
      mappingFunctor (NativePowers.sphereFree.{u, v} n) :=
  Functor.Iteration.iterateIso stabilizationFunctionIhomIso n ≪≫
    (NativePowers.freeFunctionIterationIso n).symm ≪≫ freeSphereIhomIso n

/-- The complete original free/evaluation maps identify the actual iterate
with its shifted cotensor. -/
def functionIterationOutputIso (n : ℕ) :
    Functor.Iteration.iterate stabilizationFunction.{u, v} n ≅
      shiftedCotensor n (PointedCGWH.orthogonalSphere.{u, v} n) :=
  functionFreeSphereIterationIso n ≪≫
    nativeFreeFunctionNatIso n (PointedCGWH.orthogonalSphere n)

/-- All original input arrows remain in the forward whole free-sphere comparison. -/
theorem functionFreeSphereIterationIso_hom_naturality (n : ℕ)
    {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    (Functor.Iteration.iterate stabilizationFunction n).map f ≫
        (functionFreeSphereIterationIso n).hom.app Y =
      (functionFreeSphereIterationIso n).hom.app X ≫
        (mappingFunctor (NativePowers.sphereFree n)).map f :=
  (functionFreeSphereIterationIso n).hom.naturality f

/-- The inverse whole comparison retains those same original input arrows. -/
theorem functionFreeSphereIterationIso_inv_naturality (n : ℕ)
    {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    (mappingFunctor (NativePowers.sphereFree n)).map f ≫
        (functionFreeSphereIterationIso n).inv.app Y =
      (functionFreeSphereIterationIso n).inv.app X ≫
        (Functor.Iteration.iterate stabilizationFunction n).map f :=
  (functionFreeSphereIterationIso n).inv.naturality f

/-- Every whole native input arrow is retained by the forward source output chart. -/
theorem functionIterationOutputIso_hom_naturality (n : ℕ)
    {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    (Functor.Iteration.iterate stabilizationFunction n).map f ≫
        (functionIterationOutputIso n).hom.app Y =
      (functionIterationOutputIso n).hom.app X ≫
        (shiftedCotensor n (PointedCGWH.orthogonalSphere n)).map f :=
  (functionIterationOutputIso n).hom.naturality f

/-- The inverse source output chart retains every whole original native input arrow. -/
theorem functionIterationOutputIso_inv_naturality (n : ℕ)
    {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    (shiftedCotensor n (PointedCGWH.orthogonalSphere n)).map f ≫
        (functionIterationOutputIso n).inv.app Y =
      (functionIterationOutputIso n).inv.app X ≫
        (Functor.Iteration.iterate stabilizationFunction n).map f :=
  (functionIterationOutputIso n).inv.naturality f

/-- The original shifted cotensor retains both identity evaluation maps at every pair of degrees. -/
def shiftedCotensorEvaluationIso (n m : ℕ) :
    shiftedCotensor n (PointedCGWH.orthogonalSphere.{u, v} n) ⋙ IterationMaps.level m ≅
      IterationMaps.level (m + n) ⋙ ihom (PointedCGWH.orthogonalSphere.{u, v} n) :=
  NatIso.ofComponents
    (fun X => Iso.refl ((ihom (PointedCGWH.orthogonalSphere.{u, v} n)).obj
      (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (m + n)))))
    (by
      intro X Y f
      change component ((shiftedCotensor n (PointedCGWH.orthogonalSphere n)).map f)
          (OrthogonalOperatorIndex.ofIndex.{u, v} m) ≫ 𝟙 _ =
        𝟙 _ ≫ (ihom (PointedCGWH.orthogonalSphere n)).map
          (component f (OrthogonalOperatorIndex.ofIndex.{u, v} (m + n)))
      rw [Category.comp_id, Category.id_comp]
      exact (cotensorMap_component (PointedCGWH.orthogonalSphere n) _ _).trans
        (congrArg (ihom (PointedCGWH.orthogonalSphere n)).map
          (RightShift.shift_map_component n m f)))

/-- Every actual iterate evaluates through its complete original free-sphere
function and coefficient. -/
def functionIterationCoefficientEvaluationIso (n m : ℕ) :
    Functor.Iteration.iterate stabilizationFunction.{u, v} n ⋙ IterationMaps.level m ≅
      IterationMaps.level (m + n) ⋙ ihom (PointedCGWH.orthogonalSphere.{u, v} n) :=
  Functor.isoWhiskerRight (functionIterationOutputIso n) (IterationMaps.level m) ≪≫
    shiftedCotensorEvaluationIso n m

/-- The genuine first free/function chart and its original iteration maps
give every evaluated loop power. -/
def functionIterationEvaluationIso (n m : ℕ) :
    Functor.Iteration.iterate stabilizationFunction.{u, v} n ⋙ IterationMaps.level m ≅
      IterationMaps.level (m + n) ⋙ LoopPowerAtPoints.power n :=
  Functor.isoWhiskerRight (Functor.Iteration.iterateIso stabilizationFunctionIso n)
    (IterationMaps.level m) ≪≫ IterationMaps.evaluationComparison n m

/-- Both entire evaluated comparison maps retain the original input-spectrum naturality. -/
theorem functionIterationEvaluationIso_hom_naturality (n m : ℕ)
    {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    (IterationMaps.level m).map ((Functor.Iteration.iterate stabilizationFunction n).map f) ≫
        (functionIterationEvaluationIso n m).hom.app Y =
      (functionIterationEvaluationIso n m).hom.app X ≫
        (LoopPowerAtPoints.power n).map ((IterationMaps.level (m + n)).map f) :=
  (functionIterationEvaluationIso n m).hom.naturality f

/-- The inverse evaluated comparison retains those same complete original input-spectrum maps. -/
theorem functionIterationEvaluationIso_inv_naturality (n m : ℕ)
    {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    (LoopPowerAtPoints.power n).map ((IterationMaps.level (m + n)).map f) ≫
        (functionIterationEvaluationIso n m).inv.app Y =
      (functionIterationEvaluationIso n m).inv.app X ≫
        (IterationMaps.level m).map ((Functor.Iteration.iterate stabilizationFunction n).map f) :=
  (functionIterationEvaluationIso n m).inv.naturality f

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.LambdaUnitSource.SourceAlgebra

universe uC vC
variable {C : Type uC} [Category.{vC} C]

/-- A complete coefficient isomorphism cancels in the original five-map source word. -/
theorem cancelCoefficientIso {A B D E T : C} (f : A ⟶ B) (g : B ⟶ D)
    (e : D ≅ E) (q : D ⟶ T) :
    (f ≫ g ≫ e.hom) ≫ (e.inv ≫ q) = f ≫ g ≫ q := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.LambdaUnitSource.SourceAlgebra

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.LambdaUnitSource

open FunctionIteration

/-- The canonical source smash tensor on native orthogonal spectra. -/
local instance : MonoidalCategory CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmash.monoidalCategory.{u, v}

/-- The original native free representation sphere in every degree. -/
abbrev sphereFree (n : ℕ) := NativePowers.sphereFree.{u, v} n

/-- The original zero-plus-n label is retained before the actual stabilization map. -/
def gammaSourceIso (n : ℕ) :
    sphereFree.{u, v} n ≅ Free.object
      (OrthogonalOperatorIndex.ofIndex.{u, v} (0 + n)) (PointedCGWH.orthogonalSphere.{u, v} n) :=
  eqToIso (congrArg (fun k => Free.object
    (OrthogonalOperatorIndex.ofIndex.{u, v} k) (PointedCGWH.orthogonalSphere.{u, v} n))
      (Nat.zero_add n).symm)

/-- Each actual source-to-unit gamma uses the original stabilization
and complete native free-zero inverse. -/
def gamma (n : ℕ) : sphereFree.{u, v} n ⟶ 𝟙_ CanonicalSourceSmash.Carrier.{u, v} :=
  (gammaSourceIso n).hom ≫ Actual.orthogonalStabilization 0 n ≫
    CanonicalSourceSmashUnit.unitIso.inv

/-- The original first free sphere, including its whole native enriched action. -/
abbrev source := sphereFree.{u, v} 1

/-- The actual source-to-unit arrow from the original zero-one stabilization. -/
abbrev lambda01 : source.{u, v} ⟶ 𝟙_ CanonicalSourceSmash.Carrier.{u, v} := gamma 1

/-- The original native zero-free sphere retains its actual sphere-zero coefficient. -/
abbrev freeZeroSphere := Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} 0)
  (PointedCGWH.orthogonalSphere.{u, v} 0)

/-- Both complete free-zero unit maps retain the original source unit
and sphere-zero coefficient. -/
def unitFreeZeroSphereIso : 𝟙_ CanonicalSourceSmash.Carrier.{u, v} ≅ freeZeroSphere.{u, v} :=
  CanonicalSourceSmashUnit.unitIso ≪≫
    (Free.functor (OrthogonalOperatorIndex.ofIndex.{u, v} 0)).mapIso
      PointedCGWH.orthogonalSphereUnitIso.{u, v}

/-- The literal original lambda has free-one sphere source and free-zero sphere target. -/
def lambdaFree01 : source.{u, v} ⟶ freeZeroSphere.{u, v} :=
  (gammaSourceIso 1).hom ≫ Actual.orthogonalStabilization 0 1 ≫
    (Free.functor (OrthogonalOperatorIndex.ofIndex.{u, v} 0)).map
      PointedCGWH.orthogonalSphereUnitIso.hom

/-- Both original free-zero unit factors recover exactly the same original unit arrow. -/
theorem lambdaFree01_unit_inverse : lambdaFree01.{u, v} ≫ unitFreeZeroSphereIso.inv = lambda01 := by
  exact SourceAlgebra.cancelCoefficientIso
    (gammaSourceIso.{u, v} 1).hom (Actual.orthogonalStabilization.{u, v} 0 1)
    ((Free.functor (OrthogonalOperatorIndex.ofIndex.{u, v} 0)).mapIso
      PointedCGWH.orthogonalSphereUnitIso.{u, v})
    CanonicalSourceSmashUnit.unitIso.{u, v}.inv

/-- The complete original native lambda retains every original stabilization and unit factor. -/
theorem lambda01_original_initializer : lambda01.{u, v} =
    (gammaSourceIso.{u, v} 1).hom ≫ Actual.orthogonalStabilization.{u, v} 0 1 ≫
      CanonicalSourceSmashUnit.unitIso.{u, v}.inv := rfl

/-- The literal complete free-zero arrow retains the original degree pair and coefficient map. -/
theorem lambdaFree01_original_initializer : lambdaFree01.{u, v} =
    (gammaSourceIso.{u, v} 1).hom ≫ Actual.orthogonalStabilization.{u, v} 0 1 ≫
      (Free.functor (OrthogonalOperatorIndex.ofIndex.{u, v} 0)).map
        PointedCGWH.orthogonalSphereUnitIso.{u, v}.hom := rfl

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.LambdaUnitSource


namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.LambdaUnitSource.UnitSource

universe uV vV uI
open CategoryTheory.EnrichedFunctorCat
open scoped CategoryTheory.MonObj
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I]
  [MonoidalCategory (EnrichedFunctorCat V I)]
  (S : EnrichedFunctorCat V I) [MonObj S]

/-- The full original source-unit adjunct, on the unchanged stock right-module free functor. -/
def SourceUnitEpsilonProperty (a : I)
    (q : Free.object a (𝟙_ V) ≅ 𝟙_ (EnrichedFunctorCat V I))
    (epsilon : 𝟙_ V ⟶ S.toEnrichedFunctor.obj a) : Prop :=
  (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction S a).homEquiv
      (𝟙_ V) (RightModuleFree.regularObject S)
      (CanonicalSourceRightModuleFreeUnit.Internal.sourceFreeRegularIso S a (𝟙_ V) q).hom =
    epsilon

private theorem module_eqToHom_hom
    {M N : CommutativeModuleConversion.RightModule S} (e : M = N) :
    (eqToHom e).hom = eqToHom (congrArg (fun M => M.X) e) := by
  cases e
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The entire original source unit comparison sends its actual free generator
to the original monoid unit. -/
theorem sourceUnit_generator (a : I)
    (q : Free.object a (𝟙_ V) ≅ 𝟙_ (EnrichedFunctorCat V I)) :
    RightModuleFree.freeGenerator S (Free.object a (𝟙_ V)) ≫
        (CanonicalSourceRightModuleFreeUnit.Internal.sourceFreeRegularIso S a (𝟙_ V) q).hom.hom =
      q.hom ≫ MonObj.one (X := S) := by
  have hcar :
      (CanonicalSourceRightModuleFreeUnit.Internal.sourceFreeRegularIso S a (𝟙_ V) q).hom.hom =
        (q.hom ▷ S) ≫ (λ_ S).hom := by
    have hid : (eqToHom
        (CanonicalSourceRightModuleFreeUnit.Internal.sourceFreeObjectEq S a (𝟙_ V))).hom =
      𝟙 (Free.object a (𝟙_ V) ⊗ S) := by
      rw [module_eqToHom_hom]
      rfl
    have h := congrArg Mod.Hom.hom
      (CanonicalSourceRightModuleFreeUnit.Internal.sourceFreeRegularIso_hom S a (𝟙_ V) q)
    have hc :
        (CanonicalSourceRightModuleFreeUnit.Internal.sourceFreeRegularIso S a (𝟙_ V) q).hom.hom =
          𝟙 (Free.object a (𝟙_ V) ⊗ S) ≫ ((q.hom ▷ S) ≫ (λ_ S).hom) := by
      simpa only [Mod.comp_hom', hid, RightModuleFree.freeMap_hom,
        RightModuleFree.freeUnitRegularIso_hom] using h
    exact hc.trans (Category.id_comp ((q.hom ▷ S) ≫ (λ_ S).hom))
  have hunit := RightModuleFree.freeUnitRegularIso_generator S
  change RightModuleFree.freeGenerator S (𝟙_ (EnrichedFunctorCat V I)) ≫ (λ_ S).hom =
    MonObj.one (X := S) at hunit
  calc
    _ = RightModuleFree.freeGenerator S (Free.object a (𝟙_ V)) ≫
        ((q.hom ▷ S) ≫ (λ_ S).hom) := congrArg (fun f =>
          RightModuleFree.freeGenerator S (Free.object a (𝟙_ V)) ≫ f) hcar
    _ = (q.hom ≫ RightModuleFree.freeGenerator S (𝟙_ (EnrichedFunctorCat V I))) ≫
        (λ_ S).hom := (Category.assoc _ _ _).symm.trans
          (congrArg (fun f => f ≫ (λ_ S).hom) (RightModuleFree.freeGenerator_naturality S q.hom))
    _ = q.hom ≫ MonObj.one (X := S) := (Category.assoc _ _ _).trans
      (congrArg (fun f => q.hom ≫ f) hunit)

/-- The genuine two-stage source adjunction evaluates the full unit comparison
through both original units. -/
theorem sourceUnit_evaluation (a : I)
    (q : Free.object a (𝟙_ V) ≅ 𝟙_ (EnrichedFunctorCat V I)) :
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction S a).homEquiv
        (𝟙_ V) (RightModuleFree.regularObject S)
        (CanonicalSourceRightModuleFreeUnit.Internal.sourceFreeRegularIso S a (𝟙_ V) q).hom =
      Free.evaluate a (𝟙_ V) S (q.hom ≫ MonObj.one (X := S)) :=
  (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.hom_apply S a (𝟙_ V)
    (RightModuleFree.regularObject S)
    (CanonicalSourceRightModuleFreeUnit.Internal.sourceFreeRegularIso S a (𝟙_ V) q).hom).trans
      (congrArg (Free.evaluate a (𝟙_ V) S) (sourceUnit_generator S a q))

universe uJ
variable {J : Type uJ} [EnrichedCategory V J]

/-- The inverse actual native unit comparison has the original full source-adjunction evaluation. -/
theorem inverseUnit_evaluation
    (E : CommutativeModuleConversion.RightModule S ≌ EnrichedFunctorCat V J)
    (i : I) (a : J) (q : Free.object i (𝟙_ V) ≅ 𝟙_ (EnrichedFunctorCat V I))
    (h : E.functor ⋙ EnrichedFunctorCat.evaluation a ≅
      CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.evaluation S i) :
    Free.evaluate a (𝟙_ V) (E.functor.obj (RightModuleFree.regularObject S))
        (CanonicalSourceRightModuleFreeUnit.Internal.regularUnitOperatorIso
          S E i a q h).inv =
      (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction S i).homEquiv
          (𝟙_ V) (RightModuleFree.regularObject S)
          (CanonicalSourceRightModuleFreeUnit.Internal.sourceFreeRegularIso S i (𝟙_ V) q).hom ≫
        h.inv.app (RightModuleFree.regularObject S) :=
  (FreeAdjunctionSource.point E a
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S i)
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.evaluation S i)
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction S i) h
    (CanonicalSourceRightModuleFreeUnit.Internal.sourceFreeRegularIso S i (𝟙_ V) q).hom).symm

/-- The full inverse native unit adjunct retains the entire original evaluation comparison. -/
def InverseUnitEpsilonProperty
    (E : CommutativeModuleConversion.RightModule S ≌ EnrichedFunctorCat V J)
    (i : I) (a : J) (q : Free.object i (𝟙_ V) ≅ 𝟙_ (EnrichedFunctorCat V I))
    (h : E.functor ⋙ EnrichedFunctorCat.evaluation a ≅
      CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.evaluation S i)
    (epsilon : 𝟙_ V ⟶ S.toEnrichedFunctor.obj i) : Prop :=
  Free.evaluate a (𝟙_ V) (E.functor.obj (RightModuleFree.regularObject S))
      (CanonicalSourceRightModuleFreeUnit.Internal.regularUnitOperatorIso S E i a q h).inv ≫
        h.hom.app (RightModuleFree.regularObject S) = epsilon

/-- The proved source unit and actual inverse evaluation comparison give the whole inverse law. -/
theorem inverseUnit_epsilon_spec
    (E : CommutativeModuleConversion.RightModule S ≌ EnrichedFunctorCat V J)
    (i : I) (a : J) (q : Free.object i (𝟙_ V) ≅ 𝟙_ (EnrichedFunctorCat V I))
    (h : E.functor ⋙ EnrichedFunctorCat.evaluation a ≅
      CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.evaluation S i)
    (epsilon : 𝟙_ V ⟶ S.toEnrichedFunctor.obj i)
    (hu : SourceUnitEpsilonProperty S i q epsilon) :
    InverseUnitEpsilonProperty S E i a q h epsilon := by
  have he := congrArg (fun f => f ≫ h.hom.app (RightModuleFree.regularObject S))
    (inverseUnit_evaluation S E i a q h)
  have hc := congrArg (fun f =>
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction S i).homEquiv
      (𝟙_ V) (RightModuleFree.regularObject S)
      (CanonicalSourceRightModuleFreeUnit.Internal.sourceFreeRegularIso S i (𝟙_ V) q).hom ≫ f)
        (h.inv_hom_id_app (RightModuleFree.regularObject S))
  exact he.trans ((Category.assoc _ _ _).trans
    (hc.trans ((Category.comp_id _).trans hu)))

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.LambdaUnitSource.UnitSource

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.LambdaUnitSource.DayUnitSource

universe uV vV uI vI
open EnrichedFunctorCat EnrichedDayKernel
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)

omit [HasColimitsOfSize.{uI, uI} V] in
/-- The original free coefficient-unit comparison and full represented sphere unit
evaluate to the original lax sphere unit. -/
theorem representedUnit_evaluation :
    Free.evaluate (𝟙_ I) (𝟙_ V) (⟨S⟩ : EnrichedFunctorCat V I)
        ((Free.unitCoefficientIso (𝟙_ I)).hom ≫ LaxMonoid.unit d S L) = L.epsilon := by
  have he := Free.evaluate_postcomp (𝟙_ I) (𝟙_ V)
    (Free.unitCoefficientIso (𝟙_ I)).hom (LaxMonoid.unit d S L)
  have hu := Free.unitCoefficientIso_identity_evaluation (V := V) (𝟙_ I)
  let m := EnrichedFunctorCat.component (LaxMonoid.unit d S L) (𝟙_ I)
  exact he.trans ((congrArg (fun f => f ≫ m) hu).trans (LaxMonoid.unit_epsilon d S L))

/-- The genuine Day monoid and both original free adjunctions
compute the whole sphere-unit adjunct. -/
theorem sourceUnit_epsilon :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction
        (⟨S⟩ : EnrichedFunctorCat V I) (𝟙_ I)).homEquiv
        (𝟙_ V) (RightModuleFree.regularObject (⟨S⟩ : EnrichedFunctorCat V I))
        (CanonicalSourceRightModuleFreeUnit.Internal.sourceFreeRegularIso
          (⟨S⟩ : EnrichedFunctorCat V I) (𝟙_ I) (𝟙_ V)
          (Free.unitCoefficientIso (𝟙_ I))).hom = L.epsilon := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  have hu := UnitSource.sourceUnit_evaluation (⟨S⟩ : EnrichedFunctorCat V I) (𝟙_ I)
    (Free.unitCoefficientIso (𝟙_ I))
  have hm := congrArg (fun f => Free.evaluate (𝟙_ I) (𝟙_ V)
    (⟨S⟩ : EnrichedFunctorCat V I) ((Free.unitCoefficientIso (𝟙_ I)).hom ≫ f))
      (LaxMonoid.monObj_one d S L)
  exact hu.trans (hm.trans (representedUnit_evaluation d S L))

/-- The complete original source-unit equation, with the exact genuine Day and sphere factories. -/
def SourceUnitEpsilonProperty : Prop :=
  letI := ColimitMonoidal.monoidalCategory d
  letI := LaxMonoid.monObj d S L
  UnitSource.SourceUnitEpsilonProperty (⟨S⟩ : EnrichedFunctorCat V I) (𝟙_ I)
    (Free.unitCoefficientIso (𝟙_ I)) L.epsilon

/-- Both actual free units and the original lax unit prove this complete predicate. -/
theorem sourceUnit_epsilon_spec : SourceUnitEpsilonProperty d S L := sourceUnit_epsilon d S L

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.LambdaUnitSource.DayUnitSource

open CategoryTheory.Spectra CategoryTheory.Spectra.OrthogonalSourceRightModule

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.LambdaUnitSource.FreeStage

universe uV vV uI
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I]

theorem stabilization_evaluate (a b : I) (K : V) (D : K ⟶ (a ⟶[V] b))
    (F : EnrichedFunctorCat V I) (q : Free.object a (𝟙_ V) ⟶ F) :
    Free.evaluate b K F (CurrentFree.stabilization a b K D ≫ q) =
      (λ_ K).inv ≫ (Free.evaluate a (𝟙_ V) F q ⊗ₘ D) ≫
        MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b) := by
  let H := a ⟶[V] b
  let e := Free.evaluate a (𝟙_ V) F q
  let act := MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b)
  have hs := CurrentFree.stabilization_adjunct a b K D
  rw [Free.adjunction_homEquiv] at hs
  have he : Free.evaluate b K (Free.object a (𝟙_ V)) (CurrentFree.stabilization a b K D) =
      D ≫ (λ_ H).inv := hs
  have hpost := Free.evaluate_postcomp b K (CurrentFree.stabilization a b K D) q
  have hcomp := Free.reconstruct_component a (𝟙_ V) F q b
  change component q b = (e ⊗ₘ 𝟙 H) ≫ act at hcomp
  have hpad : D ≫ (λ_ H).inv ≫ (e ⊗ₘ 𝟙 H) = (λ_ K).inv ≫ (e ⊗ₘ D) := by
    rw [← Category.assoc, leftUnitor_inv_naturality, Category.assoc,
      tensorHom_id, ← tensorHom_def']
  exact hpost.trans
    ((congrArg (fun f => f ≫ component q b) he).trans
      ((congrArg (fun f => (D ≫ (λ_ H).inv) ≫ f) hcomp).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun f => f ≫ act)
            ((Category.assoc _ _ _).trans hpad)).trans (Category.assoc _ _ _)))))

theorem stabilization_evaluate_action (a b : I) (K : V) (D : K ⟶ (a ⟶[V] b))
    (F : EnrichedFunctorCat V I) (q : Free.object a (𝟙_ V) ⟶ F) :
    Free.evaluate b K F (CurrentFree.stabilization a b K D ≫ q) =
      (λ_ K).inv ≫ (Free.evaluate a (𝟙_ V) F q ▷ K) ≫
        (F.toEnrichedFunctor.obj a ◁ D) ≫
          MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b) := by
  have h := stabilization_evaluate a b K D F q
  rw [tensorHom_def, Category.assoc] at h
  exact h

theorem evaluate_reindex {a b : I} (h : a = b) (X : V) (F : EnrichedFunctorCat V I)
    (g : Free.object b X ⟶ F) :
    Free.evaluate a X F (eqToHom (congrArg (fun a => Free.object a X) h) ≫ g) =
      Free.evaluate b X F g ≫ eqToHom (congrArg F.toEnrichedFunctor.obj h.symm) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

omit [MonoidalCategory V] [BraidedCategory V] [MonoidalClosed V] in
theorem sourceWord_inverse {A B D T : V} (f : A ⟶ B) (g : B ⟶ D) (k : D ⟶ T)
    (e : T ≅ A) (h : f ≫ g ≫ k ≫ e.hom = 𝟙 A) : f ≫ g ≫ k = e.inv := by
  apply (Iso.comp_hom_eq_id e).mp
  simpa only [Category.assoc] using h

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.LambdaUnitSource.FreeStage

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.LambdaUnitSource.RegularEvaluation

open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK

attribute [local instance] OrthogonalIndex.category OrthogonalIndex.monoidalCategory
  OrthogonalIndex.enrichedOrdinaryCategory OrthogonalIndex.symmetricCategory
  MonoidalLeftAction.monoidalOppositeLeftAction Enriched.prodCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits

/-- Day convolution on pointed enriched functors from the orthogonal index. -/
local instance : MonoidalCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) :=
  OrthogonalDay.monoidalCategory.{u, v}
/-- The symmetry of orthogonal Day convolution induced by the index block swap. -/
local instance : SymmetricCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) :=
  OrthogonalDay.symmetricCategory.{u, v}
/-- The closed structure on orthogonal Day convolution from the original enriched monoidal index
data. -/
local instance : MonoidalClosed (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) :=
  EnrichedDayKernel.Closed.monoidalClosed OrthogonalIndex.enrichedMonoidalData.{u, v}
/-- The sphere-diagram monoid under orthogonal Day convolution. -/
local instance : MonObj sphereISpace.{u, v} := OrthogonalDay.sphereMonObj.{u, v}
local instance : IsCommMonObj sphereISpace.{u, v} := OrthogonalDay.sphereIsCommMonObj.{u, v}

/-- The regular right module over the orthogonal sphere diagram. -/
abbrev regularSource := RightModuleFree.regularObject sphereISpace.{u, v}
/-- The native orthogonal spectrum corresponding to the regular sphere module under the original
source equivalence. -/
abbrev regularNative :=
  CanonicalSourceRightModuleEquivalence.equivalence.{u, v}.symm.functor.obj regularSource.{u, v}

theorem inverseUnit_epsilon :
    Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} 0) (𝟙_ PointedCGWH.{u, v})
      regularNative.{u, v}
      CanonicalSourceRightModuleFreeUnit.regularSphereNativeFreeIso.{u, v}.inv =
      orthogonalSphereMonoidalData.{u, v}.epsilon := by
  have h := UnitSource.inverseUnit_epsilon_spec sphereISpace.{u, v}
    CanonicalSourceRightModuleEquivalence.equivalence.{u, v}.symm (0 : OrthogonalIndex)
    (OrthogonalOperatorIndex.ofIndex.{u, v} 0)
    CanonicalSourceRightModuleFreeUnit.freeUnitISpaceIso.{u, v}
    (CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v} 0)
    orthogonalSphereMonoidalData.{u, v}.epsilon
    (DayUnitSource.sourceUnit_epsilon_spec OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v})
  change Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} 0) (𝟙_ PointedCGWH.{u, v})
      regularNative.{u, v}
      CanonicalSourceRightModuleFreeUnit.regularSphereNativeFreeIso.{u, v}.inv ≫
        (CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v} 0).hom.app
          regularSource.{u, v} = orthogonalSphereMonoidalData.{u, v}.epsilon at h
  rw [CanonicalSourceRightModuleFreeEvaluation.evaluationComparison_hom_app] at h
  exact (Category.comp_id
    (Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} 0) (𝟙_ PointedCGWH.{u, v})
      regularNative.{u, v}
      CanonicalSourceRightModuleFreeUnit.regularSphereNativeFreeIso.{u, v}.inv)).symm.trans h

theorem inverseUnit_extension :
    CanonicalSourceRightModuleFreeUnit.regularSphereNativeFreeIso.{u, v}.inv =
      Free.extend (OrthogonalOperatorIndex.ofIndex.{u, v} 0) (𝟙_ PointedCGWH.{u, v})
        regularNative.{u, v} orthogonalSphereMonoidalData.{u, v}.epsilon := by
  have h := Free.extend_evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} 0)
    (𝟙_ PointedCGWH.{u, v}) regularNative.{u, v}
    CanonicalSourceRightModuleFreeUnit.regularSphereNativeFreeIso.{u, v}.inv
  rw [inverseUnit_epsilon] at h
  exact h.symm

theorem sphereComponent (n a : OrthogonalIndex) :
    NativeSphereModule.sphereComponent regularSource.{u, v} n a =
      orthogonalSphereMonoidalData.{u, v}.mu n a := by
  have hp := NativeSphereModule.sphereComponent_day_point regularSource.{u, v} n a
  have hm := congrArg (fun f => EnrichedDayKernel.Generators.point
    OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
    orthogonalSphereFunctor.{u, v} orthogonalSphereFunctor.{u, v} (n, a) ≫
      component f (n + a)) (RightModuleFree.regularObject_action sphereISpace.{u, v})
  have hu := EnrichedDayKernel.LaxMonoid.unitGenerator_multiply
    OrthogonalIndex.enrichedMonoidalData.{u, v} orthogonalSphereFunctor.{u, v}
    orthogonalSphereMonoidalData.{u, v} (n, a)
  exact hp.trans (hm.trans hu)

theorem sphereComponent_leftUnit (n : OrthogonalIndex) :
    (orthogonalSphereMonoidalData.{u, v}.epsilon ▷ PointedCGWH.orthogonalSphere.{u, v} n) ≫
        NativeSphereModule.sphereComponent regularSource.{u, v} 0 n ≫
          orthogonalSphereFunctor.{u, v}.toOrdinaryFunctor.map (λ_ n).hom =
      (λ_ (PointedCGWH.orthogonalSphere.{u, v} n)).hom := by
  have hm := sphereComponent.{u, v} 0 n
  exact (congrArg (fun f =>
    (orthogonalSphereMonoidalData.{u, v}.epsilon ▷ PointedCGWH.orthogonalSphere.{u, v} n) ≫
      f ≫ orthogonalSphereFunctor.{u, v}.toOrdinaryFunctor.map (λ_ n).hom) hm).trans
        (orthogonalSphereMonoidalData.{u, v}.unit n).1.symm

theorem sphereCoordinateIso_finCongr {m n : ℕ} (h : m = n) :
    orthogonalSphereCoordinateIso.{u, v} (finCongr h) =
      eqToIso (congrArg (PointedCGWH.orthogonalSphere.{u, v}) h) := by
  cases h
  apply Iso.ext
  apply Under.UnderMorphism.ext
  apply ConcreteCategory.hom_ext
  intro z
  induction z using OnePoint.rec with
  | infty => rfl
  | coe x =>
      rcases x with ⟨x⟩
      change ((ULift.up (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
          (finCongr (rfl : m = m)) x) :
          ULift.{v, 0} (EuclideanSpace ℝ (Fin m))) :
            OnePoint (ULift.{v, 0} (EuclideanSpace ℝ (Fin m)))) =
        ((ULift.up x : ULift.{v, 0} (EuclideanSpace ℝ (Fin m))) :
          OnePoint (ULift.{v, 0} (EuclideanSpace ℝ (Fin m))))
      apply congrArg (fun y : EuclideanSpace ℝ (Fin m) =>
        ((ULift.up y : ULift.{v, 0} (EuclideanSpace ℝ (Fin m))) :
          OnePoint (ULift.{v, 0} (EuclideanSpace ℝ (Fin m)))))
      ext j
      rfl

theorem sphere_leftUnitor_image (n : OrthogonalIndex) :
    orthogonalSphereFunctor.{u, v}.toOrdinaryFunctor.map (λ_ n).hom =
      eqToHom (congrArg (PointedCGWH.orthogonalSphere.{u, v}) (Nat.zero_add n)) := by
  change orthogonalSphereMap.{u, v} (λ_ n).hom = _
  exact (orthogonalSphereMap_leftUnitor n).trans
    (congrArg Iso.hom (sphereCoordinateIso_finCongr (Nat.zero_add n)))

theorem stabilization_evaluate (n : ℕ) :
    Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} (0 + n))
        (PointedCGWH.orthogonalSphere.{u, v} n) regularNative.{u, v}
        (Actual.orthogonalStabilization.{u, v} 0 n ≫
            CanonicalSourceRightModuleFreeUnit.regularSphereNativeFreeIso.{u, v}.inv) =
      (λ_ (PointedCGWH.orthogonalSphere.{u, v} n)).inv ≫
        (orthogonalSphereMonoidalData.{u, v}.epsilon ▷
          PointedCGWH.orthogonalSphere.{u, v} n) ≫
        NativeSphereModule.sphereComponent regularSource.{u, v} 0 n := by
  have h := FreeStage.stabilization_evaluate_action
    (OrthogonalOperatorIndex.ofIndex.{u, v} 0)
    (OrthogonalOperatorIndex.ofIndex.{u, v} (0 + n))
    (PointedCGWH.orthogonalSphere.{u, v} n) (OrthogonalOperatorIndex.nu.{u, v} 0 n)
    regularNative.{u, v} CanonicalSourceRightModuleFreeUnit.regularSphereNativeFreeIso.{u, v}.inv
  rw [inverseUnit_epsilon] at h
  have ha : sphereAction regularNative.{u, v} 0 n =
      NativeSphereModule.sphereComponent regularSource.{u, v} 0 n :=
    CanonicalSourceRightModuleActions.fromModule_sphereAction regularSource.{u, v} 0 n
  have hn := sphereAction_original_nu regularNative.{u, v} 0 n
  exact h.trans
    (congrArg (fun f => (λ_ (PointedCGWH.orthogonalSphere.{u, v} n)).inv ≫
      (orthogonalSphereMonoidalData.{u, v}.epsilon ▷
        PointedCGWH.orthogonalSphere.{u, v} n) ≫ f) (hn.symm.trans ha))

theorem stabilization_evaluate_identity (n : ℕ) :
    Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} (0 + n))
        (PointedCGWH.orthogonalSphere.{u, v} n) regularNative.{u, v}
        (Actual.orthogonalStabilization.{u, v} 0 n ≫
          CanonicalSourceRightModuleFreeUnit.regularSphereNativeFreeIso.{u, v}.inv) =
      eqToHom (congrArg (PointedCGWH.orthogonalSphere.{u, v}) (Nat.zero_add n).symm) := by
  have hu := sphereComponent_leftUnit.{u, v} n
  rw [sphere_leftUnitor_image] at hu
  have hp := (congrArg (fun f => (λ_ (PointedCGWH.orthogonalSphere.{u, v} n)).inv ≫ f)
    hu).trans (Iso.inv_hom_id (λ_ (PointedCGWH.orthogonalSphere.{u, v} n)))
  change (λ_ (PointedCGWH.orthogonalSphere.{u, v} n)).inv ≫
    (orthogonalSphereMonoidalData.{u, v}.epsilon ▷ PointedCGWH.orthogonalSphere.{u, v} n) ≫
    NativeSphereModule.sphereComponent regularSource.{u, v} 0 n ≫
    eqToHom (congrArg (PointedCGWH.orthogonalSphere.{u, v}) (Nat.zero_add n)) =
      𝟙 (PointedCGWH.orthogonalSphere.{u, v} n) at hp
  have hc : (λ_ (PointedCGWH.orthogonalSphere.{u, v} n)).inv ≫
      (orthogonalSphereMonoidalData.{u, v}.epsilon ▷ PointedCGWH.orthogonalSphere.{u, v} n) ≫
      NativeSphereModule.sphereComponent regularSource.{u, v} 0 n =
        eqToHom (congrArg (PointedCGWH.orthogonalSphere.{u, v}) (Nat.zero_add n).symm) := by
    exact FreeStage.sourceWord_inverse
      (λ_ (PointedCGWH.orthogonalSphere.{u, v} n)).inv
      (orthogonalSphereMonoidalData.{u, v}.epsilon ▷ PointedCGWH.orthogonalSphere.{u, v} n)
      (NativeSphereModule.sphereComponent regularSource.{u, v} 0 n)
      (eqToIso (congrArg (PointedCGWH.orthogonalSphere.{u, v}) (Nat.zero_add n))) hp
  exact (stabilization_evaluate n).trans hc

/-- The original zero-source stabilization transported to the free sphere source and regular
native target. -/
def regularGamma (n : ℕ) : sphereFree.{u, v} n ⟶ regularNative.{u, v} :=
  (gammaSourceIso.{u, v} n).hom ≫ Actual.orthogonalStabilization.{u, v} 0 n ≫
    CanonicalSourceRightModuleFreeUnit.regularSphereNativeFreeIso.{u, v}.inv

theorem regularGamma_evaluate (n : ℕ) :
    Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} n)
        (PointedCGWH.orthogonalSphere.{u, v} n) regularNative.{u, v}
        (regularGamma.{u, v} n) = 𝟙 (PointedCGWH.orthogonalSphere.{u, v} n) := by
  have h := FreeStage.evaluate_reindex
    (congrArg (OrthogonalOperatorIndex.ofIndex.{u, v}) (Nat.zero_add n).symm)
    (PointedCGWH.orthogonalSphere.{u, v} n) regularNative.{u, v}
    (Actual.orthogonalStabilization.{u, v} 0 n ≫
      CanonicalSourceRightModuleFreeUnit.regularSphereNativeFreeIso.{u, v}.inv)
  rw [stabilization_evaluate_identity] at h
  have hc : eqToHom (congrArg (PointedCGWH.orthogonalSphere.{u, v}) (Nat.zero_add n).symm) ≫
      eqToHom (congrArg (PointedCGWH.orthogonalSphere.{u, v}) (Nat.zero_add n)) =
      𝟙 (PointedCGWH.orthogonalSphere.{u, v} n) := by
    rw [eqToHom_trans, eqToHom_refl]
  exact h.trans hc

theorem regularGamma_eq_extend (n : ℕ) :
    regularGamma.{u, v} n = Free.extend (OrthogonalOperatorIndex.ofIndex.{u, v} n)
      (PointedCGWH.orthogonalSphere.{u, v} n) regularNative.{u, v}
      (𝟙 (PointedCGWH.orthogonalSphere.{u, v} n)) := by
  have h := Free.extend_evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} n)
    (PointedCGWH.orthogonalSphere.{u, v} n) regularNative.{u, v} (regularGamma.{u, v} n)
  rw [regularGamma_evaluate] at h
  exact h.symm

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.LambdaUnitSource.RegularEvaluation

universe uMates vMates

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.OriginalUnitMates

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
variable {C : Type uMates} [Category.{vMates} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [CategoryTheory.Limits.HasEqualizers C]
  [CategoryTheory.Limits.HasCoequalizers C] (R : C) [MonObj R] [IsCommMonObj R]

theorem regularEvaluation_leftMate (N : CommutativeModuleConversion.RightModule R) :
    letI := RightModuleFree.tensorMonoidal R
    letI := RightModuleFree.tensorSymmetric R
    (tensorLeft (RightModuleFree.regularObject R)).map
        ((RightModuleMappingEnd.Regular.regularMappingNatIso R).inv.app N) ≫
        (RightModuleMappingEnd.leftAdjunction R (RightModuleFree.regularObject R)).counit.app N =
      (β_ (RightModuleFree.regularObject R) N).hom ≫
        (RightModuleMappingEnd.Regular.regularTensorIso R).hom.app N := by
  let := RightModuleFree.tensorMonoidal R
  let := RightModuleFree.tensorSymmetric R
  have h := RightModuleMappingEnd.Regular.regularMappingIso_inv_mate R N
  have hp := congrArg (fun f => (β_ (RightModuleFree.regularObject R) N).hom ≫ f) h
  change (β_ (RightModuleFree.regularObject R) N).hom ≫
      ((RightModuleMappingEnd.Regular.regularMappingNatIso R).inv.app N ▷
        RightModuleFree.regularObject R) ≫
      (β_ (RightModuleFree.regularObject R)
        ((RightModuleMappingEnd.functor R (RightModuleFree.regularObject R)).obj N)).inv ≫
      (RightModuleMappingEnd.leftAdjunction R
        (RightModuleFree.regularObject R)).counit.app N = _ at hp
  rw [← braiding_naturality_right_assoc, Iso.hom_inv_id_assoc] at hp
  exact hp

theorem regularEvaluation_leftUnitorMate
    (N : CommutativeModuleConversion.RightModule R) :
    letI := RightModuleFree.tensorMonoidal R
    letI := RightModuleFree.tensorSymmetric R
    (tensorLeft (RightModuleFree.regularObject R)).map
        ((RightModuleMappingEnd.Regular.regularMappingNatIso R).inv.app N) ≫
        (RightModuleMappingEnd.leftAdjunction R (RightModuleFree.regularObject R)).counit.app N =
      ((RightModuleFree.regularTensorUnitIso R).hom ▷ N) ≫ (λ_ N).hom := by
  let := RightModuleFree.tensorMonoidal R
  let := RightModuleFree.tensorSymmetric R
  have h := regularEvaluation_leftMate R N
  change _ = (β_ (RightModuleFree.regularObject R) N).hom ≫
    (N ◁ (RightModuleFree.regularTensorUnitIso R).hom) ≫ (ρ_ N).hom at h
  rw [← braiding_naturality_left_assoc, braiding_rightUnitor] at h
  exact h

theorem sourceCoaugmentation_uncurry
    {M : CommutativeModuleConversion.RightModule R}
    (f : M ⟶ RightModuleFree.regularObject R)
    (N : CommutativeModuleConversion.RightModule R) :
    letI := RightModuleFree.tensorMonoidal R
    letI := RightModuleFree.tensorSymmetric R
    (tensorLeft M).map ((Ambient.sourceCoaugmentation R f).app N) ≫
      (RightModuleMappingEnd.leftAdjunction R M).counit.app N =
        ((f ≫ (RightModuleFree.regularTensorUnitIso R).hom) ▷ N) ≫ (λ_ N).hom := by
  let := RightModuleFree.tensorMonoidal R
  let := RightModuleFree.tensorSymmetric R
  change (tensorLeft M).map
      ((RightModuleMappingEnd.Regular.regularMappingNatIso R).inv.app N ≫
        RightModuleMappingEnd.sourceMap R f N) ≫
      (RightModuleMappingEnd.leftAdjunction R M).counit.app N = _
  rw [Functor.map_comp, Category.assoc, Ambient.sourceMapCounit]
  change M ◁ (RightModuleMappingEnd.Regular.regularMappingNatIso R).inv.app N ≫
      f ▷ (RightModuleMappingEnd.functor R (RightModuleFree.regularObject R)).obj N ≫
      (RightModuleMappingEnd.leftAdjunction R
        (RightModuleFree.regularObject R)).counit.app N = _
  rw [whisker_exchange_assoc]
  have h := regularEvaluation_leftUnitorMate R N
  change (RightModuleFree.regularObject R) ◁
      (RightModuleMappingEnd.Regular.regularMappingNatIso R).inv.app N ≫
      (RightModuleMappingEnd.leftAdjunction R
        (RightModuleFree.regularObject R)).counit.app N = _ at h
  rw [h]
  change (f ▷ N) ≫ ((RightModuleFree.regularTensorUnitIso R).hom ▷ N) ≫ (λ_ N).hom =
    ((f ≫ (RightModuleFree.regularTensorUnitIso R).hom) ▷ N) ≫ (λ_ N).hom
  simp only [comp_whiskerRight, Category.assoc]

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.OriginalUnitMates

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.SourceTransport

universe uD vD
variable {C : Type uMates} [Category.{vMates} C] [MonoidalCategory C]
  {D : Type uD} [Category.{vD} D]
  (E : C ≌ D) (R : C → C ⥤ C) (h : ∀ M : C, tensorLeft M ⊣ R M)

theorem transportedSourceUnitor (A X : D) :
    letI := Monoidal.transport E
    ∀ l : A ⟶ 𝟙_ D,
      (l ▷ X) ≫ (λ_ X).hom =
        E.functor.map
          (((E.inverse.map l ≫ E.unitIso.inv.app (𝟙_ C)) ▷ E.inverse.obj X) ≫
            (λ_ (E.inverse.obj X)).hom) ≫ E.counitIso.hom.app X := by
  let := Monoidal.transport E
  intro l
  change E.functor.map (E.inverse.map l ▷ E.inverse.obj X) ≫
      (E.functor.map
        ((E.unitIso.inv.app (𝟙_ C) ▷ E.inverse.obj X) ≫ (λ_ (E.inverse.obj X)).hom) ≫
          E.counitIso.hom.app X) = _
  simp only [comp_whiskerRight, Functor.map_comp, Category.assoc]

theorem carriedSourceUnitorMate (A X : D)
    (g : E.inverse.obj X ⟶ (R (E.inverse.obj A)).obj (E.inverse.obj X)) :
    letI := Monoidal.transport E
    ∀ l : A ⟶ 𝟙_ D,
      ((h (E.inverse.obj A)).homEquiv (E.inverse.obj X) (E.inverse.obj X)).symm g =
          ((E.inverse.map l ≫ E.unitIso.inv.app (𝟙_ C)) ▷ E.inverse.obj X) ≫
            (λ_ (E.inverse.obj X)).hom →
      ((CanonicalSourceSmashClosed.Primitive.adjunction E R h A).homEquiv X X).symm
        (E.counitIso.inv.app X ≫ E.functor.map g) = (l ▷ X) ≫ (λ_ X).hom := by
  let := Monoidal.transport E
  intro l hg
  have hCarry : E.counitIso.inv.app X ≫ E.functor.map g =
      (E.symm.toAdjunction.homEquiv X
        ((R (E.inverse.obj A)).obj (E.inverse.obj X))) g := by
    rw [Adjunction.homEquiv_unit]
    rfl
  change (((E.symm.toAdjunction.comp (h (E.inverse.obj A))).comp E.toAdjunction).homEquiv
    X X).symm _ = _
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  change (E.toAdjunction.homEquiv (E.inverse.obj A ⊗ E.inverse.obj X) X).symm
      (((h (E.inverse.obj A)).homEquiv (E.inverse.obj X) (E.inverse.obj X)).symm
        ((E.symm.toAdjunction.homEquiv X
          ((R (E.inverse.obj A)).obj (E.inverse.obj X))).symm
            (E.counitIso.inv.app X ≫ E.functor.map g))) = _
  rw [hCarry, Equiv.symm_apply_apply, hg, Adjunction.homEquiv_counit]
  exact (transportedSourceUnitor E A X l).symm

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.SourceTransport

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.CoefficientPowers

/-- The original sphere-one coefficient maps give both actual one-loop maps. -/
def firstFunctionIso : ihom (PointedCGWH.orthogonalSphere.{u, v} 1) ≅ PointedCGWH.loop.{u, v} :=
  MonoidalClosed.internalHom.mapIso orthogonalOneSphereIsoSphereOne.{u, v}.symm.op

/-- The original sphere tensorators and sphere-zero unit construct all coefficient currying maps. -/
def sphereFunctionIterationIso (n : ℕ) :
    ihom (PointedCGWH.orthogonalSphere.{u, v} n) ≅
      Functor.Iteration.iterate (ihom (PointedCGWH.orthogonalSphere.{u, v} 1)) n :=
  Powers.FreeFamily.functionIso (PointedCGWH.orthogonalSphere.{u, v} 1)
    PointedCGWH.orthogonalSphere.{u, v} PointedCGWH.orthogonalSphereUnitIso.{u, v}
    (fun n => (NativePowers.spherePrefixIso.{u, v} n).symm) n

/-- Every loop-power comparison is independently constructed
from the actual sphere coefficient maps. -/
def sphereLoopPowerIso (n : ℕ) :
    ihom (PointedCGWH.orthogonalSphere.{u, v} n) ≅ LoopPowerAtPoints.power.{u, v} n :=
  sphereFunctionIterationIso n ≪≫ Functor.Iteration.iterateIso firstFunctionIso n

theorem firstFunctionIso_hom_app (X : PointedCGWH.{u, v}) :
    firstFunctionIso.{u, v}.hom.app X =
      (MonoidalClosed.pre orthogonalOneSphereIsoSphereOne.{u, v}.inv).app X := rfl

theorem firstFunctionIso_inv_app (X : PointedCGWH.{u, v}) :
    firstFunctionIso.{u, v}.inv.app X =
      (MonoidalClosed.pre orthogonalOneSphereIsoSphereOne.{u, v}.hom).app X := rfl

theorem sphereLoopPowerIso_hom_naturality (n : ℕ)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (ihom (PointedCGWH.orthogonalSphere n)).map f ≫ (sphereLoopPowerIso n).hom.app Y =
      (sphereLoopPowerIso n).hom.app X ≫ (LoopPowerAtPoints.power n).map f :=
  (sphereLoopPowerIso n).hom.naturality f

theorem sphereLoopPowerIso_inv_naturality (n : ℕ)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (LoopPowerAtPoints.power n).map f ≫ (sphereLoopPowerIso n).inv.app Y =
      (sphereLoopPowerIso n).inv.app X ≫ (ihom (PointedCGWH.orthogonalSphere n)).map f :=
  (sphereLoopPowerIso n).inv.naturality f

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.CoefficientPowers
