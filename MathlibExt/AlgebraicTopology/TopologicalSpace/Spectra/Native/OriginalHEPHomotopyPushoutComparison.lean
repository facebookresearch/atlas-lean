/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.RelativeCylinder
import MathlibExt.CategoryTheory.Monoidal.IntervalActionProjection
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OmegaTestHomotopyCofiberClosure
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.MappingCylinderLevelSDR

/-!
# Relative homotopies for the original native mapping cylinder

All-target homotopy extension constructs the inverse and both relative
homotopies for the original cylinder. The source endpoint, target inclusion,
projection and whole time maps are the original ones. The comparison to an
arbitrary pushout must retain its actual cocone. A level weak comparison of
arbitrary badly based span replacements is a separate mathematical obligation.
-/

set_option autoImplicit false
noncomputable section
universe u v uC vC

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory MonoidalClosed


namespace PointedCGWH.Spectra.OriginalHEPHomotopyPushoutComparison

open PointedCGWH.Spectra.NativeOmegaWeakClosure

/-- Reflection acts on the entire original freely based time coefficient. -/
def literalCoefficientReflection : PointedCGWH.RealizedIntervalContraction.time.{u, v} ≅
    PointedCGWH.RealizedIntervalContraction.time.{u, v} :=
  (Under.costar CGWH.point.{u, v}).mapIso CGWH.literalTimeReflection

/-- The whole literal endpoint family is carried to its actual reflected time. -/
@[reassoc]
theorem literalCoefficientReflection_endpoint (t : unitInterval) :
    PointedCGWH.freePointIntervalEndpoint.{u, v} t ≫ literalCoefficientReflection.hom =
      PointedCGWH.freePointIntervalEndpoint.{u, v} (unitInterval.symm t) := by
  let F := Under.costar CGWH.point.{u, v}
  let hF : F.CoreMonoidal := CategoryTheory.Pointed.costarCoreMonoidal
    CGWH.point CGWH.point_isTerminal
  change (hF.εIso.hom ≫ F.map (CGWH.homotopyIntervalEndpoint t)) ≫
      F.map CGWH.literalTimeReflection.hom =
    hF.εIso.hom ≫ F.map (CGWH.homotopyIntervalEndpoint (unitInterval.symm t))
  rw [Category.assoc, ← F.map_comp, CGWH.literalTimeReflection_endpoint]

/-- Both complete maps reflect the actual original realized interval coefficient. -/
def originalCoefficientReflection : PointedCGWH.IntervalCoefficient.interval.{u, v} ≅
    PointedCGWH.IntervalCoefficient.interval.{u, v} :=
  originalTimeCoefficientIso.symm ≪≫ literalCoefficientReflection ≪≫ originalTimeCoefficientIso

/-- Reflection sends the original first realized endpoint to the original second endpoint. -/
@[reassoc]
theorem originalCoefficientReflection_zero :
    PointedCGWH.IntervalCoefficient.endpoint.{u, v} 0 ≫ originalCoefficientReflection.hom =
      PointedCGWH.IntervalCoefficient.endpoint.{u, v} 1 := by
  rw [← originalTimeCoefficientIso_zero]
  change (PointedCGWH.freePointIntervalEndpoint 0 ≫ originalTimeCoefficientIso.hom) ≫
      (originalTimeCoefficientIso.inv ≫ literalCoefficientReflection.hom ≫
        originalTimeCoefficientIso.hom) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc, literalCoefficientReflection_endpoint_assoc,
    unitInterval.symm_zero, originalTimeCoefficientIso_one]

/-- Reflection sends the original second realized endpoint to the original first endpoint. -/
@[reassoc]
theorem originalCoefficientReflection_one :
    PointedCGWH.IntervalCoefficient.endpoint.{u, v} 1 ≫ originalCoefficientReflection.hom =
      PointedCGWH.IntervalCoefficient.endpoint.{u, v} 0 := by
  rw [← originalTimeCoefficientIso_one]
  change (PointedCGWH.freePointIntervalEndpoint 1 ≫ originalTimeCoefficientIso.hom) ≫
      (originalTimeCoefficientIso.inv ≫ literalCoefficientReflection.hom ≫
        originalTimeCoefficientIso.hom) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc, literalCoefficientReflection_endpoint_assoc,
    unitInterval.symm_one, originalTimeCoefficientIso_zero]

/-- The full original coefficient reflection preserves its actual augmentation. -/
@[reassoc]
theorem originalCoefficientReflection_augmentation :
    originalCoefficientReflection.hom ≫ PointedCGWH.IntervalCoefficient.augmentation.{u, v} =
      PointedCGWH.IntervalCoefficient.augmentation.{u, v} := by
  let F := Under.costar CGWH.point.{u, v}
  let e := CGWH.literalTimeReflection.{u, v} ≪≫ CGWH.homotopyIntervalIsoInterval.{u, v}
  rw [PointedCGWH.RealizedIntervalContraction.augmentation_eq]
  change (F.map e.inv ≫ F.map CGWH.literalTimeReflection.hom ≫ F.map e.hom) ≫
      F.map CGWH.intervalAugmentation = F.map CGWH.intervalAugmentation
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg F.map (CGWH.point_isTerminal.hom_ext
      (e.inv ≫ CGWH.literalTimeReflection.hom ≫ e.hom ≫ CGWH.intervalAugmentation)
      CGWH.intervalAugmentation)

/-- The original free-point monoidal data uses the same native Cartesian source structure. -/
def originalFreeMonoidalCore : (Under.costar CGWH.point.{u, v}).CoreMonoidal := by
  let _ : BraidedCategory CGWH.{u, v} := BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  exact CategoryTheory.Pointed.costarCoreMonoidal CGWH.point CGWH.point_isTerminal

/-- The original realized augmentation is the actual strong-monoidal image of its terminal map. -/
theorem originalAugmentation_collapseImage :
    Functor.CoreMonoidal.intervalCollapseImage (Under.costar CGWH.point.{u, v})
        originalFreeMonoidalCore (CartesianMonoidalCategory.toUnit CGWH.interval.{u, v}) =
      PointedCGWH.IntervalCoefficient.augmentation.{u, v} := by
  let F := Under.costar CGWH.point.{u, v}
  let hF := originalFreeMonoidalCore.{u, v}
  have hi : F.map (CGWH.point_isTerminal.from (𝟙_ CGWH.{u, v})) = hF.εIso.inv := by
    change F.map (CGWH.point_isTerminal.from (𝟙_ CGWH.{u, v})) =
      ((Under.costarAdjForget CGWH.point).homEquiv (𝟙_ CGWH) (F.obj CGWH.point)).symm
        (CGWH.point_isTerminal.from (𝟙_ CGWH.{u, v}) ≫ coprod.inr)
    apply ((Under.costarAdjForget CGWH.point).homEquiv
      (𝟙_ CGWH) (F.obj CGWH.point)).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    have hu : (Under.costarAdjForget CGWH.point.{u, v}).unit.app (𝟙_ CGWH) =
        (coprod.inr : (𝟙_ CGWH) ⟶ CGWH.point ⨿ (𝟙_ CGWH)) := rfl
    rw [hu]
    change coprod.inr ≫ coprod.map (𝟙 CGWH.point)
      (CGWH.point_isTerminal.from (𝟙_ CGWH.{u, v})) = _
    exact coprod.inr_map _ _
  let invUnit : F.obj (𝟙_ CGWH.{u, v}) ⟶ F.obj CGWH.point := hF.εIso.inv
  have hInv : F.map (CGWH.point_isTerminal.from (𝟙_ CGWH.{u, v})) = invUnit := hi
  have hCanonical : F.map (CartesianMonoidalCategory.toUnit CGWH.interval) ≫ invUnit =
      F.map CGWH.intervalAugmentation := by
    rw [← hInv, ← F.map_comp]
    exact congrArg F.map (CGWH.point_isTerminal.hom_ext _ _)
  exact hCanonical.trans (PointedCGWH.RealizedIntervalContraction.augmentation_eq).symm

/-- The actual original pointed interval action preserves the whole original collapse. -/
theorem originalAction_augmentation :
    PointedCGWH.RealizedIntervalContraction.action.{u, v} ≫
        PointedCGWH.IntervalCoefficient.augmentation.{u, v} =
      (PointedCGWH.freePointIntervalCollapse.{u, v} ⊗ₘ
        PointedCGWH.IntervalCoefficient.augmentation.{u, v}) ≫
          (λ_ (𝟙_ PointedCGWH.{u, v})).hom := by
  let F := Under.costar CGWH.point.{u, v}
  let hF := originalFreeMonoidalCore.{u, v}
  let cT := CartesianMonoidalCategory.toUnit CGWH.homotopyInterval.{u, v}
  let cJ := CartesianMonoidalCategory.toUnit CGWH.interval.{u, v}
  have h : CGWH.RealizedIntervalContraction.action ≫ cJ =
      (cT ⊗ₘ cJ) ≫ (λ_ (𝟙_ CGWH.{u, v})).hom :=
    CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _
  have hp := Functor.CoreMonoidal.intervalActionImage_collapse F hF
    CGWH.RealizedIntervalContraction.action cT cJ h
  have hJ : Functor.CoreMonoidal.intervalCollapseImage F hF cJ =
      PointedCGWH.IntervalCoefficient.augmentation := originalAugmentation_collapseImage
  have hT : Functor.CoreMonoidal.intervalCollapseImage F hF cT =
      PointedCGWH.freePointIntervalCollapse := rfl
  have hA : Functor.CoreMonoidal.intervalActionImage F hF
      CGWH.RealizedIntervalContraction.action =
        PointedCGWH.RealizedIntervalContraction.action := rfl
  rw [hA, hJ, hT] at hp
  exact hp

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
attribute [local instance] MonoidalClosed.enrichedCategorySelf
  PointedCGWH.EnrichedMapping.hasSmallLimits
open PointedCGWH.EnrichedIntervalContraction PointedCGWH.EnrichedIntervalCylinder

/-- Reflection is the actual scalar isomorphism on every original native interval. -/
def originalIntervalReflection : EnrichedIntervalCylinder.functor (I := I) ≅
    EnrichedIntervalCylinder.functor (I := I) :=
  (EnrichedFunctorCat.tensorBifunctor (V := PointedCGWH.{u, v}) (A := I)).mapIso
    originalCoefficientReflection

/-- The full original scalar reflection keeps its actual coefficient map. -/
theorem originalIntervalReflection_hom (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (originalIntervalReflection (I := I)).hom.app X =
      scalarTensorMap originalCoefficientReflection.hom X := rfl

/-- The full inverse scalar reflection keeps its actual inverse coefficient map. -/
theorem originalIntervalReflection_inv (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (originalIntervalReflection (I := I)).inv.app X =
      scalarTensorMap originalCoefficientReflection.inv X := rfl

/-- The entire first original native endpoint reflects to the second endpoint. -/
@[reassoc]
theorem originalIntervalReflection_zero (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    inclusion 0 X ≫ (originalIntervalReflection (I := I)).hom.app X = inclusion 1 X := by
  change ((scalarUnitIso X).inv ≫ scalarTensorMap (IntervalCoefficient.endpoint 0) X) ≫
      scalarTensorMap originalCoefficientReflection.hom X =
    (scalarUnitIso X).inv ≫ scalarTensorMap (IntervalCoefficient.endpoint 1) X
  rw [Category.assoc, ← scalarTensorMap_comp, originalCoefficientReflection_zero]

/-- The entire second original native endpoint reflects to the first endpoint. -/
@[reassoc]
theorem originalIntervalReflection_one (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    inclusion 1 X ≫ (originalIntervalReflection (I := I)).hom.app X = inclusion 0 X := by
  change ((scalarUnitIso X).inv ≫ scalarTensorMap (IntervalCoefficient.endpoint 1) X) ≫
      scalarTensorMap originalCoefficientReflection.hom X =
    (scalarUnitIso X).inv ≫ scalarTensorMap (IntervalCoefficient.endpoint 0) X
  rw [Category.assoc, ← scalarTensorMap_comp, originalCoefficientReflection_one]

/-- Both full projection factors are retained under the actual original scalar reflection. -/
@[reassoc]
theorem originalIntervalReflection_projection (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (originalIntervalReflection (I := I)).hom.app X ≫ projection X = projection X := by
  change scalarTensorMap originalCoefficientReflection.hom X ≫
      (scalarTensorMap IntervalCoefficient.augmentation X ≫ (scalarUnitIso X).hom) =
    scalarTensorMap IntervalCoefficient.augmentation X ≫ (scalarUnitIso X).hom
  rw [← Category.assoc, ← scalarTensorMap_comp, originalCoefficientReflection_augmentation]

/-- The inverse original reflection also carries the entire first endpoint to the second. -/
@[reassoc]
theorem originalIntervalReflection_inv_zero (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    inclusion 0 X ≫ (originalIntervalReflection (I := I)).inv.app X = inclusion 1 X := by
  exact OriginalRelativeCylinder.inverse_endpoint ((originalIntervalReflection (I := I)).app X)
    (inclusion 0 X) (inclusion 1 X) (originalIntervalReflection_one X)

/-- The whole original projection is invariant under the inverse reflection as well. -/
@[reassoc]
theorem originalIntervalReflection_inv_projection
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (originalIntervalReflection (I := I)).inv.app X ≫ projection X = projection X := by
  exact OriginalRelativeCylinder.inverse_projection
    ((originalIntervalReflection (I := I)).app X) (projection X)
    (originalIntervalReflection_projection X)

/-- The reflected action is a whole natural transformation on every original native input map. -/
def freeEndpointActionNatTrans : EnrichedIntervalCylinder.functor ⋙ timeFunctor (I := I) ⟶
    EnrichedIntervalCylinder.functor :=
  OriginalRelativeCylinder.conjugateAction timeFunctor EnrichedIntervalCylinder.functor
    actionNatTrans originalIntervalReflection

/-- The actual contraction toward the original free endpoint is conjugated from the
original contraction. All coefficient and native time maps are retained. -/
def freeEndpointAction (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    timeObject (EnrichedIntervalCylinder.object X) ⟶ EnrichedIntervalCylinder.object X :=
  (freeEndpointActionNatTrans (I := I)).app X

/-- Time zero of the complete original free-endpoint contraction is the identity. -/
theorem freeEndpointAction_zero (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    timeInclusion 0 (EnrichedIntervalCylinder.object X) ≫ freeEndpointAction X = 𝟙 _ := by
  apply OriginalRelativeCylinder.conjugateAction_zero timeFunctor
    EnrichedIntervalCylinder.functor
    (timeInclusionNatTrans 0) actionNatTrans originalIntervalReflection
  intro Y
  exact action_zero Y

/-- Time one is the original projection followed by its free endpoint. -/
theorem freeEndpointAction_one (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    timeInclusion 1 (EnrichedIntervalCylinder.object X) ≫ freeEndpointAction X =
      projection X ≫ inclusion 1 X := by
  exact OriginalRelativeCylinder.conjugateAction_one timeFunctor EnrichedIntervalCylinder.functor
    (timeInclusionNatTrans 1) actionNatTrans originalIntervalReflection
    (inclusionNatTrans 0) (inclusionNatTrans 1) projectionNatTrans
    action_one originalIntervalReflection_projection originalIntervalReflection_inv_zero X

/-- The original free endpoint is fixed at every native time, for arbitrary source diagrams. -/
theorem freeEndpointAction_fixed (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    tensorLeftMap RealizedIntervalContraction.time (inclusion 1 X) ≫ freeEndpointAction X =
      timeProjection X ≫ inclusion 1 X := by
  exact OriginalRelativeCylinder.conjugateAction_fixed timeFunctor
    EnrichedIntervalCylinder.functor
    actionNatTrans originalIntervalReflection (inclusionNatTrans 0) (inclusionNatTrans 1)
    timeProjectionNatTrans action_fixed originalIntervalReflection_one
    originalIntervalReflection_inv_zero X

/-- All original native diagram maps commute with the complete reflected action. -/
@[reassoc]
theorem freeEndpointAction_naturality
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    tensorLeftMap RealizedIntervalContraction.time (tensorLeftMap IntervalCoefficient.interval f) ≫
        freeEndpointAction Y =
      freeEndpointAction X ≫ tensorLeftMap IntervalCoefficient.interval f := by
  exact (freeEndpointActionNatTrans (I := I)).naturality f

/-- The actual original native action retains both complete time and interval projections. -/
theorem originalAction_projection (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    action X ≫ projection X =
      timeProjection (EnrichedIntervalCylinder.object X) ≫ projection X := by
  apply hom_ext
  intro k
  rw [component_comp, action_component, projection_component,
    component_comp, timeProjection_component, projection_component]
  simpa only [EnrichedIntervalCylinder.object, tensorLeftObject_obj,
    EnrichedFunctor.tensorLeft_obj, Category.assoc] using
    congrArg (fun f => f ≫ (λ_ (X.toEnrichedFunctor.obj k)).hom)
      (tensorIntervalMap_projection PointedCGWH.RealizedIntervalContraction.action
        PointedCGWH.freePointIntervalCollapse IntervalCoefficient.augmentation
        originalAction_augmentation (X.toEnrichedFunctor.obj k))

/-- The complete reflected native action preserves the same original projection. -/
theorem freeEndpointAction_projection (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    freeEndpointAction X ≫ projection X =
      timeProjection (EnrichedIntervalCylinder.object X) ≫ projection X :=
  OriginalRelativeCylinder.conjugateAction_projection timeFunctor EnrichedIntervalCylinder.functor
    actionNatTrans originalIntervalReflection timeProjectionNatTrans projectionNatTrans
    originalAction_projection originalIntervalReflection_projection
    originalIntervalReflection_inv_projection X

/-- The genuine reverse path has the original constant projection at every time. -/
theorem freeEndpointAction_pathProjection (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    tensorLeftMap RealizedIntervalContraction.time (inclusion 0 X) ≫
        freeEndpointAction X ≫ projection X = timeProjection X := by
  have hp := freeEndpointAction_projection X
  rw [hp, timeProjection_naturality_assoc, inclusion_projection, Category.comp_id]

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

omit B in
private theorem originalTime_preservesPushouts :
    PreservesColimitsOfShape WalkingSpan (timeFunctor (I := I)) := by
  let _ : PreservesColimits (timeFunctor (I := I)) :=
    (ScalarLeibniz.adjunction RealizedIntervalContraction.time).leftAdjoint_preservesColimits
  infer_instance

attribute [local instance] originalTime_preservesPushouts

/-- Original all-target native HEP constructs the genuine inverse and BOTH relative homotopies
of the same original realized mapping cylinder, on arbitrary source and target diagrams. -/
def originalPair {A X : EnrichedFunctorCat PointedCGWH.{u, v} I} (i : A ⟶ X)
    (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property i) :
    OriginalRelativeCylinder.PairData timeFunctor (timeInclusionNatTrans 0)
      (timeInclusionNatTrans 1) timeProjectionNatTrans i
      (PointedCGWH.EnrichedIntervalMappingCylinder.source (Arrow.mk i))
      (PointedCGWH.EnrichedIntervalMappingCylinder.retraction (Arrow.mk i)) :=
  OriginalRelativeCylinder.ofHEP timeFunctor EnrichedIntervalCylinder.functor
    (timeInclusionNatTrans 0) (timeInclusionNatTrans 1) timeProjectionNatTrans
    (inclusionNatTrans 0) (inclusionNatTrans 1) projectionNatTrans
    (inclusion_projection 0) freeEndpointActionNatTrans freeEndpointAction_zero
    freeEndpointAction_one freeEndpointAction_fixed freeEndpointAction_pathProjection i hi

/-- Evaluate the original native homotopies to obtain an actual ordinary level equivalence. -/
def pairLevelEquivalence
    {A X M : EnrichedFunctorCat PointedCGWH.{u, v} I} {i : A ⟶ X} {j : A ⟶ M} {r : M ⟶ X}
    (d : OriginalRelativeCylinder.PairData timeFunctor (timeInclusionNatTrans 0)
      (timeInclusionNatTrans 1) timeProjectionNatTrans i j r) (k : I) :
    ContinuousMap.HomotopyEquiv (M.toEnrichedFunctor.obj k).right
      (X.toEnrichedFunctor.obj k).right := by
  let rK := component r k
  let sK := component d.inverse k
  have hH₀ : timeInclusion 0 M ≫ d.cylinderHomotopy = 𝟙 M := d.cylinder_zero
  have hH₁ : timeInclusion 1 M ≫ d.cylinderHomotopy = r ≫ d.inverse := d.cylinder_one
  have hJ₀ : timeInclusion 0 X ≫ d.targetHomotopy = 𝟙 X := d.target_zero
  have hJ₁ : timeInclusion 1 X ≫ d.targetHomotopy = d.inverse ≫ r := d.target_one
  let HK := PointedCGWH.EnrichedIntervalMappingCylinderLevelSDR.componentTimeAction
    d.cylinderHomotopy k
  let JK := PointedCGWH.EnrichedIntervalMappingCylinderLevelSDR.componentTimeAction
    d.targetHomotopy k
  have hHK₀ : (λ_ (M.toEnrichedFunctor.obj k)).inv ≫
      (PointedCGWH.freePointIntervalEndpoint 0 ⊗ₘ 𝟙 _) ≫ HK = 𝟙 _ := by
    have h := PointedCGWH.EnrichedIntervalMappingCylinderLevelSDR.componentTimeAction_endpoint
      d.cylinderHomotopy 0 k
    rw [hH₀, component_id] at h
    exact h
  have hHK₁ : (λ_ (M.toEnrichedFunctor.obj k)).inv ≫
      (PointedCGWH.freePointIntervalEndpoint 1 ⊗ₘ 𝟙 _) ≫ HK = rK ≫ sK := by
    have h := PointedCGWH.EnrichedIntervalMappingCylinderLevelSDR.componentTimeAction_endpoint
      d.cylinderHomotopy 1 k
    rw [hH₁, component_comp] at h
    exact h
  have hJK₀ : (λ_ (X.toEnrichedFunctor.obj k)).inv ≫
      (PointedCGWH.freePointIntervalEndpoint 0 ⊗ₘ 𝟙 _) ≫ JK = 𝟙 _ := by
    have h := PointedCGWH.EnrichedIntervalMappingCylinderLevelSDR.componentTimeAction_endpoint
      d.targetHomotopy 0 k
    rw [hJ₀, component_id] at h
    exact h
  have hJK₁ : (λ_ (X.toEnrichedFunctor.obj k)).inv ≫
      (PointedCGWH.freePointIntervalEndpoint 1 ⊗ₘ 𝟙 _) ≫ JK = sK ≫ rK := by
    have h := PointedCGWH.EnrichedIntervalMappingCylinderLevelSDR.componentTimeAction_endpoint
      d.targetHomotopy 1 k
    rw [hJ₁, component_comp] at h
    exact h
  exact {
    toFun := ConcreteCategory.hom rK.right
    invFun := ConcreteCategory.hom sK.right
    left_inv := ⟨(PointedCGWH.freePointIntervalActionHomotopy
      (𝟙 (M.toEnrichedFunctor.obj k)) (rK ≫ sK) HK hHK₀ hHK₁).symm⟩
    right_inv := ⟨(PointedCGWH.freePointIntervalActionHomotopy
      (𝟙 (X.toEnrichedFunctor.obj k)) (sK ≫ rK) JK hJK₀ hJK₁).symm⟩ }

omit B in
/-- The full original level forward map is the actual original retraction component. -/
theorem pairLevelEquivalence_toFun
    {A X M : EnrichedFunctorCat PointedCGWH.{u, v} I} {i : A ⟶ X} {j : A ⟶ M} {r : M ⟶ X}
    (d : OriginalRelativeCylinder.PairData timeFunctor (timeInclusionNatTrans 0)
      (timeInclusionNatTrans 1) timeProjectionNatTrans i j r) (k : I) :
    (pairLevelEquivalence d k).toFun = ConcreteCategory.hom (component r k).right := rfl

/-- The computed genuine pair makes the SAME original projection level weak, at every point. -/
theorem pairProjection_weakEquivalence
    {A X M : EnrichedFunctorCat PointedCGWH.{u, v} I} {i : A ⟶ X} {j : A ⟶ M} {r : M ⟶ X}
    (d : OriginalRelativeCylinder.PairData timeFunctor (timeInclusionNatTrans 0)
      (timeInclusionNatTrans 1) timeProjectionNatTrans i j r) : WeakEquivalence r := by
  apply (HomotopicalAlgebra.weakEquivalence_iff r).mpr
  rw [HomotopicalAlgebra.EnrichedProjective.Native.weakEquivalences_eq]
  apply (EvaluationTransfer.evaluationProperty_iff
    (fun k : I => evaluation k) (weakEquivalences PointedCGWH.{u, v}) r).mpr
  intro k
  apply (HomotopicalAlgebra.weakEquivalence_iff (component r k)).mp
  apply (PointedCGWH.weakEquivalence_iff _).mpr
  apply (CGWH.modelCategory.weakEquivalence_iff _).mpr
  rw [CGWH.weakHomotopyEquivalences_eq_inverseImage]
  change TopCat.weakHomotopyEquivalences (TopCat.ofHom (pairLevelEquivalence d k).toFun)
  exact TopCat.homotopyEquiv_toFun_mem (pairLevelEquivalence d k)

/-- The actual original double cylinder attaches the SAME original source through the second leg. -/
abbrev originalDoubleCylinder {A X Z : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (i : A ⟶ X) (z : A ⟶ Z) : EnrichedFunctorCat PointedCGWH.{u, v} I :=
  pushout (PointedCGWH.EnrichedIntervalMappingCylinder.source (Arrow.mk i)) z

/-- The genuine comparison to the caller's original pushout preserves both complete legs. -/
def originalDoubleCylinderComparison
    {A X Z P : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (i : A ⟶ X) (z : A ⟶ Z) (kX : X ⟶ P) (kZ : Z ⟶ P)
    (sq : IsPushout i z kX kZ) : originalDoubleCylinder i z ⟶ P :=
  OriginalRelativeCylinder.pushoutComparison sq
    (IsPushout.of_hasPushout (PointedCGWH.EnrichedIntervalMappingCylinder.source (Arrow.mk i)) z)
    (PointedCGWH.EnrichedIntervalMappingCylinder.fac (Arrow.mk i))

/-- The original HEP computes both homotopies over the caller's actual pushout,
retaining the original other leg and the entire double-cylinder attachment. -/
def originalPushoutPair
    {A X Z P : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (i : A ⟶ X) (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property i)
    (z : A ⟶ Z) (kX : X ⟶ P) (kZ : Z ⟶ P) (sq : IsPushout i z kX kZ) :
    OriginalRelativeCylinder.PairData timeFunctor (timeInclusionNatTrans 0)
      (timeInclusionNatTrans 1) timeProjectionNatTrans kZ
      (pushout.inr (PointedCGWH.EnrichedIntervalMappingCylinder.source (Arrow.mk i)) z)
      (originalDoubleCylinderComparison i z kX kZ sq) :=
  OriginalRelativeCylinder.cobasePair timeFunctor (timeInclusionNatTrans 0)
    (timeInclusionNatTrans 1) timeProjectionNatTrans
    (timeInclusion_projection 0) (timeInclusion_projection 1) (originalPair i hi)
    (PointedCGWH.EnrichedIntervalMappingCylinder.fac (Arrow.mk i)) z sq
    (IsPushout.of_hasPushout (PointedCGWH.EnrichedIntervalMappingCylinder.source (Arrow.mk i)) z)

/-- The original arbitrary HEP pushout has its genuine actual double-cylinder level comparison.
This concerns the same original cylinder, not an assumed badly based span approximation. -/
theorem originalDoubleCylinderComparison_weakEquivalence
    {A X Z P : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (i : A ⟶ X) (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property i)
    (z : A ⟶ Z) (kX : X ⟶ P) (kZ : Z ⟶ P) (sq : IsPushout i z kX kZ) :
    WeakEquivalence (originalDoubleCylinderComparison i z kX kZ sq) :=
  pairProjection_weakEquivalence (originalPushoutPair i hi z kX kZ sq)

omit B in
/-- The same original MC leg retains the original retraction and caller's target map. -/
@[reassoc]
theorem originalDoubleCylinderComparison_inl
    {A X Z P : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (i : A ⟶ X) (z : A ⟶ Z) (kX : X ⟶ P) (kZ : Z ⟶ P) (sq : IsPushout i z kX kZ) :
    pushout.inl (PointedCGWH.EnrichedIntervalMappingCylinder.source (Arrow.mk i)) z ≫
        originalDoubleCylinderComparison i z kX kZ sq =
      PointedCGWH.EnrichedIntervalMappingCylinder.retraction (Arrow.mk i) ≫ kX :=
  OriginalRelativeCylinder.pushoutComparison_inl sq
    (IsPushout.of_hasPushout (PointedCGWH.EnrichedIntervalMappingCylinder.source (Arrow.mk i)) z)
    (PointedCGWH.EnrichedIntervalMappingCylinder.fac (Arrow.mk i))

omit B in
/-- The original other leg is exactly the same double-cylinder leg followed by collapse. -/
@[reassoc]
theorem originalDoubleCylinderComparison_inr
    {A X Z P : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (i : A ⟶ X) (z : A ⟶ Z) (kX : X ⟶ P) (kZ : Z ⟶ P) (sq : IsPushout i z kX kZ) :
    pushout.inr (PointedCGWH.EnrichedIntervalMappingCylinder.source (Arrow.mk i)) z ≫
        originalDoubleCylinderComparison i z kX kZ sq = kZ :=
  OriginalRelativeCylinder.pushoutComparison_inr sq
    (IsPushout.of_hasPushout (PointedCGWH.EnrichedIntervalMappingCylinder.source (Arrow.mk i)) z)
    (PointedCGWH.EnrichedIntervalMappingCylinder.fac (Arrow.mk i))

omit B in
/-- Every actual comparison of caller pushouts retains BOTH original target-leg equations. -/
@[reassoc]
theorem originalDoubleCylinderComparison_choiceMap
    {A X Z P P' : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (i : A ⟶ X) (z : A ⟶ Z) (kX : X ⟶ P) (kZ : Z ⟶ P) (sq : IsPushout i z kX kZ)
    (kX' : X ⟶ P') (kZ' : Z ⟶ P') (sq' : IsPushout i z kX' kZ')
    (h : P ⟶ P') (hX : kX ≫ h = kX') (hZ : kZ ≫ h = kZ') :
    originalDoubleCylinderComparison i z kX kZ sq ≫ h =
      originalDoubleCylinderComparison i z kX' kZ' sq' := by
  apply pushout.hom_ext
  · rw [originalDoubleCylinderComparison_inl_assoc, hX,
      originalDoubleCylinderComparison_inl]
  · rw [originalDoubleCylinderComparison_inr_assoc, hZ,
      originalDoubleCylinderComparison_inr]

open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK

/-- Every actual original double-cylinder comparison is weak against ALL original Omega targets. -/
theorem originalDoubleCylinderComparison_omegaTests {L : Type}
    (s : NativeStabilizationFamily (I := I) L)
    {A X Z P : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (i : A ⟶ X) (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property i)
    (z : A ⟶ Z) (kX : X ⟶ P) (kZ : Z ⟶ P) (sq : IsPushout i z kX kZ) :
    NativeK.omegaTests s (originalDoubleCylinderComparison i z kX kZ sq) :=
  NativeK.levelWeak_le_omegaTests s _ ((HomotopicalAlgebra.weakEquivalence_iff _).mp
    (originalDoubleCylinderComparison_weakEquivalence i hi z kX kZ sq))

/-- The full original arbitrary cobase question reduces to its SAME actual double-cylinder leg.
Weakness of that leg is not a premise or a claimed closure theorem. -/
theorem originalOtherLeg_omegaTests_iff {L : Type} (s : NativeStabilizationFamily (I := I) L)
    {A X Z P : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (i : A ⟶ X) (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property i)
    (z : A ⟶ Z) (kX : X ⟶ P) (kZ : Z ⟶ P) (sq : IsPushout i z kX kZ) :
    NativeK.omegaTests s kZ ↔
      NativeK.omegaTests s
        (pushout.inr (PointedCGWH.EnrichedIntervalMappingCylinder.source (Arrow.mk i)) z) := by
  let f : Z ⟶ originalDoubleCylinder i z :=
    pushout.inr (PointedCGWH.EnrichedIntervalMappingCylinder.source (Arrow.mk i)) z
  let c := originalDoubleCylinderComparison i z kX kZ sq
  have hc : NativeK.omegaTests s c := originalDoubleCylinderComparison_omegaTests s i hi z kX kZ sq
  have hfc : f ≫ c = kZ := originalDoubleCylinderComparison_inr i z kX kZ sq
  constructor
  · intro h
    exact (NativeK.omegaTests s).of_postcomp f c hc (hfc.symm ▸ h)
  · intro h
    have hComp := (NativeK.omegaTests s).comp_mem f c h hc
    exact hfc ▸ hComp

private abbrev Carrier := EnrichedFunctorCat PointedCGWH.{u, v} I

/-- The original first arrow retains every endpoint of the caller's entire span. -/
def originalFirstArrowFunctor : (WalkingSpan ⥤ Carrier (I := I)) ⥤ Arrow (Carrier (I := I)) where
  obj F := Arrow.mk (F.map WalkingSpan.Hom.fst)
  map α := Arrow.homMk (α.app WalkingSpan.zero) (α.app WalkingSpan.left)
    (α.naturality WalkingSpan.Hom.fst).symm
  map_id F := by apply Arrow.hom_ext <;> rfl
  map_comp α β := by apply Arrow.hom_ext <;> rfl

/-- The full original double-cylinder span is functorial in every caller span and transformation. -/
def originalDoubleCylinderSpanFunctor :
    (WalkingSpan ⥤ Carrier (I := I)) ⥤ WalkingSpan ⥤ Carrier (I := I) where
  obj F := span
    (PointedCGWH.EnrichedIntervalMappingCylinder.source (originalFirstArrowFunctor.obj F))
    (F.map WalkingSpan.Hom.snd)
  map α := spanHomMk (α.app WalkingSpan.zero)
    (PointedCGWH.EnrichedIntervalMappingCylinder.map (originalFirstArrowFunctor.map α))
    (α.app WalkingSpan.right)
    (PointedCGWH.EnrichedIntervalMappingCylinder.source_map (originalFirstArrowFunctor.map α))
    (α.naturality WalkingSpan.Hom.snd)
  map_id F := by
    apply NatTrans.ext
    funext j
    rcases j with (_ | _ | _)
    · rfl
    · change PointedCGWH.EnrichedIntervalMappingCylinder.functor.map
        (originalFirstArrowFunctor.map (𝟙 F)) = 𝟙 _
      rw [originalFirstArrowFunctor.map_id]
      exact PointedCGWH.EnrichedIntervalMappingCylinder.functor.map_id _
    · rfl
  map_comp α β := by
    apply NatTrans.ext
    funext j
    rcases j with (_ | _ | _)
    · rfl
    · change PointedCGWH.EnrichedIntervalMappingCylinder.functor.map
        (originalFirstArrowFunctor.map (α ≫ β)) =
        PointedCGWH.EnrichedIntervalMappingCylinder.functor.map
          (originalFirstArrowFunctor.map α) ≫
        PointedCGWH.EnrichedIntervalMappingCylinder.functor.map
          (originalFirstArrowFunctor.map β)
      rw [originalFirstArrowFunctor.map_comp]
      exact PointedCGWH.EnrichedIntervalMappingCylinder.functor.map_comp _ _
    · rfl

/-- Every original span keeps its original source identity, MC projection and other-leg identity. -/
def originalDoubleCylinderSpanCounit : originalDoubleCylinderSpanFunctor (I := I) ⟶
    𝟭 (WalkingSpan ⥤ Carrier (I := I)) where
  app F := spanHomMk (𝟙 (F.obj WalkingSpan.zero))
    (PointedCGWH.EnrichedIntervalMappingCylinder.retraction (originalFirstArrowFunctor.obj F))
    (𝟙 (F.obj WalkingSpan.right))
    (by
      change PointedCGWH.EnrichedIntervalMappingCylinder.source
        (originalFirstArrowFunctor.obj F) ≫
        PointedCGWH.EnrichedIntervalMappingCylinder.retraction
          (originalFirstArrowFunctor.obj F) =
        (𝟙 (F.obj WalkingSpan.zero)) ≫ F.map WalkingSpan.Hom.fst
      rw [Category.id_comp]
      exact PointedCGWH.EnrichedIntervalMappingCylinder.fac (originalFirstArrowFunctor.obj F))
    (by
      change F.map WalkingSpan.Hom.snd ≫ (𝟙 (F.obj WalkingSpan.right)) =
        (𝟙 (F.obj WalkingSpan.zero)) ≫ F.map WalkingSpan.Hom.snd
      simp only [Category.id_comp, Category.comp_id])
  naturality F G α := by
    apply NatTrans.ext
    funext j
    rcases j with (_ | _ | _)
    · change α.app WalkingSpan.zero ≫ 𝟙 _ = 𝟙 _ ≫ α.app WalkingSpan.zero
      simp only [Category.comp_id, Category.id_comp]
    · exact PointedCGWH.EnrichedIntervalMappingCylinder.map_retraction
        (originalFirstArrowFunctor.map α)
    · change α.app WalkingSpan.right ≫ 𝟙 _ = 𝟙 _ ≫ α.app WalkingSpan.right
      simp only [Category.comp_id, Category.id_comp]

/-- The actual full double-cylinder colimit construction keeps every original input map. -/
def originalDoubleCylinderColimit : (WalkingSpan ⥤ Carrier (I := I)) ⥤ Carrier (I := I) :=
  originalDoubleCylinderSpanFunctor ⋙ colim

/-- The same original full span counit induces the whole original colimit comparison. -/
def originalDoubleCylinderColimitComparison : originalDoubleCylinderColimit (I := I) ⟶ colim :=
  Functor.whiskerRight originalDoubleCylinderSpanCounit colim

omit B in
/-- Every original colimit leg retains its complete original span comparison equation. -/
@[reassoc]
theorem originalDoubleCylinderColimitComparison_ι
    (F : WalkingSpan ⥤ Carrier (I := I)) (j : WalkingSpan) :
    colimit.ι (originalDoubleCylinderSpanFunctor.obj F) j ≫
        (originalDoubleCylinderColimitComparison (I := I)).app F =
      (originalDoubleCylinderSpanCounit.app F).app j ≫ colimit.ι F j :=
  ι_colimMap (originalDoubleCylinderSpanCounit.app F) j

omit B in
/-- Every whole original span transformation retains the same actual colimit naturality. -/
@[reassoc]
theorem originalDoubleCylinderColimitComparison_naturality
    {F G : WalkingSpan ⥤ Carrier (I := I)} (α : F ⟶ G) :
    originalDoubleCylinderColimit.map α ≫ originalDoubleCylinderColimitComparison.app G =
      originalDoubleCylinderColimitComparison.app F ≫ colim.map α :=
  originalDoubleCylinderColimitComparison.naturality α

omit B in
/-- A complete span recovers the SAME original double cylinder, with no carrier substitution. -/
theorem originalDoubleCylinderColimit_obj_span
    {A X Z : Carrier (I := I)} (i : A ⟶ X) (z : A ⟶ Z) :
    originalDoubleCylinderColimit.obj (span i z) = originalDoubleCylinder i z := rfl

omit B in
/-- The whole functorial comparison is the actual original canonical two-leg collapse. -/
theorem originalDoubleCylinderColimitComparison_app_span
    {A X Z : Carrier (I := I)} (i : A ⟶ X) (z : A ⟶ Z) :
    originalDoubleCylinderColimitComparison.app (span i z) =
      originalDoubleCylinderComparison i z (pushout.inl i z) (pushout.inr i z)
        (IsPushout.of_hasPushout i z) := by
  let c : originalDoubleCylinder i z ⟶ pushout i z :=
    originalDoubleCylinderColimitComparison.app (span i z)
  change c = originalDoubleCylinderComparison i z (pushout.inl i z) (pushout.inr i z)
    (IsPushout.of_hasPushout i z)
  apply pushout.hom_ext
  · have h := originalDoubleCylinderColimitComparison_ι (span i z) WalkingSpan.left
    change pushout.inl (PointedCGWH.EnrichedIntervalMappingCylinder.source (Arrow.mk i)) z ≫ c =
      PointedCGWH.EnrichedIntervalMappingCylinder.retraction (Arrow.mk i) ≫ pushout.inl i z at h
    exact h.trans (originalDoubleCylinderComparison_inl i z _ _
      (IsPushout.of_hasPushout i z)).symm
  · have h := originalDoubleCylinderColimitComparison_ι (span i z) WalkingSpan.right
    change pushout.inr (PointedCGWH.EnrichedIntervalMappingCylinder.source (Arrow.mk i)) z ≫ c =
      (𝟙 Z) ≫ pushout.inr i z at h
    have h' : pushout.inr (PointedCGWH.EnrichedIntervalMappingCylinder.source (Arrow.mk i)) z ≫ c =
        pushout.inr i z := by simpa only [Category.id_comp] using h
    exact h'.trans (originalDoubleCylinderComparison_inr i z _ _
      (IsPushout.of_hasPushout i z)).symm

/-- The same whole functorial colimit comparison is level weak for EVERY original HEP span. -/
theorem originalDoubleCylinderColimitComparison_weakEquivalence
    (F : WalkingSpan ⥤ Carrier (I := I))
    (hF : PointedCGWH.EnrichedBasedHomotopyExtension.property (F.map WalkingSpan.Hom.fst)) :
    WeakEquivalence (originalDoubleCylinderColimitComparison.app F) := by
  let G := span (F.map WalkingSpan.Hom.fst) (F.map WalkingSpan.Hom.snd)
  let e : F ≅ G := diagramIsoSpan F
  let W := weakEquivalences (Carrier (I := I))
  have hG : W (originalDoubleCylinderColimitComparison.app G) := by
    apply (HomotopicalAlgebra.weakEquivalence_iff _).mp
    rw [originalDoubleCylinderColimitComparison_app_span]
    exact originalDoubleCylinderComparison_weakEquivalence _ hF _ _ _
      (IsPushout.of_hasPushout _ _)
  have hL : W (originalDoubleCylinderColimit.map e.hom) := W.of_isIso _
  have hR : W ((colim (C := Carrier (I := I))).map e.hom) := W.of_isIso _
  have hComp := W.comp_mem _ _ hL hG
  have hn := originalDoubleCylinderColimitComparison.naturality e.hom
  have hOriginal : W (originalDoubleCylinderColimitComparison.app F ≫ colim.map e.hom) :=
    hn ▸ hComp
  exact (HomotopicalAlgebra.weakEquivalence_iff _).mpr (W.of_postcomp _ _ hR hOriginal)

end PointedCGWH.Spectra.OriginalHEPHomotopyPushoutComparison
