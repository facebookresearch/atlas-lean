/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Limits.Shapes.EndofunctorCone
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalHEPHomotopyPushoutComparison
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.MappingCylinderBasedHEP
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenPuppeRotation
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenFiberCofiberComparison
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.FreeSphereNullHom
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.ScalarFreeSphereHom
import MathlibExt.Algebra.Category.Grp.FilteredKernelRepresentatives
import MathlibExt.Algebra.Category.Grp.ExactnessTransport
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.SuspensionStablePi
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.ScalarSuspensionClassGroupMap

import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.StageIntegerStablePi

/-!
# Original scalar cones and raw stable homotopy pushouts

The cone collapses the actual second endpoint of the original realized
interval. Its inclusion uses the first endpoint. All maps are maps of the
original native carrier, with arbitrary based source and target objects.
The scalar cofiber retains these exact cone and target legs. Homotopy
extension compares it with the caller's actual quotient pushout.

The later raw integer homotopy gluing theorem must retain these maps and
the unsuspended kernel classes. No stable equivalence, exactness or gluing
outcome is assumed by the cone construction.
-/

set_option autoImplicit false
noncomputable section
universe u v uC vC

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory MonoidalClosed ZeroObject


namespace PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

open PointedCGWH.EnrichedIntervalContraction PointedCGWH.EnrichedIntervalCylinder
open PointedCGWH.Spectra.OriginalHEPHomotopyPushoutComparison

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
attribute [local instance] MonoidalClosed.enrichedCategorySelf
  PointedCGWH.EnrichedMapping.hasSmallLimits
  HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.nativeHasZeroObject
  HasZeroObject.zeroMorphismsOfZeroObject
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

private instance originalTimePreservesPushouts :
    PreservesColimitsOfShape WalkingSpan (timeFunctor (I := I)) := by
  let _ : PreservesColimits (timeFunctor (I := I)) :=
    (ScalarLeibniz.adjunction RealizedIntervalContraction.time).leftAdjoint_preservesColimits
  infer_instance

private instance originalTimePreservesZero :
    (timeFunctor (I := I)).PreservesZeroMorphisms := by
  let _ : (timeFunctor (I := I)).IsLeftAdjoint :=
    (ScalarLeibniz.adjunction RealizedIntervalContraction.time).isLeftAdjoint
  infer_instance

/-- The full native cone collapses the original realized second endpoint. -/
abbrev originalConeFunctor : EnrichedFunctorCat PointedCGWH.{u, v} I ⥤
    EnrichedFunctorCat PointedCGWH.{u, v} I :=
  OriginalScalarCone.coneFunctor EnrichedIntervalCylinder.functor (inclusionNatTrans 1)

/-- The actual original native cone quotient retains its entire interval leg. -/
abbrev originalConeQuotient (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    EnrichedIntervalCylinder.object X ⟶ originalConeFunctor.obj X :=
  OriginalScalarCone.quotient EnrichedIntervalCylinder.functor (inclusionNatTrans 1) X

/-- The whole original native first endpoint is the scalar cone inclusion. -/
abbrev originalConeInclusion : 𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} I) ⟶
    originalConeFunctor :=
  OriginalScalarCone.inclusionNatTrans EnrichedIntervalCylinder.functor
    (inclusionNatTrans 0) (inclusionNatTrans 1)

/-- The actual cone homotopy descends the original full free-endpoint contraction. -/
abbrev originalConeContraction (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    timeObject (originalConeFunctor.obj X) ⟶ originalConeFunctor.obj X :=
  OriginalScalarCone.contraction timeFunctor EnrichedIntervalCylinder.functor
    (inclusionNatTrans 1) timeProjectionNatTrans freeEndpointActionNatTrans
    freeEndpointAction_fixed X

/-- The actual original interval endpoint is zero in the same native cone. -/
@[reassoc]
theorem originalConeQuotient_one (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    inclusion 1 X ≫ originalConeQuotient X = 0 :=
  OriginalScalarCone.endpoint_quotient EnrichedIntervalCylinder.functor (inclusionNatTrans 1) X

/-- The computed native cone contraction starts at the identity, on every original source. -/
theorem originalConeContraction_zero (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    timeInclusion 0 (originalConeFunctor.obj X) ≫ originalConeContraction X = 𝟙 _ :=
  OriginalScalarCone.contraction_zero timeFunctor EnrichedIntervalCylinder.functor
    (timeInclusionNatTrans 0) (inclusionNatTrans 1) timeProjectionNatTrans
    freeEndpointActionNatTrans freeEndpointAction_fixed freeEndpointAction_zero X

/-- The computed native cone contraction ends at zero, with no source cofibrancy hypothesis. -/
theorem originalConeContraction_one (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    timeInclusion 1 (originalConeFunctor.obj X) ≫ originalConeContraction X = 0 :=
  OriginalScalarCone.contraction_one timeFunctor EnrichedIntervalCylinder.functor
    (timeInclusionNatTrans 1) (inclusionNatTrans 1) timeProjectionNatTrans projectionNatTrans
    freeEndpointActionNatTrans freeEndpointAction_fixed freeEndpointAction_one X

/-- Every original native input map commutes with the full actual cone contraction. -/
@[reassoc]
theorem originalConeContraction_naturality
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    tensorLeftMap RealizedIntervalContraction.time (originalConeFunctor.map f) ≫
        originalConeContraction Y = originalConeContraction X ≫ originalConeFunctor.map f :=
  OriginalScalarCone.contraction_naturality timeFunctor EnrichedIntervalCylinder.functor
    (inclusionNatTrans 1) timeProjectionNatTrans freeEndpointActionNatTrans
    freeEndpointAction_fixed f

/-- The full actual native scalar cofiber retains the original arrow and cone legs. -/
abbrev originalScalarCofiberFunctor : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I) ⥤
    EnrichedFunctorCat PointedCGWH.{u, v} I :=
  OriginalScalarCone.cofiberFunctor EnrichedIntervalCylinder.functor
    (inclusionNatTrans 0) (inclusionNatTrans 1)

/-- The actual cone contraction supplies both native homotopies of its zero projection. -/
def originalConeZeroPair (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    OriginalRelativeCylinder.PairData timeFunctor (timeInclusionNatTrans 0)
      (timeInclusionNatTrans 1) timeProjectionNatTrans
      (0 : (0 : EnrichedFunctorCat PointedCGWH.{u, v} I) ⟶ 0)
      (0 : (0 : EnrichedFunctorCat PointedCGWH.{u, v} I) ⟶ originalConeFunctor.obj X)
      (0 : originalConeFunctor.obj X ⟶ (0 : EnrichedFunctorCat PointedCGWH.{u, v} I)) where
  inverse := 0
  inverse_source := by simp
  cylinderHomotopy := originalConeContraction X
  cylinder_zero := originalConeContraction_zero X
  cylinder_one := by
    change timeInclusion 1 (originalConeFunctor.obj X) ≫ originalConeContraction X =
      (0 : originalConeFunctor.obj X ⟶ (0 : EnrichedFunctorCat PointedCGWH.{u, v} I)) ≫
        (0 : (0 : EnrichedFunctorCat PointedCGWH.{u, v} I) ⟶ originalConeFunctor.obj X)
    rw [zero_comp]
    exact originalConeContraction_one X
  cylinder_fixed := by
    exact (timeFunctor.map_isZero
      (isZero_zero (EnrichedFunctorCat PointedCGWH.{u, v} I))).isInitial.hom_ext _ _
  targetHomotopy := 0
  target_zero := by
    exact (isZero_zero (EnrichedFunctorCat PointedCGWH.{u, v} I)).isInitial.hom_ext _ _
  target_one := by simp
  target_fixed := by simp

/-- The actual scalar cone collapses to zero by a genuine level homotopy equivalence. -/
theorem originalConeProjection_weakEquivalence
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    WeakEquivalence
      (0 : originalConeFunctor.obj X ⟶ (0 : EnrichedFunctorCat PointedCGWH.{u, v} I)) := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
    HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  exact pairProjection_weakEquivalence (originalConeZeroPair X)

/-- Both full original zero choices are related by their actual unique zero isomorphism. -/
def originalZeroDiagramIso : (0 : EnrichedFunctorCat PointedCGWH.{u, v} I) ≅
    HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram :=
  (isZero_zero (EnrichedFunctorCat PointedCGWH.{u, v} I)).iso
    HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero

/-- The actual cone also collapses weakly to the same explicit original native zero diagram. -/
theorem originalConeCollapse_weakEquivalence
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    WeakEquivalence
      (HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.toZero
        (originalConeFunctor.obj X)) := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} I) :=
    HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  let r : originalConeFunctor.obj X ⟶ (0 : EnrichedFunctorCat PointedCGWH.{u, v} I) := 0
  let _ : WeakEquivalence r := originalConeProjection_weakEquivalence X
  have h : r ≫ originalZeroDiagramIso.hom =
      HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.toZero
        (originalConeFunctor.obj X) :=
    HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  have hw : WeakEquivalence (r ≫ originalZeroDiagramIso.hom) := by infer_instance
  exact h ▸ hw

/-- The same actual native scalar cofiber is the original double cylinder with zero second leg. -/
def originalScalarCofiberDoubleIso
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    originalDoubleCylinder f (0 : X ⟶ (0 : EnrichedFunctorCat PointedCGWH.{u, v} I)) ≅
      originalScalarCofiberFunctor.obj (Arrow.mk f) :=
  OriginalScalarCone.doubleCofiberIso EnrichedIntervalCylinder.functor
    (inclusionNatTrans 0) (inclusionNatTrans 1) f

/-- The scalar cofiber comparison retains the caller's actual quotient cocone and target leg. -/
def originalScalarCofiberQuotientComparison
    {X Y Z P : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (f : X ⟶ Y) (z : X ⟶ Z) (hZ : IsZero Z) (kY : Y ⟶ P) (kZ : Z ⟶ P)
    (sq : IsPushout f z kY kZ) : originalScalarCofiberFunctor.obj (Arrow.mk f) ⟶ P :=
  OriginalScalarCone.cofiberQuotientComparison EnrichedIntervalCylinder.functor
    (inclusionNatTrans 0) (inclusionNatTrans 1) f z hZ kY kZ sq

/-- Every original scalar cone inclusion has all-target native HEP on arbitrary source objects. -/
theorem originalConeInclusion_basedHEP (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    PointedCGWH.EnrichedBasedHomotopyExtension.property (originalConeInclusion.app X) := by
  have sq := OriginalScalarCone.coneJointIsPushout EnrichedIntervalCylinder.functor
    (inclusionNatTrans 0) (inclusionNatTrans 1) X
  exact MorphismProperty.of_isPushout sq.flip
    (PointedCGWH.EnrichedBasedHomotopyExtension.jointMap_mem X)

/-- The actual target-to-scalar-cofiber inclusion has native HEP for every original arrow. -/
theorem originalScalarCofiberTarget_basedHEP
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    PointedCGWH.EnrichedBasedHomotopyExtension.property
      (OriginalScalarCone.cofiberTarget EnrichedIntervalCylinder.functor
        (inclusionNatTrans 0) (inclusionNatTrans 1) f) :=
  MorphismProperty.of_isPushout
    (OriginalScalarCone.cofiberIsPushout EnrichedIntervalCylinder.functor
      (inclusionNatTrans 0) (inclusionNatTrans 1) f) (originalConeInclusion_basedHEP X)

/-- The actual scalar-cofiber target-to-quotient map is exactly the caller's original target leg. -/
@[reassoc]
theorem originalScalarCofiberQuotientComparison_target
    {X Y Z P : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (f : X ⟶ Y) (z : X ⟶ Z) (hZ : IsZero Z) (kY : Y ⟶ P) (kZ : Z ⟶ P)
    (sq : IsPushout f z kY kZ) :
    OriginalScalarCone.cofiberTarget EnrichedIntervalCylinder.functor
        (inclusionNatTrans 0) (inclusionNatTrans 1) f ≫
      originalScalarCofiberQuotientComparison f z hZ kY kZ sq = kY :=
  OriginalScalarCone.cofiberQuotientComparison_target EnrichedIntervalCylinder.functor
    (inclusionNatTrans 0) (inclusionNatTrans 1) f z hZ kY kZ sq

/-- The same full original cone leg vanishes under the actual quotient comparison. -/
@[reassoc]
theorem originalScalarCofiberQuotientComparison_cone
    {X Y Z P : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (f : X ⟶ Y) (z : X ⟶ Z) (hZ : IsZero Z) (kY : Y ⟶ P) (kZ : Z ⟶ P)
    (sq : IsPushout f z kY kZ) :
    OriginalScalarCone.cofiberCone EnrichedIntervalCylinder.functor
        (inclusionNatTrans 0) (inclusionNatTrans 1) f ≫
      originalScalarCofiberQuotientComparison f z hZ kY kZ sq = 0 :=
  OriginalScalarCone.cofiberQuotientComparison_cone EnrichedIntervalCylinder.functor
    (inclusionNatTrans 0) (inclusionNatTrans 1) f z hZ kY kZ sq

/-- All-target HEP makes the exact scalar-cofiber-to-caller-quotient comparison level weak.
The source, target, zero choice, caller cocone and both actual legs are retained. -/
theorem originalScalarCofiberQuotientComparison_weakEquivalence
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    {X Y Z P : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (f : X ⟶ Y) (hf : PointedCGWH.EnrichedBasedHomotopyExtension.property f)
    (z : X ⟶ Z) (hZ : IsZero Z) (kY : Y ⟶ P) (kZ : Z ⟶ P)
    (sq : IsPushout f z kY kZ) :
    WeakEquivalence (originalScalarCofiberQuotientComparison f z hZ kY kZ sq) := by
  let Z₀ : EnrichedFunctorCat PointedCGWH.{u, v} I := 0
  let eZ : Z ≅ Z₀ := hZ.iso (isZero_zero _)
  let k₀ : Z₀ ⟶ P := eZ.inv ≫ kZ
  have sq₀ : IsPushout f (0 : X ⟶ Z₀) kY k₀ := by
    apply sq.of_iso (Iso.refl X) (Iso.refl Y) eZ (Iso.refl P)
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    · exact (isZero_zero (EnrichedFunctorCat PointedCGWH.{u, v} I)).isTerminal.hom_ext _ _
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    · change kZ ≫ 𝟙 P = eZ.hom ≫ (eZ.inv ≫ kZ)
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id]
  let c : originalScalarCofiberFunctor.obj (Arrow.mk f) ⟶ P :=
    originalScalarCofiberQuotientComparison f z hZ kY kZ sq
  let e := originalScalarCofiberDoubleIso f
  let r : PointedCGWH.EnrichedIntervalMappingCylinder.object (Arrow.mk f) ⟶ Y :=
    PointedCGWH.EnrichedIntervalMappingCylinder.retraction (Arrow.mk f)
  let m : PointedCGWH.EnrichedIntervalMappingCylinder.object (Arrow.mk f) ⟶
      originalScalarCofiberFunctor.obj (Arrow.mk f) :=
    OriginalScalarCone.cylinderToCofiber EnrichedIntervalCylinder.functor
      (inclusionNatTrans 0) (inclusionNatTrans 1) f
  have hFzero : f ≫ kY = 0 := by
    rw [sq.w, hZ.eq_of_tgt z 0, zero_comp]
  have hMC : m ≫ c = r ≫ kY := by
    have sqMC : IsPushout (inclusion 0 X) f
        (PointedCGWH.EnrichedIntervalMappingCylinder.intervalLeg (Arrow.mk f))
        (PointedCGWH.EnrichedIntervalMappingCylinder.targetLeg (Arrow.mk f)) :=
      IsPushout.of_hasPushout _ _
    have hL : PointedCGWH.EnrichedIntervalMappingCylinder.intervalLeg (Arrow.mk f) ≫ m =
        originalConeQuotient X ≫
          OriginalScalarCone.cofiberCone EnrichedIntervalCylinder.functor
            (inclusionNatTrans 0) (inclusionNatTrans 1) f :=
      OriginalScalarCone.cylinderToCofiber_interval EnrichedIntervalCylinder.functor
        (inclusionNatTrans 0) (inclusionNatTrans 1) f
    have hR : PointedCGWH.EnrichedIntervalMappingCylinder.targetLeg (Arrow.mk f) ≫ m =
        OriginalScalarCone.cofiberTarget EnrichedIntervalCylinder.functor
          (inclusionNatTrans 0) (inclusionNatTrans 1) f :=
      OriginalScalarCone.cylinderToCofiber_target EnrichedIntervalCylinder.functor
        (inclusionNatTrans 0) (inclusionNatTrans 1) f
    have hLR : PointedCGWH.EnrichedIntervalMappingCylinder.intervalLeg (Arrow.mk f) ≫ r =
        projection X ≫ f := PointedCGWH.EnrichedIntervalMappingCylinder.intervalLeg_retraction _
    have hRR : PointedCGWH.EnrichedIntervalMappingCylinder.targetLeg (Arrow.mk f) ≫ r = 𝟙 Y :=
      PointedCGWH.EnrichedIntervalMappingCylinder.targetLeg_retraction _
    apply sqMC.hom_ext
    · rw [← Category.assoc, hL, Category.assoc,
        originalScalarCofiberQuotientComparison_cone, comp_zero,
        ← Category.assoc, hLR, Category.assoc, hFzero, comp_zero]
    · rw [← Category.assoc, hR, originalScalarCofiberQuotientComparison_target,
        ← Category.assoc, hRR, Category.id_comp]
  let d : originalDoubleCylinder f (0 : X ⟶ Z₀) ⟶ P :=
    originalDoubleCylinderComparison f (0 : X ⟶ Z₀) kY k₀ sq₀
  have hCompare : e.hom ≫ c = d := by
    have sqD := IsPushout.of_hasPushout
      (PointedCGWH.EnrichedIntervalMappingCylinder.source (Arrow.mk f)) (0 : X ⟶ Z₀)
    have hD : pushout.inl
        (PointedCGWH.EnrichedIntervalMappingCylinder.source (Arrow.mk f)) (0 : X ⟶ Z₀) ≫
          e.hom = m :=
      OriginalScalarCone.doubleToCofiber_cylinder EnrichedIntervalCylinder.functor
        (inclusionNatTrans 0) (inclusionNatTrans 1) f
    apply sqD.hom_ext
    · rw [← Category.assoc, hD, hMC]
      exact (originalDoubleCylinderComparison_inl f (0 : X ⟶ Z₀) kY k₀ sq₀).symm
    · exact (isZero_zero (EnrichedFunctorCat PointedCGWH.{u, v} I)).isInitial.hom_ext _ _
  let _ : WeakEquivalence d :=
    originalDoubleCylinderComparison_weakEquivalence f hf (0 : X ⟶ Z₀) kY k₀ sq₀
  have hw : WeakEquivalence (e.inv ≫ d) := by infer_instance
  have hInv : e.inv ≫ d = c := by
    rw [← hCompare, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  change WeakEquivalence c
  exact hInv ▸ hw

/-- Every actual caller comparison map retains the original target-to-quotient square. -/
@[reassoc]
theorem originalScalarCofiberQuotientComparison_caller_map
    {X Y Z P P' : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (f : X ⟶ Y) (z : X ⟶ Z) (hZ : IsZero Z)
    (kY : Y ⟶ P) (kZ : Z ⟶ P) (sq : IsPushout f z kY kZ)
    (kY' : Y ⟶ P') (kZ' : Z ⟶ P') (sq' : IsPushout f z kY' kZ')
    (g : P ⟶ P') (hY : kY ≫ g = kY') :
    originalScalarCofiberQuotientComparison f z hZ kY kZ sq ≫ g =
      originalScalarCofiberQuotientComparison f z hZ kY' kZ' sq' := by
  apply (OriginalScalarCone.cofiberIsPushout EnrichedIntervalCylinder.functor
    (inclusionNatTrans 0) (inclusionNatTrans 1) f).hom_ext
  · rw [originalScalarCofiberQuotientComparison_target_assoc, hY,
      originalScalarCofiberQuotientComparison_target]
  · rw [originalScalarCofiberQuotientComparison_cone_assoc, zero_comp,
      originalScalarCofiberQuotientComparison_cone]

/-- Original scalar suspension uses the explicit original native zero diagram. -/
abbrev originalScalarSuspensionFunctor : EnrichedFunctorCat PointedCGWH.{u, v} I ⥤
    EnrichedFunctorCat PointedCGWH.{u, v} I :=
  OriginalScalarCone.suspensionFunctor EnrichedIntervalCylinder.functor
    (inclusionNatTrans 0) (inclusionNatTrans 1)
    HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero

/-- The actual native scalar suspension retains its full original cone quotient. -/
abbrev originalScalarSuspensionQuotient (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    originalConeFunctor.obj X ⟶ originalScalarSuspensionFunctor.obj X :=
  OriginalScalarCone.suspensionQuotient EnrichedIntervalCylinder.functor
    (inclusionNatTrans 0) (inclusionNatTrans 1)
    HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero X

/-- The actual native scalar boundary keeps the original target and cone maps. -/
abbrev originalScalarBoundary (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    originalScalarCofiberFunctor.obj f ⟶ originalScalarSuspensionFunctor.obj f.left :=
  OriginalScalarCone.boundary EnrichedIntervalCylinder.functor
    (inclusionNatTrans 0) (inclusionNatTrans 1)
    HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero f

/-- Every actual original native arrow square retains the full scalar boundary square. -/
@[reassoc]
theorem originalScalarBoundary_naturality
    {f g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)} (sq : f ⟶ g) :
    originalScalarCofiberFunctor.map sq ≫ originalScalarBoundary g =
      originalScalarBoundary f ≫ originalScalarSuspensionFunctor.map sq.left :=
  OriginalScalarCone.boundary_naturality EnrichedIntervalCylinder.functor
    (inclusionNatTrans 0) (inclusionNatTrans 1)
    HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero sq

/-- Original scalar rotation retains the complete target-to-cofiber Arrow functor. -/
abbrev originalScalarRotationFunctor : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I) ⥤
    EnrichedFunctorCat PointedCGWH.{u, v} I :=
  OriginalScalarCone.rotationFunctor EnrichedIntervalCylinder.functor
    (inclusionNatTrans 0) (inclusionNatTrans 1)

/-- The actual native scalar rotation comparison descends its whole original boundary. -/
abbrev originalScalarRotationComparison
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    originalScalarRotationFunctor.obj f ⟶ originalScalarSuspensionFunctor.obj f.left :=
  OriginalScalarCone.rotationComparison EnrichedIntervalCylinder.functor
    (inclusionNatTrans 0) (inclusionNatTrans 1)
    HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero f

/-- Every full original native arrow square retains the actual scalar rotation comparison. -/
@[reassoc]
theorem originalScalarRotationComparison_naturality
    {f g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)} (sq : f ⟶ g) :
    originalScalarRotationFunctor.map sq ≫ originalScalarRotationComparison g =
      originalScalarRotationComparison f ≫ originalScalarSuspensionFunctor.map sq.left :=
  OriginalScalarCone.rotationComparison_naturality EnrichedIntervalCylinder.functor
    (inclusionNatTrans 0) (inclusionNatTrans 1)
    HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero sq

/-- The actual original scalar rotation comparison is level weak for every original arrow.
Its target inclusion has derived HEP; no source cofibrancy or weak-gluing premise is required. -/
theorem originalScalarRotationComparison_weakEquivalence
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    WeakEquivalence (originalScalarRotationComparison f) := by
  let hZ := HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero (A := I)
  let sq := OriginalScalarCone.boundaryIsPushout EnrichedIntervalCylinder.functor
    (inclusionNatTrans 0) (inclusionNatTrans 1) hZ f
  exact originalScalarCofiberQuotientComparison_weakEquivalence
    (OriginalScalarCone.cofiberTarget EnrichedIntervalCylinder.functor
      (inclusionNatTrans 0) (inclusionNatTrans 1) f.hom)
    (originalScalarCofiberTarget_basedHEP f.hom) (hZ.from_ f.right) hZ
    (originalScalarBoundary f)
    (OriginalScalarCone.suspensionZeroLeg EnrichedIntervalCylinder.functor
      (inclusionNatTrans 0) (inclusionNatTrans 1) hZ f.left) sq

/-- The neutral Puppe API receives the exact current scalar-cofiber cocone and both legs. -/
def originalChosenScalarCofiberCone
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    PushoutCocone (originalConeInclusion.app f.left) f.hom := by
  let kC : originalConeFunctor.obj f.left ⟶ originalScalarCofiberFunctor.obj f :=
    OriginalScalarCone.cofiberCone EnrichedIntervalCylinder.functor
      (inclusionNatTrans 0) (inclusionNatTrans 1) f.hom
  let kY : f.right ⟶ originalScalarCofiberFunctor.obj f :=
    OriginalScalarCone.cofiberTarget EnrichedIntervalCylinder.functor
      (inclusionNatTrans 0) (inclusionNatTrans 1) f.hom
  exact PushoutCocone.mk kC kY
    (OriginalScalarCone.cofiber_condition EnrichedIntervalCylinder.functor
      (inclusionNatTrans 0) (inclusionNatTrans 1) f.hom).symm

/-- The neutral chosen scalar cofiber retains the actual original colimit witness. -/
def originalChosenScalarCofiberIsColimit
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    IsColimit (originalChosenScalarCofiberCone f) :=
  (OriginalScalarCone.cofiberIsPushout EnrichedIntervalCylinder.functor
    (inclusionNatTrans 0) (inclusionNatTrans 1) f.hom).flip.isColimit

/-- Every neutral Puppe arrow map is the entire same original scalar-cofiber map. -/
theorem originalPuppeCofiberMap_eq
    {f g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)} (sq : f ⟶ g) :
    OrdinaryHoChosenPuppe.cofiberMap originalConeFunctor originalConeInclusion
      originalChosenScalarCofiberCone originalChosenScalarCofiberIsColimit sq =
        originalScalarCofiberFunctor.map sq := by
  let m : originalScalarCofiberFunctor.obj f ⟶ originalScalarCofiberFunctor.obj g :=
    OrdinaryHoChosenPuppe.cofiberMap originalConeFunctor originalConeInclusion
      originalChosenScalarCofiberCone originalChosenScalarCofiberIsColimit sq
  let iF : f.right ⟶ originalScalarCofiberFunctor.obj f :=
    OriginalScalarCone.cofiberTarget EnrichedIntervalCylinder.functor
      (inclusionNatTrans 0) (inclusionNatTrans 1) f.hom
  let iG : g.right ⟶ originalScalarCofiberFunctor.obj g :=
    OriginalScalarCone.cofiberTarget EnrichedIntervalCylinder.functor
      (inclusionNatTrans 0) (inclusionNatTrans 1) g.hom
  let qF : originalConeFunctor.obj f.left ⟶ originalScalarCofiberFunctor.obj f :=
    OriginalScalarCone.cofiberCone EnrichedIntervalCylinder.functor
      (inclusionNatTrans 0) (inclusionNatTrans 1) f.hom
  let qG : originalConeFunctor.obj g.left ⟶ originalScalarCofiberFunctor.obj g :=
    OriginalScalarCone.cofiberCone EnrichedIntervalCylinder.functor
      (inclusionNatTrans 0) (inclusionNatTrans 1) g.hom
  have hY : iF ≫ m = sq.right ≫ iG := OrdinaryHoChosenPuppe.cofiberMap_target
    originalConeFunctor originalConeInclusion originalChosenScalarCofiberCone
    originalChosenScalarCofiberIsColimit sq
  have hC : qF ≫ m = originalConeFunctor.map sq.left ≫ qG :=
    OrdinaryHoChosenPuppe.cofiberMap_cone originalConeFunctor originalConeInclusion
      originalChosenScalarCofiberCone originalChosenScalarCofiberIsColimit sq
  have sqF : IsPushout f.hom (originalConeInclusion.app f.left) iF qF :=
    OriginalScalarCone.cofiberIsPushout EnrichedIntervalCylinder.functor
      (inclusionNatTrans 0) (inclusionNatTrans 1) f.hom
  apply sqF.hom_ext
  · change iF ≫ m = iF ≫ originalScalarCofiberFunctor.map sq
    exact hY.trans
      (OriginalScalarCone.cofiberTarget_map EnrichedIntervalCylinder.functor
        (inclusionNatTrans 0) (inclusionNatTrans 1) sq).symm
  · change qF ≫ m = qF ≫ originalScalarCofiberFunctor.map sq
    exact hC.trans
      (OriginalScalarCone.cofiberCone_map EnrichedIntervalCylinder.functor
        (inclusionNatTrans 0) (inclusionNatTrans 1) sq).symm

/-- The complete original neutral scalar cofiber functor has the same actual carrier and maps. -/
def originalPuppeCofiberNatIso :
    OrdinaryHoChosenPuppe.cofiberFunctor (originalConeFunctor (I := I))
      (originalConeInclusion (I := I)) (originalChosenScalarCofiberCone (I := I))
      (originalChosenScalarCofiberIsColimit (I := I)) ≅
        originalScalarCofiberFunctor (I := I) :=
  NatIso.ofComponents (fun f => Iso.refl _) (fun sq => by
    change OrdinaryHoChosenPuppe.cofiberMap originalConeFunctor originalConeInclusion
      originalChosenScalarCofiberCone originalChosenScalarCofiberIsColimit sq ≫ 𝟙 _ =
        𝟙 _ ≫ originalScalarCofiberFunctor.map sq
    rw [Category.id_comp, Category.comp_id, originalPuppeCofiberMap_eq])

/-- Every neutral original suspended map is the same actual scalar-suspension functor map. -/
theorem originalPuppeSuspensionMap_eq
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    OrdinaryHoChosenPuppe.suspensionMap originalConeFunctor originalConeInclusion
      originalChosenScalarCofiberCone originalChosenScalarCofiberIsColimit
      HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram
      HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero f =
        originalScalarSuspensionFunctor.map f := by
  let hZ := HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero (A := I)
  have hq : (OrdinaryHoChosenPuppe.zeroArrowFunctor _ hZ).map f =
      (originalTerminalArrowFunctor hZ).map f := by
    apply Arrow.hom_ext <;> rfl
  change OrdinaryHoChosenPuppe.cofiberMap originalConeFunctor originalConeInclusion
    originalChosenScalarCofiberCone originalChosenScalarCofiberIsColimit
    ((OrdinaryHoChosenPuppe.zeroArrowFunctor _ hZ).map f) =
      originalScalarCofiberFunctor.map ((originalTerminalArrowFunctor hZ).map f)
  rw [originalPuppeCofiberMap_eq, hq]
  rfl

/-- The first collapse of both actual scalar cones is level weak on every native object. -/
theorem originalPuppeCollapseLeft_weakEquivalence
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    WeakEquivalence (OrdinaryHoChosenPuppeRotation.collapseLeft
      originalConeFunctor originalConeInclusion originalChosenScalarCofiberCone
      originalChosenScalarCofiberIsColimit
      HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram
      HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero X) := by
  let Z := HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram (A := I)
  let hZ : IsZero Z := HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero
  let σ := OrdinaryHoChosenPuppe.suspensionCone originalConeFunctor originalConeInclusion
    originalChosenScalarCofiberCone Z hZ X
  let D := OrdinaryHoChosenPuppeRotation.doubleCone originalConeFunctor originalConeInclusion
    originalChosenScalarCofiberCone X
  let z : X ⟶ Z := OrdinaryHoChosenPuppe.toZero Z hZ X
  have sqσ : IsPushout (originalConeInclusion.app X) z σ.inl σ.inr :=
    IsPushout.of_isColimit (originalChosenScalarCofiberIsColimit (Arrow.mk z))
  let c : D.pt ⟶ σ.pt := originalScalarCofiberQuotientComparison
    (originalConeInclusion.app X) z hZ σ.inl σ.inr sqσ
  let L : D.pt ⟶ σ.pt := OrdinaryHoChosenPuppeRotation.collapseLeft
    originalConeFunctor originalConeInclusion originalChosenScalarCofiberCone
    originalChosenScalarCofiberIsColimit Z hZ X
  have hL : L = c := by
    have hC : D.inl ≫ L = 0 := by
      have h := OrdinaryHoChosenPuppeRotation.collapseLeft_left
        originalConeFunctor originalConeInclusion originalChosenScalarCofiberCone
        originalChosenScalarCofiberIsColimit Z hZ X
      have hz : OrdinaryHoChosenPuppe.toZero Z hZ (originalConeFunctor.obj X) = 0 :=
        hZ.eq_of_tgt _ _
      exact h.trans ((congrArg (fun f => f ≫ σ.inr) hz).trans zero_comp)
    have hY : D.inr ≫ L = σ.inl := OrdinaryHoChosenPuppeRotation.collapseLeft_right
      originalConeFunctor originalConeInclusion originalChosenScalarCofiberCone
      originalChosenScalarCofiberIsColimit Z hZ X
    apply PushoutCocone.IsColimit.hom_ext
      (originalChosenScalarCofiberIsColimit (Arrow.mk (originalConeInclusion.app X)))
    · exact hC.trans
        (originalScalarCofiberQuotientComparison_cone
          (originalConeInclusion.app X) z hZ σ.inl σ.inr sqσ).symm
    · exact hY.trans
        (originalScalarCofiberQuotientComparison_target
          (originalConeInclusion.app X) z hZ σ.inl σ.inr sqσ).symm
  have hc : WeakEquivalence c := originalScalarCofiberQuotientComparison_weakEquivalence
    (originalConeInclusion.app X) (originalConeInclusion_basedHEP X) z hZ σ.inl σ.inr sqσ
  change WeakEquivalence L
  exact hL.symm ▸ hc

/-- Exchange of the same two original scalar cones is the complete original involution Iso. -/
def originalPuppeDoubleConeSwapIso (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (OrdinaryHoChosenPuppeRotation.doubleCone originalConeFunctor originalConeInclusion
      originalChosenScalarCofiberCone X).pt ≅
    (OrdinaryHoChosenPuppeRotation.doubleCone originalConeFunctor originalConeInclusion
      originalChosenScalarCofiberCone X).pt where
  hom := OrdinaryHoChosenPuppeRotation.doubleConeSwap originalConeFunctor originalConeInclusion
    originalChosenScalarCofiberCone originalChosenScalarCofiberIsColimit X
  inv := OrdinaryHoChosenPuppeRotation.doubleConeSwap originalConeFunctor originalConeInclusion
    originalChosenScalarCofiberCone originalChosenScalarCofiberIsColimit X
  hom_inv_id := OrdinaryHoChosenPuppeRotation.doubleConeSwap_involutive
    originalConeFunctor originalConeInclusion originalChosenScalarCofiberCone
    originalChosenScalarCofiberIsColimit X
  inv_hom_id := OrdinaryHoChosenPuppeRotation.doubleConeSwap_involutive
    originalConeFunctor originalConeInclusion originalChosenScalarCofiberCone
    originalChosenScalarCofiberIsColimit X

/-- The second actual scalar double-cone collapse is level weak on every native object. -/
theorem originalPuppeCollapseRight_weakEquivalence
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    WeakEquivalence (OrdinaryHoChosenPuppeRotation.collapseRight
      originalConeFunctor originalConeInclusion originalChosenScalarCofiberCone
      originalChosenScalarCofiberIsColimit
      HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram
      HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero X) := by
  let Z := HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram (A := I)
  let hZ : IsZero Z := HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero
  let L := OrdinaryHoChosenPuppeRotation.collapseLeft
    originalConeFunctor originalConeInclusion originalChosenScalarCofiberCone
    originalChosenScalarCofiberIsColimit Z hZ X
  let R := OrdinaryHoChosenPuppeRotation.collapseRight
    originalConeFunctor originalConeInclusion originalChosenScalarCofiberCone
    originalChosenScalarCofiberIsColimit Z hZ X
  let e := originalPuppeDoubleConeSwapIso X
  let _ : WeakEquivalence L := originalPuppeCollapseLeft_weakEquivalence X
  have hw : WeakEquivalence (e.hom ≫ L) := by infer_instance
  have h : e.hom ≫ L = R := OrdinaryHoChosenPuppeRotation.doubleConeSwap_collapseLeft
    originalConeFunctor originalConeInclusion originalChosenScalarCofiberCone
    originalChosenScalarCofiberIsColimit Z hZ X
  change WeakEquivalence R
  exact h ▸ hw

/-- A genuinely cofibrant source has its actual scalar cone inclusion as an original cofibration. -/
theorem originalConeInclusion_cofibration
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) [IsCofibrant X] :
    Cofibration (originalConeInclusion.app X) := by
  have sq := OriginalScalarCone.coneJointIsPushout EnrichedIntervalCylinder.functor
    (inclusionNatTrans 0) (inclusionNatTrans 1) X
  let _ : Cofibration (PointedCGWH.EnrichedIntervalCylinderModel.jointMap X) :=
    PointedCGWH.EnrichedIntervalCylinderModel.jointMap_cofibration X
  apply (HomotopicalAlgebra.cofibration_iff _).mpr
  exact (HomotopicalAlgebra.cofibrations
    (EnrichedFunctorCat PointedCGWH.{u, v} I)).of_isPushout sq.flip
    (mem_cofibrations (PointedCGWH.EnrichedIntervalCylinderModel.jointMap X))

/-- The two actual scalar double-cone collapses construct reversal in original LEVEL Ho.
Every native source is allowed, including sources without q-cofibrancy. -/
def originalScalarSuspensionReversal
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
      (OrdinaryHoChosenPuppe.suspensionCone originalConeFunctor originalConeInclusion
        originalChosenScalarCofiberCone
        HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram
        HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero X).pt ≅
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
      (OrdinaryHoChosenPuppe.suspensionCone originalConeFunctor originalConeInclusion
        originalChosenScalarCofiberCone
        HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram
        HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero X).pt := by
  let H := toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)
  let Z := HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram (A := I)
  let hZ : IsZero Z := HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero
  let L := OrdinaryHoChosenPuppeRotation.collapseLeft
    originalConeFunctor originalConeInclusion originalChosenScalarCofiberCone
    originalChosenScalarCofiberIsColimit Z hZ X
  let R := OrdinaryHoChosenPuppeRotation.collapseRight
    originalConeFunctor originalConeInclusion originalChosenScalarCofiberCone
    originalChosenScalarCofiberIsColimit Z hZ X
  let _ : WeakEquivalence L := originalPuppeCollapseLeft_weakEquivalence X
  let _ : WeakEquivalence R := originalPuppeCollapseRight_weakEquivalence X
  let _ : IsIso (H.map L) :=
    Localization.inverts H (weakEquivalences _) L (mem_weakEquivalences L)
  let _ : IsIso (H.map R) :=
    Localization.inverts H (weakEquivalences _) R (mem_weakEquivalences R)
  exact (asIso (H.map L)).symm ≪≫ asIso (H.map R)

/-- The unrestricted actual reversal sends the entire first collapse to the second. -/
theorem originalCollapseLeft_reversal
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
      (OrdinaryHoChosenPuppeRotation.collapseLeft originalConeFunctor originalConeInclusion
        originalChosenScalarCofiberCone originalChosenScalarCofiberIsColimit
        HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram
        HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero X) ≫
      (originalScalarSuspensionReversal X).hom =
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
      (OrdinaryHoChosenPuppeRotation.collapseRight originalConeFunctor originalConeInclusion
        originalChosenScalarCofiberCone originalChosenScalarCofiberIsColimit
        HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram
        HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero X) := by
  simp only [originalScalarSuspensionReversal, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, asIso_inv, IsIso.hom_inv_id_assoc]

/-- The unrestricted actual reversal also sends the whole second collapse to the first. -/
theorem originalCollapseRight_reversal
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
      (OrdinaryHoChosenPuppeRotation.collapseRight originalConeFunctor originalConeInclusion
        originalChosenScalarCofiberCone originalChosenScalarCofiberIsColimit
        HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram
        HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero X) ≫
      (originalScalarSuspensionReversal X).hom =
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
      (OrdinaryHoChosenPuppeRotation.collapseLeft originalConeFunctor originalConeInclusion
        originalChosenScalarCofiberCone originalChosenScalarCofiberIsColimit
        HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram
        HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero X) := by
  rw [← OrdinaryHoChosenPuppeRotation.doubleConeSwap_collapseLeft
    originalConeFunctor originalConeInclusion originalChosenScalarCofiberCone
    originalChosenScalarCofiberIsColimit, Functor.map_comp, Category.assoc,
    originalCollapseLeft_reversal, ← Functor.map_comp,
    OrdinaryHoChosenPuppeRotation.doubleConeSwap_collapseRight]

/-- Both original actual double-cone maps prove the unrestricted reversal is an involution. -/
theorem originalScalarSuspensionReversal_involutive
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (originalScalarSuspensionReversal X).hom ≫ (originalScalarSuspensionReversal X).hom = 𝟙 _ := by
  let H := toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)
  let Z := HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram (A := I)
  let hZ : IsZero Z := HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero
  let L := OrdinaryHoChosenPuppeRotation.collapseLeft
    originalConeFunctor originalConeInclusion originalChosenScalarCofiberCone
    originalChosenScalarCofiberIsColimit Z hZ X
  let _ : WeakEquivalence L := originalPuppeCollapseLeft_weakEquivalence X
  let _ : IsIso (H.map L) :=
    Localization.inverts H (weakEquivalences _) L (mem_weakEquivalences L)
  apply (cancel_epi (H.map L)).mp
  rw [← Category.assoc, originalCollapseLeft_reversal,
    originalCollapseRight_reversal, Category.comp_id]

/-- Unrestricted actual scalar reversal retains the whole original suspended source map. -/
theorem originalScalarSuspensionReversal_naturality
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
      (OrdinaryHoChosenPuppe.suspensionMap originalConeFunctor originalConeInclusion
        originalChosenScalarCofiberCone originalChosenScalarCofiberIsColimit
        HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram
        HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero f) ≫
      (originalScalarSuspensionReversal Y).hom =
    (originalScalarSuspensionReversal X).hom ≫
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
        (OrdinaryHoChosenPuppe.suspensionMap originalConeFunctor originalConeInclusion
          originalChosenScalarCofiberCone originalChosenScalarCofiberIsColimit
          HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram
          HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero f) := by
  let H := toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)
  let Z := HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram (A := I)
  let hZ : IsZero Z := HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero
  let L := OrdinaryHoChosenPuppeRotation.collapseLeft
    originalConeFunctor originalConeInclusion originalChosenScalarCofiberCone
    originalChosenScalarCofiberIsColimit Z hZ X
  let _ : WeakEquivalence L := originalPuppeCollapseLeft_weakEquivalence X
  let _ : IsIso (H.map L) :=
    Localization.inverts H (weakEquivalences _) L (mem_weakEquivalences L)
  apply (cancel_epi (H.map L)).mp
  rw [← Category.assoc, ← Functor.map_comp,
    ← OrdinaryHoChosenPuppeRotation.collapseLeft_naturality,
    Functor.map_comp, Category.assoc, originalCollapseLeft_reversal,
    ← Functor.map_comp, OrdinaryHoChosenPuppeRotation.collapseRight_naturality,
    Functor.map_comp, ← Category.assoc, originalCollapseLeft_reversal]

/-- The actual next boundary is rotation followed by the original suspended map and reversal.
Every source and target is allowed; neither endpoint is required to be cofibrant. -/
theorem originalPuppeRotation_boundary
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
      (OrdinaryHoChosenPuppeRotation.rotationComparison
        originalConeFunctor originalConeInclusion originalChosenScalarCofiberCone
        originalChosenScalarCofiberIsColimit
        HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram
        HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero f) ≫
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
      (OrdinaryHoChosenPuppe.suspensionMap originalConeFunctor originalConeInclusion
        originalChosenScalarCofiberCone originalChosenScalarCofiberIsColimit
        HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram
        HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero f.hom) ≫
      (originalScalarSuspensionReversal f.right).hom =
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
      (OrdinaryHoChosenPuppe.boundary originalConeFunctor originalConeInclusion
        originalChosenScalarCofiberCone originalChosenScalarCofiberIsColimit
        HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram
        HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero
        (OrdinaryHoChosenPuppeRotation.targetArrow originalConeFunctor originalConeInclusion
          originalChosenScalarCofiberCone f)) := by
  rw [← Category.assoc, ← Functor.map_comp,
    ← OrdinaryHoChosenPuppeRotation.rotationToDoubleCone_collapseLeft,
    Functor.map_comp, Category.assoc, originalCollapseLeft_reversal,
    ← Functor.map_comp, OrdinaryHoChosenPuppeRotation.rotationToDoubleCone_collapseRight]

/-- A null actual coefficient map extends through its original scalar cone.
Only the coefficient source is cofibrant; every actual native target is fibrant. -/
theorem originalConeExtension_of_null
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (K E : EnrichedFunctorCat PointedCGWH.{u, v} I) [IsCofibrant K] (g : K ⟶ E)
    (hg : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map g =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map (0 : K ⟶ E)) :
    ∃ h : originalConeFunctor.obj K ⟶ E, originalConeInclusion.app K ≫ h = g := by
  let Z := HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram (A := I)
  let hZ : IsZero Z := HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero
  let H := toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)
  let _ : IsFibrant E := HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant E
  let _ : Cofibration (originalConeInclusion.app K) := originalConeInclusion_cofibration K
  have hNull : OrdinaryHoChosenPuppe.nullMap Z hZ K E = (0 : K ⟶ E) := by
    change OrdinaryHoChosenPuppe.toZero Z hZ K ≫ OrdinaryHoChosenPuppe.fromZero Z hZ E = 0
    rw [hZ.eq_of_tgt (OrdinaryHoChosenPuppe.toZero Z hZ K) 0, zero_comp]
  exact OrdinaryHoChosenFiberCofiberComparison.coneExtension_of_null
    Z hZ originalConeFunctor originalConeInclusion g (hg.trans (H.congr_map hNull.symm))

/-- A null original coefficient in the actual scalar cofiber has a suspended preimage.
The source and target of f are arbitrary. Only the actual sphere coefficient K is cofibrant. -/
theorem originalScalarCoefficientLift_of_null
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (K : EnrichedFunctorCat PointedCGWH.{u, v} I) [IsCofibrant K] (g : K ⟶ f.right)
    (hg : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
        (g ≫ OriginalScalarCone.cofiberTarget EnrichedIntervalCylinder.functor
          (inclusionNatTrans 0) (inclusionNatTrans 1) f.hom) =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
        (0 : K ⟶ originalScalarCofiberFunctor.obj f)) :
    ∃ k : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
        (OrdinaryHoChosenPuppe.suspensionCone originalConeFunctor originalConeInclusion
          originalChosenScalarCofiberCone
          HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram
          HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero K).pt ⟶
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
        (OrdinaryHoChosenPuppe.suspensionCone originalConeFunctor originalConeInclusion
          originalChosenScalarCofiberCone
          HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram
          HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero f.left).pt,
      k ≫ (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
          (originalScalarSuspensionFunctor.map f.hom) =
        (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
          (originalScalarSuspensionFunctor.map g) := by
  let H := toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)
  let Z := HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram (A := I)
  let hZ : IsZero Z := HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero
  obtain ⟨h, hh⟩ := originalConeExtension_of_null K
    (originalChosenScalarCofiberCone f).pt (g ≫ (originalChosenScalarCofiberCone f).inr) hg
  let q := OrdinaryHoChosenFiberCofiberComparison.coneToCofiberSquare
    originalConeFunctor originalConeInclusion originalChosenScalarCofiberCone f K g h hh
  let A := H.map (OrdinaryHoChosenPuppeRotation.collapseRight
    originalConeFunctor originalConeInclusion originalChosenScalarCofiberCone
    originalChosenScalarCofiberIsColimit Z hZ K)
  let _ : IsIso A := Localization.inverts H (weakEquivalences _)
    (OrdinaryHoChosenPuppeRotation.collapseRight originalConeFunctor originalConeInclusion
      originalChosenScalarCofiberCone originalChosenScalarCofiberIsColimit Z hZ K)
    (originalPuppeCollapseRight_weakEquivalence K).mem
  let rK := originalScalarSuspensionReversal K
  let rY := originalScalarSuspensionReversal f.right
  let u := inv A ≫ H.map (OrdinaryHoChosenPuppe.cofiberMap
      originalConeFunctor originalConeInclusion originalChosenScalarCofiberCone
      originalChosenScalarCofiberIsColimit q) ≫
    H.map (OrdinaryHoChosenPuppeRotation.rotationComparison
      originalConeFunctor originalConeInclusion originalChosenScalarCofiberCone
      originalChosenScalarCofiberIsColimit Z hZ f)
  have hBoundary : H.map (OrdinaryHoChosenPuppe.cofiberMap
      originalConeFunctor originalConeInclusion originalChosenScalarCofiberCone
      originalChosenScalarCofiberIsColimit q) ≫
    H.map (OrdinaryHoChosenPuppe.boundary
      originalConeFunctor originalConeInclusion originalChosenScalarCofiberCone
      originalChosenScalarCofiberIsColimit Z hZ
      (OrdinaryHoChosenPuppeRotation.targetArrow originalConeFunctor originalConeInclusion
        originalChosenScalarCofiberCone f)) =
    A ≫ H.map (OrdinaryHoChosenPuppe.suspensionMap
      originalConeFunctor originalConeInclusion originalChosenScalarCofiberCone
      originalChosenScalarCofiberIsColimit Z hZ g) := by
    have hNat := H.congr_map (OrdinaryHoChosenPuppe.boundary_naturality
      originalConeFunctor originalConeInclusion originalChosenScalarCofiberCone
      originalChosenScalarCofiberIsColimit Z hZ q)
    simp only [Functor.map_comp] at hNat
    exact hNat
  have hRot := originalPuppeRotation_boundary f
  have hReversalY : rY.hom ≫ rY.hom = 𝟙 _ := originalScalarSuspensionReversal_involutive f.right
  have hUg : u ≫ H.map (OrdinaryHoChosenPuppe.suspensionMap
      originalConeFunctor originalConeInclusion originalChosenScalarCofiberCone
      originalChosenScalarCofiberIsColimit Z hZ f.hom) ≫ rY.hom =
    H.map (OrdinaryHoChosenPuppe.suspensionMap
      originalConeFunctor originalConeInclusion originalChosenScalarCofiberCone
      originalChosenScalarCofiberIsColimit Z hZ g) := by
    change (inv A ≫ _ ≫ _) ≫ _ ≫ rY.hom = _
    simp only [Category.assoc]
    rw [hRot, hBoundary]
    rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  have hU : u ≫ H.map (OrdinaryHoChosenPuppe.suspensionMap
      originalConeFunctor originalConeInclusion originalChosenScalarCofiberCone
      originalChosenScalarCofiberIsColimit Z hZ f.hom) =
    H.map (OrdinaryHoChosenPuppe.suspensionMap
      originalConeFunctor originalConeInclusion originalChosenScalarCofiberCone
      originalChosenScalarCofiberIsColimit Z hZ g) ≫ rY.hom := by
    apply (cancel_mono rY.hom).mp
    simp only [Category.assoc]
    rw [hReversalY, Category.comp_id]
    exact hUg
  refine ⟨rK.hom ≫ u, ?_⟩
  have hOld : (rK.hom ≫ u) ≫ H.map (OrdinaryHoChosenPuppe.suspensionMap
      originalConeFunctor originalConeInclusion originalChosenScalarCofiberCone
      originalChosenScalarCofiberIsColimit Z hZ f.hom) =
    H.map (OrdinaryHoChosenPuppe.suspensionMap
      originalConeFunctor originalConeInclusion originalChosenScalarCofiberCone
      originalChosenScalarCofiberIsColimit Z hZ g) := by
    rw [Category.assoc, hU, ← Category.assoc,
      ← originalScalarSuspensionReversal_naturality g,
      Category.assoc, hReversalY, Category.comp_id]
  have hmF : OrdinaryHoChosenPuppe.suspensionMap
      originalConeFunctor originalConeInclusion originalChosenScalarCofiberCone
      originalChosenScalarCofiberIsColimit Z hZ f.hom =
      originalScalarSuspensionFunctor.map f.hom := originalPuppeSuspensionMap_eq f.hom
  have hmG : OrdinaryHoChosenPuppe.suspensionMap
      originalConeFunctor originalConeInclusion originalChosenScalarCofiberCone
      originalChosenScalarCofiberIsColimit Z hZ g =
      originalScalarSuspensionFunctor.map g := originalPuppeSuspensionMap_eq g
  exact (congrArg (fun t => (rK.hom ≫ u) ≫ H.map t) hmF).symm.trans
    (hOld.trans (H.congr_map hmG))


/-- The scalar cofiber retains the canonical ordinary quotient for every native arrow. -/
abbrev originalCanonicalQuotientComparison
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    originalScalarCofiberFunctor.obj f ⟶
      (ordinaryCofiber (C := EnrichedFunctorCat PointedCGWH.{u, v} I)).obj f :=
  OriginalScalarCone.canonicalQuotientComparison EnrichedIntervalCylinder.functor
    (inclusionNatTrans 0) (inclusionNatTrans 1) f

/-- All-target HEP makes the actual canonical quotient comparison level weak. -/
theorem originalCanonicalQuotientComparison_weakEquivalence
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (hf : PointedCGWH.EnrichedBasedHomotopyExtension.property f.hom) :
    WeakEquivalence (originalCanonicalQuotientComparison f) :=
  originalScalarCofiberQuotientComparison_weakEquivalence f.hom hf
    (terminal.from f.left) OriginalScalarCone.terminalIsZero
    (OriginalScalarCone.ordinaryQuotientTarget f)
    (OriginalScalarCone.ordinaryQuotientZero f)
    (OriginalScalarCone.ordinaryQuotientIsPushout f)

/-- The cofiber map across the caller's actual HEP pushout is level weak.
This uses the same pushout twice through its canonical ordinary quotients. -/
theorem originalScalarCofiberMap_weakEquivalence_of_isPushout
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    {A X Z P : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (i : A ⟶ X) (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property i)
    (z : A ⟶ Z) (kX : X ⟶ P) (kZ : Z ⟶ P)
    (sq : IsPushout i z kX kZ) :
    WeakEquivalence (originalScalarCofiberFunctor.map
      (Arrow.homMk (f := Arrow.mk i) (g := Arrow.mk kZ) z kX sq.w.symm)) := by
  let f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I) := Arrow.mk i
  let g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I) := Arrow.mk kZ
  let a : f ⟶ g := Arrow.homMk z kX sq.w.symm
  let m := originalScalarCofiberFunctor.map a
  let n := (ordinaryCofiber (C := EnrichedFunctorCat PointedCGWH.{u, v} I)).map a
  let cF := originalCanonicalQuotientComparison f
  let cG := originalCanonicalQuotientComparison g
  have hkZ : PointedCGWH.EnrichedBasedHomotopyExtension.property kZ :=
    MorphismProperty.of_isPushout sq.flip hi
  let _ : WeakEquivalence cF := originalCanonicalQuotientComparison_weakEquivalence f hi
  let _ : WeakEquivalence cG := originalCanonicalQuotientComparison_weakEquivalence g hkZ
  let _ : IsIso n := OriginalScalarCone.ordinaryCofiberMap_isIso_of_isPushout
    i z kX kZ sq
  let _ : WeakEquivalence (cF ≫ n) := inferInstance
  have h : m ≫ cG = cF ≫ n :=
    OriginalScalarCone.canonicalQuotientComparison_naturality EnrichedIntervalCylinder.functor
      (inclusionNatTrans 0) (inclusionNatTrans 1) a
  exact weakEquivalence_of_postcomp_of_fac h

end PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

namespace PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

open PointedCGWH.Spectra.OriginalHEPHomotopyPushoutComparison

/-- The actual free-source counit retains the literal original realized interval carrier. -/
def originalDiskFreeCounit : PointedCGWH.IntervalCoefficient.interval.{u, v} ⟶
    PointedCGWH.diskOne.{u, v} :=
  Under.freeForgetCounit PointedCGWH.diskOne

/-- The actual free-point collapse retains the original monoidal-unit carrier. -/
def originalFreePointCollapse : (𝟙_ PointedCGWH.{u, v}) ⟶
    (Under.mk (𝟙 CGWH.point.{u, v}) : PointedCGWH.{u, v}) :=
  Under.freePointCollapse

/-- The freely based interval forgets its added point into the original δ0-based disk. -/
def originalCoefficientToDisk : PointedCGWH.IntervalCoefficient.interval.{u, v} ⟶
    PointedCGWH.diskOne.{u, v} :=
  originalCoefficientReflection.hom ≫ originalDiskFreeCounit

/-- The original monoidal unit is the literal ordered disk boundary source. -/
def originalDiskSourceUnitIso : (𝟙_ PointedCGWH.{u, v}) ≅
    Under.mk (coprod.inl : CGWH.point.{u, v} ⟶ CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) := by
  change PointedCGWH.sphereZero.{u, v} ≅
    Under.mk (coprod.inl : CGWH.point.{u, v} ⟶ CGWH.point.{u, v} ⨿ CGWH.point.{u, v})
  have hPoint : PointedCGWH.sphereZero.{u, v}.hom =
      (coprod.inl : CGWH.point.{u, v} ⟶ CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) := by
    change (coprod.inl : CGWH.point.{u, v} ⟶
      CGWH.point.{u, v} ⨿ (CGWH.point.{u, v} ⨿ CGWH.point.{u, v})) ≫
        coprod.desc
          (coprod.inl : CGWH.point.{u, v} ⟶ CGWH.point.{u, v} ⨿ CGWH.point.{u, v})
          (𝟙 (CGWH.point.{u, v} ⨿ CGWH.point.{u, v})) = _
    exact coprod.inl_desc _ _
  exact Under.isoMk (Iso.refl (CGWH.point.{u, v} ⨿ CGWH.point.{u, v}))
    ((Category.comp_id PointedCGWH.sphereZero.hom).trans hPoint)

/-- Reflection carries the original surviving endpoint to the free disk boundary endpoint. -/
@[reassoc]
theorem originalCoefficientToDisk_zero :
    PointedCGWH.IntervalCoefficient.endpoint.{u, v} 0 ≫ originalCoefficientToDisk =
      originalDiskSourceUnitIso.hom ≫ PointedCGWH.diskBoundary := by
  rw [originalCoefficientToDisk, ← Category.assoc, originalCoefficientReflection_zero,
    PointedCGWH.RealizedIntervalContraction.endpoint_one_eq]
  apply Under.UnderMorphism.ext
  change coprod.map (𝟙 CGWH.point) CGWH.intervalZero ≫
      coprod.desc CGWH.intervalOne (𝟙 _) =
    𝟙 _ ≫ coprod.desc CGWH.intervalOne CGWH.intervalZero
  rw [Category.id_comp]
  apply coprod.hom_ext <;> simp

/-- Reflection sends the collapsed endpoint to the actual original disk basepoint. -/
@[reassoc]
theorem originalCoefficientToDisk_one :
    PointedCGWH.IntervalCoefficient.endpoint.{u, v} 1 ≫ originalCoefficientToDisk =
      originalFreePointCollapse ≫ Under.mkIdInitial.to PointedCGWH.diskOne := by
  rw [originalCoefficientToDisk, ← Category.assoc, originalCoefficientReflection_one,
    PointedCGWH.RealizedIntervalContraction.endpoint_zero_eq]
  exact (Under.freeSourcePresentationIsPushout PointedCGWH.diskOne).w

/-- The exact reflected coefficient collapse is the full original disk pushout. -/
theorem originalCoefficientToDisk_isPushout :
    IsPushout (PointedCGWH.IntervalCoefficient.endpoint.{u, v} 1)
      originalFreePointCollapse originalCoefficientToDisk
      (Under.mkIdInitial.to PointedCGWH.diskOne) := by
  have h : IsPushout (PointedCGWH.IntervalCoefficient.endpoint 0)
      originalFreePointCollapse originalDiskFreeCounit
      (Under.mkIdInitial.to PointedCGWH.diskOne) := by
    rw [PointedCGWH.RealizedIntervalContraction.endpoint_zero_eq]
    exact Under.freeSourcePresentationIsPushout PointedCGWH.diskOne.{u, v}
  apply h.of_iso (Iso.refl _) originalCoefficientReflection.symm (Iso.refl _) (Iso.refl _)
  · have he : PointedCGWH.IntervalCoefficient.endpoint.{u, v} 1 ≫
        originalCoefficientReflection.hom = PointedCGWH.IntervalCoefficient.endpoint 0 :=
      originalCoefficientReflection_one
    have hr : (PointedCGWH.IntervalCoefficient.endpoint.{u, v} 1 ≫
        originalCoefficientReflection.hom) ≫ originalCoefficientReflection.inv =
        PointedCGWH.IntervalCoefficient.endpoint 1 := by
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have hi : PointedCGWH.IntervalCoefficient.endpoint.{u, v} 0 ≫
        originalCoefficientReflection.inv = PointedCGWH.IntervalCoefficient.endpoint 1 :=
      (congrArg (fun k => k ≫ originalCoefficientReflection.inv) he).symm.trans hr
    exact hi
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · have hr : originalCoefficientReflection.inv ≫
        (originalCoefficientReflection.hom ≫ originalDiskFreeCounit) =
        originalDiskFreeCounit := originalCoefficientReflection.inv_hom_id_assoc _
    exact (Category.comp_id originalDiskFreeCounit).trans hr.symm
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

end PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

namespace PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

open PointedCGWH.EnrichedIntervalCylinder

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
attribute [local instance] MonoidalClosed.enrichedCategorySelf
  PointedCGWH.EnrichedMapping.hasSmallLimits
  HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.nativeHasZeroObject
  HasZeroObject.zeroMorphismsOfZeroObject

private instance originalScalarPreservesColimits
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    PreservesColimits (WeightedEndVariance.tensorBifunctor.flip.obj X) :=
  (PointedCGWH.EnrichedFunctorMapping.tensorMappingAdjunction X).leftAdjoint_preservesColimits

/-- The original identity-point coefficient tensors to an actual native zero object. -/
def originalIdentityCoefficientZeroIso (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    tensorLeftObject (Under.mk (𝟙 CGWH.point.{u, v})) X ≅
      (0 : EnrichedFunctorCat PointedCGWH.{u, v} I) := by
  apply IsZero.iso _ (isZero_zero _)
  apply EnrichedZeroCompletion.diagram_isZero_of_obj_isZero
  intro a
  have hZ : IsZero (Under.mk (𝟙 CGWH.point.{u, v}) : PointedCGWH.{u, v}) :=
    { unique_to := fun Y =>
        ⟨{ default := Under.mkIdInitial.to Y
           uniq := fun f => Under.mkIdInitial.hom_ext f _ }⟩
      unique_from := fun Y =>
        ⟨{ default := Under.homMk (CGWH.point_isTerminal.from Y.right)
              (CGWH.point_isTerminal.hom_ext _ _)
           uniq := fun f => Under.UnderMorphism.ext
              (CGWH.point_isTerminal.hom_ext f.right _) }⟩ }
  change IsZero ((Under.mk (𝟙 CGWH.point.{u, v}) : PointedCGWH.{u, v}) ⊗
    X.toEnrichedFunctor.obj a)
  exact EnrichedZeroCompletion.tensor_isZero_left hZ (X.toEnrichedFunctor.obj a)

/-- The actual reflected coefficient disk presentation tensors to every original native diagram. -/
theorem originalDiskTensorIsPushout (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    IsPushout (inclusion 1 X) (0 : X ⟶ (0 : EnrichedFunctorCat PointedCGWH.{u, v} I))
      (scalarTensorMap originalCoefficientToDisk X)
      (0 : (0 : EnrichedFunctorCat PointedCGWH.{u, v} I) ⟶
        tensorLeftObject PointedCGWH.diskOne X) := by
  let F := WeightedEndVariance.tensorBifunctor.flip.obj X
  let h := originalCoefficientToDisk_isPushout.map F
  let eZ := originalIdentityCoefficientZeroIso X
  apply h.of_iso (scalarUnitIso X) (Iso.refl _) eZ (Iso.refl _)
  · change scalarTensorMap (PointedCGWH.IntervalCoefficient.endpoint 1) X ≫ 𝟙 _ =
      (scalarUnitIso X).hom ≫ inclusion 1 X
    rw [Category.comp_id, inclusion_eq, Iso.hom_inv_id_assoc]
  · exact (isZero_zero (EnrichedFunctorCat PointedCGWH.{u, v} I)).isTerminal.hom_ext _ _
  · change scalarTensorMap originalCoefficientToDisk X ≫ 𝟙 _ =
      𝟙 _ ≫ scalarTensorMap originalCoefficientToDisk X
    rw [Category.comp_id, Category.id_comp]
  · exact ((isZero_zero (EnrichedFunctorCat PointedCGWH.{u, v} I)).of_iso eZ).isInitial.hom_ext _ _

/-- The original scalar cone is canonically the original reflected disk tensor, for every source. -/
def originalConeDiskIso (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    originalConeFunctor.obj X ≅ tensorLeftObject PointedCGWH.diskOne X :=
  (OriginalScalarCone.coneIsPushout EnrichedIntervalCylinder.functor
    (inclusionNatTrans 1) X).isoIsPushout _ _ (originalDiskTensorIsPushout X)

/-- The full original interval leg becomes the exact reflected coefficient disk map. -/
@[reassoc]
theorem originalConeDiskIso_quotient (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    originalConeQuotient X ≫ (originalConeDiskIso X).hom =
      scalarTensorMap originalCoefficientToDisk X :=
  (OriginalScalarCone.coneIsPushout EnrichedIntervalCylinder.functor
    (inclusionNatTrans 1) X).inl_isoIsPushout_hom _ _ (originalDiskTensorIsPushout X)

/-- The surviving original source endpoint becomes the actual ordered disk boundary map. -/
@[reassoc]
theorem originalConeDiskIso_inclusion (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    originalConeInclusion.app X ≫ (originalConeDiskIso X).hom =
      (scalarUnitIso X).inv ≫ scalarTensorMap originalDiskSourceUnitIso.hom X ≫
        scalarTensorMap PointedCGWH.diskBoundary X := by
  change (inclusion 0 X ≫ originalConeQuotient X) ≫ (originalConeDiskIso X).hom = _
  rw [Category.assoc, originalConeDiskIso_quotient, inclusion_eq, Category.assoc,
    ← scalarTensorMap_comp, originalCoefficientToDisk_zero, scalarTensorMap_comp]

/-- The full disk cone comparison is natural in every actual original native transformation. -/
@[reassoc]
theorem originalConeDiskIso_naturality
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    originalConeFunctor.map f ≫ (originalConeDiskIso Y).hom =
      (originalConeDiskIso X).hom ≫ tensorLeftMap PointedCGWH.diskOne f := by
  have sq := OriginalScalarCone.coneIsPushout EnrichedIntervalCylinder.functor
    (inclusionNatTrans 1) X
  have hx : OriginalScalarCone.quotient EnrichedIntervalCylinder.functor
      (inclusionNatTrans 1) X ≫ (originalConeDiskIso X).hom =
      scalarTensorMap originalCoefficientToDisk X := originalConeDiskIso_quotient X
  have hy : OriginalScalarCone.quotient EnrichedIntervalCylinder.functor
      (inclusionNatTrans 1) Y ≫ (originalConeDiskIso Y).hom =
      scalarTensorMap originalCoefficientToDisk Y := originalConeDiskIso_quotient Y
  have hn : EnrichedIntervalCylinder.functor.map f ≫
      scalarTensorMap originalCoefficientToDisk Y =
      scalarTensorMap originalCoefficientToDisk X ≫ tensorLeftMap PointedCGWH.diskOne f :=
    scalarTensorMap_diagram_naturality originalCoefficientToDisk f
  apply sq.hom_ext
  · rw [← Category.assoc,
      ← OriginalScalarCone.quotient_naturality EnrichedIntervalCylinder.functor
        (inclusionNatTrans 1) f,
      Category.assoc, hy, hn, ← Category.assoc, hx]
    rfl
  · exact (isZero_zero (EnrichedFunctorCat PointedCGWH.{u, v} I)).isInitial.hom_ext _ _

/-- The entire original cone functor is the actual disk scalar tensor functor. -/
def originalConeDiskNatIso : originalConeFunctor (I := I) ≅
    EnrichedFunctorCat.tensorLeft PointedCGWH.diskOne :=
  NatIso.ofComponents originalConeDiskIso (fun f => originalConeDiskIso_naturality f)

end PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

namespace PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

open PointedCGWH.EnrichedIntervalCylinder

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
attribute [local instance] MonoidalClosed.enrichedCategorySelf
  PointedCGWH.EnrichedMapping.hasSmallLimits
  HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.nativeHasZeroObject
  HasZeroObject.zeroMorphismsOfZeroObject

/-- The disk quotient retains the original canonical ordinary cofiber leg and sphere isomorphism. -/
def originalDiskSphereQuotient : PointedCGWH.diskOne.{u, v} ⟶ PointedCGWH.sphereOne.{u, v} := by
  let q : PointedCGWH.diskOne.{u, v} ⟶
      (ordinaryCofiber (C := PointedCGWH.{u, v})).obj
        (Arrow.mk PointedCGWH.diskBoundary.{u, v}) :=
    OriginalScalarCone.ordinaryQuotientTarget (C := PointedCGWH.{u, v})
      (Arrow.mk PointedCGWH.diskBoundary.{u, v})
  exact q ≫ PointedCGWH.diskCofiberIsoSphereOne.hom

/-- The chosen terminal coefficient tensors to the actual original native zero diagram. -/
def originalTerminalCoefficientZeroIso (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    tensorLeftObject (⊤_ PointedCGWH.{u, v}) X ≅
      HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram := by
  apply IsZero.iso _ HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero
  apply EnrichedZeroCompletion.diagram_isZero_of_obj_isZero
  intro a
  exact EnrichedZeroCompletion.tensor_isZero_left
    (OriginalScalarCone.terminalIsZero (C := PointedCGWH.{u, v}))
    (X.toEnrichedFunctor.obj a)

/-- The actual scalar disk-boundary quotient is the original sphere tensor pushout on every
  input. -/
theorem originalDiskSphereTensorIsPushout (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    IsPushout (scalarTensorMap PointedCGWH.diskBoundary X)
      (HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.toZero
        (tensorLeftObject (Arrow.mk PointedCGWH.diskBoundary).left X))
      (scalarTensorMap originalDiskSphereQuotient X)
      (HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroTo
        (tensorLeftObject PointedCGWH.sphereOne X)) := by
  let F := WeightedEndVariance.tensorBifunctor.flip.obj X
  let f : Arrow PointedCGWH.{u, v} := Arrow.mk PointedCGWH.diskBoundary
  let h := (OriginalScalarCone.ordinaryQuotientIsPushout f).map F
  let eZ := originalTerminalCoefficientZeroIso X
  let eP := F.mapIso PointedCGWH.diskCofiberIsoSphereOne
  apply h.of_iso (Iso.refl _) (Iso.refl _) eZ eP
  · change scalarTensorMap PointedCGWH.diskBoundary X ≫ 𝟙 _ =
      𝟙 _ ≫ scalarTensorMap PointedCGWH.diskBoundary X
    rw [Category.comp_id, Category.id_comp]
  · exact HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  · change F.map (OriginalScalarCone.ordinaryQuotientTarget f) ≫
      F.map PointedCGWH.diskCofiberIsoSphereOne.hom =
      𝟙 _ ≫ scalarTensorMap originalDiskSphereQuotient X
    rw [Category.id_comp]
    exact (F.map_comp (OriginalScalarCone.ordinaryQuotientTarget f)
      PointedCGWH.diskCofiberIsoSphereOne.hom).symm
  · exact (HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero.of_iso
    eZ).isInitial.hom_ext _ _

/-- The original surviving source identifies with the full ordered disk-boundary tensor source. -/
def originalDiskTensorSourceIso (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    X ≅ tensorLeftObject (Arrow.mk PointedCGWH.diskBoundary).left X :=
  (scalarUnitIso X).symm ≪≫
    (WeightedEndVariance.tensorBifunctor.flip.obj X).mapIso originalDiskSourceUnitIso

/-- The full disk tensor source comparison retains the same original cone inclusion. -/
theorem originalDiskTensorSource_inclusion (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    originalConeInclusion.app X ≫ (originalConeDiskIso X).hom =
      (originalDiskTensorSourceIso X).hom ≫ scalarTensorMap PointedCGWH.diskBoundary X := by
  have hS : (originalDiskTensorSourceIso X).hom =
      (scalarUnitIso X).inv ≫ scalarTensorMap originalDiskSourceUnitIso.hom X := rfl
  rw [hS, Category.assoc]
  exact originalConeDiskIso_inclusion X

/-- Both original scalar suspension endpoints are collapsed in the actual sphere tensor. -/
theorem originalSphereSuspensionIsPushout (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    IsPushout (originalConeInclusion.app X)
      (HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.toZero X)
      ((originalConeDiskIso X).hom ≫ scalarTensorMap originalDiskSphereQuotient X)
      (HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroTo
        (tensorLeftObject PointedCGWH.sphereOne X)) := by
  let h := originalDiskSphereTensorIsPushout X
  have hi : scalarTensorMap PointedCGWH.diskBoundary X ≫ (originalConeDiskIso X).inv =
      (originalDiskTensorSourceIso X).inv ≫ originalConeInclusion.app X := by
    apply (cancel_mono (originalConeDiskIso X).hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
      originalDiskTensorSource_inclusion, Iso.inv_hom_id_assoc]
  have hq : scalarTensorMap originalDiskSphereQuotient X ≫ 𝟙 _ =
      (originalConeDiskIso X).inv ≫
        ((originalConeDiskIso X).hom ≫ scalarTensorMap originalDiskSphereQuotient X) := by
    rw [Category.comp_id, Iso.inv_hom_id_assoc]
  apply h.of_iso (originalDiskTensorSourceIso X).symm (originalConeDiskIso X).symm
    (Iso.refl _) (Iso.refl _)
  · exact hi
  · exact HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  · exact hq
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- The literal original scalar suspension is naturally the original sphere tensor on every
  input. -/
def originalScalarSuspensionSphereIso (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    originalScalarSuspensionFunctor.obj X ≅ tensorLeftObject PointedCGWH.sphereOne X :=
  (OriginalScalarCone.cofiberIsPushout EnrichedIntervalCylinder.functor
    (inclusionNatTrans 0) (inclusionNatTrans 1)
    (HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.toZero X)).isoIsPushout _ _
      (originalSphereSuspensionIsPushout X).flip

/-- The scalar suspension quotient becomes the exact original reflected disk-to-sphere quotient. -/
@[reassoc]
theorem originalScalarSuspensionSphereIso_quotient
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    originalScalarSuspensionQuotient X ≫ (originalScalarSuspensionSphereIso X).hom =
      (originalConeDiskIso X).hom ≫ scalarTensorMap originalDiskSphereQuotient X :=
  (OriginalScalarCone.cofiberIsPushout EnrichedIntervalCylinder.functor
    (inclusionNatTrans 0) (inclusionNatTrans 1)
    (HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.toZero X)).inr_isoIsPushout_hom
      _ _ (originalSphereSuspensionIsPushout X).flip

/-- The full original scalar zero leg remains the actual native sphere zero leg. -/
@[reassoc]
theorem originalScalarSuspensionSphereIso_zero
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    OriginalScalarCone.suspensionZeroLeg EnrichedIntervalCylinder.functor
        (inclusionNatTrans 0) (inclusionNatTrans 1)
        HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero X ≫
      (originalScalarSuspensionSphereIso X).hom =
    HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroTo
      (tensorLeftObject PointedCGWH.sphereOne X) :=
  (OriginalScalarCone.cofiberIsPushout EnrichedIntervalCylinder.functor
    (inclusionNatTrans 0) (inclusionNatTrans 1)
    (HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.toZero X)).inl_isoIsPushout_hom
      _ _ (originalSphereSuspensionIsPushout X).flip

/-- Every whole original map retains the same scalar suspension and sphere tensor square. -/
@[reassoc]
theorem originalScalarSuspensionSphereIso_naturality
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    originalScalarSuspensionFunctor.map f ≫ (originalScalarSuspensionSphereIso Y).hom =
      (originalScalarSuspensionSphereIso X).hom ≫ tensorLeftMap PointedCGWH.sphereOne f := by
  let qX : originalConeFunctor.obj X ⟶ originalScalarSuspensionFunctor.obj X :=
    originalScalarSuspensionQuotient X
  let qY : originalConeFunctor.obj Y ⟶ originalScalarSuspensionFunctor.obj Y :=
    originalScalarSuspensionQuotient Y
  let zX : HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram ⟶
      originalScalarSuspensionFunctor.obj X :=
    OriginalScalarCone.suspensionZeroLeg EnrichedIntervalCylinder.functor
      (inclusionNatTrans 0) (inclusionNatTrans 1)
      HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero X
  have sq : IsPushout (HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.toZero X)
      (originalConeInclusion.app X) zX qX :=
    OriginalScalarCone.cofiberIsPushout EnrichedIntervalCylinder.functor
      (inclusionNatTrans 0) (inclusionNatTrans 1)
      (HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.toZero X)
  have hq : qX ≫ originalScalarSuspensionFunctor.map f = originalConeFunctor.map f ≫ qY :=
    (OriginalScalarCone.suspensionQuotient_naturality EnrichedIntervalCylinder.functor
      (inclusionNatTrans 0) (inclusionNatTrans 1)
      HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero f).symm
  have hX : qX ≫ (originalScalarSuspensionSphereIso X).hom =
      (originalConeDiskIso X).hom ≫ scalarTensorMap originalDiskSphereQuotient X :=
    originalScalarSuspensionSphereIso_quotient X
  have hY : qY ≫ (originalScalarSuspensionSphereIso Y).hom =
      (originalConeDiskIso Y).hom ≫ scalarTensorMap originalDiskSphereQuotient Y :=
    originalScalarSuspensionSphereIso_quotient Y
  apply sq.hom_ext
  · exact HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagramIsInitial.hom_ext _ _
  · rw [← Category.assoc, hq, Category.assoc, hY,
      ← Category.assoc, originalConeDiskIso_naturality,
      Category.assoc, scalarTensorMap_diagram_naturality]
    have hZ : ((originalConeDiskIso X).hom ≫ scalarTensorMap originalDiskSphereQuotient X) ≫
        tensorLeftMap PointedCGWH.sphereOne f =
      (qX ≫ (originalScalarSuspensionSphereIso X).hom) ≫
        tensorLeftMap PointedCGWH.sphereOne f :=
      congrArg (fun t => t ≫ tensorLeftMap PointedCGWH.sphereOne f) hX.symm
    exact (Category.assoc (originalConeDiskIso X).hom
      (scalarTensorMap originalDiskSphereQuotient X) (tensorLeftMap PointedCGWH.sphereOne
        f)).symm.trans
      (hZ.trans (Category.assoc qX (originalScalarSuspensionSphereIso X).hom
        (tensorLeftMap PointedCGWH.sphereOne f)))

/-- The full scalar suspension and sphere tensor functors are naturally isomorphic. -/
def originalScalarSuspensionSphereNatIso : originalScalarSuspensionFunctor (I := I) ≅
    EnrichedFunctorCat.tensorLeft PointedCGWH.sphereOne :=
  NatIso.ofComponents originalScalarSuspensionSphereIso
    (fun f => originalScalarSuspensionSphereIso_naturality f)

end PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

namespace PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

open PointedCGWH.EnrichedIntervalCylinder

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
attribute [local instance] MonoidalClosed.enrichedCategorySelf
  PointedCGWH.EnrichedMapping.hasSmallLimits
  HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.nativeHasZeroObject
  HasZeroObject.zeroMorphismsOfZeroObject
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- A null coefficient in the actual scalar cofiber has a preimage after actual sphere suspension.
Only K is cofibrant. Both endpoints of the original native arrow remain arbitrary. -/
theorem originalSphereCoefficientLift_of_null
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (K : EnrichedFunctorCat PointedCGWH.{u, v} I) [IsCofibrant K] (g : K ⟶ f.right)
    (hg : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
        (g ≫ OriginalScalarCone.cofiberTarget EnrichedIntervalCylinder.functor
          (inclusionNatTrans 0) (inclusionNatTrans 1) f.hom) =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
        (0 : K ⟶ originalScalarCofiberFunctor.obj f)) :
    ∃ k : (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
        (tensorLeftObject PointedCGWH.sphereOne K) ⟶
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
        (tensorLeftObject PointedCGWH.sphereOne f.left),
      k ≫ (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
          (tensorLeftMap PointedCGWH.sphereOne f.hom) =
        (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
          (tensorLeftMap PointedCGWH.sphereOne g) := by
  let H := toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)
  obtain ⟨k₀, hk₀⟩ := originalScalarCoefficientLift_of_null f K g hg
  let k : H.obj (originalScalarSuspensionFunctor.obj K) ⟶
      H.obj (originalScalarSuspensionFunctor.obj f.left) := k₀
  have hk : k ≫ H.map (originalScalarSuspensionFunctor.map f.hom) =
      H.map (originalScalarSuspensionFunctor.map g) := hk₀
  let eK := H.mapIso (originalScalarSuspensionSphereIso K)
  let eX := H.mapIso (originalScalarSuspensionSphereIso f.left)
  let eY := H.mapIso (originalScalarSuspensionSphereIso f.right)
  have hf : H.map (originalScalarSuspensionFunctor.map f.hom) ≫ eY.hom =
      eX.hom ≫ H.map (tensorLeftMap PointedCGWH.sphereOne f.hom) := by
    exact (H.map_comp _ _).symm.trans
      ((H.congr_map (originalScalarSuspensionSphereIso_naturality f.hom)).trans
        (H.map_comp _ _))
  have hG : H.map (originalScalarSuspensionFunctor.map g) ≫ eY.hom =
      eK.hom ≫ H.map (tensorLeftMap PointedCGWH.sphereOne g) := by
    exact (H.map_comp _ _).symm.trans
      ((H.congr_map (originalScalarSuspensionSphereIso_naturality g)).trans
        (H.map_comp _ _))
  refine ⟨eK.inv ≫ k ≫ eX.hom, ?_⟩
  change (eK.inv ≫ k ≫ eX.hom) ≫ H.map (tensorLeftMap PointedCGWH.sphereOne f.hom) =
    H.map (tensorLeftMap PointedCGWH.sphereOne g)
  calc
    _ = eK.inv ≫ k ≫ (eX.hom ≫ H.map (tensorLeftMap PointedCGWH.sphereOne f.hom)) := by
      simp only [Category.assoc]
    _ = eK.inv ≫ k ≫ (H.map (originalScalarSuspensionFunctor.map f.hom) ≫ eY.hom) :=
      congrArg (fun t => eK.inv ≫ k ≫ t) hf.symm
    _ = eK.inv ≫ (k ≫ H.map (originalScalarSuspensionFunctor.map f.hom)) ≫ eY.hom := by
      simp only [Category.assoc]
    _ = eK.inv ≫ H.map (originalScalarSuspensionFunctor.map g) ≫ eY.hom :=
      congrArg (fun t => eK.inv ≫ t ≫ eY.hom) hk
    _ = eK.inv ≫ (eK.hom ≫ H.map (tensorLeftMap PointedCGWH.sphereOne g)) :=
      congrArg (fun t => eK.inv ≫ t) hG
    _ = _ := eK.inv_hom_id_assoc _

end PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

namespace PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

open PointedCGWH.Spectra.NativeOmegaWeakClosure
  PointedCGWH.Spectra.OriginalHEPHomotopyPushoutComparison

/-- The original native interval reflection retains the entire realization comparison. -/
def originalRealizedIntervalReflection : CGWH.interval.{u, v} ≅ CGWH.interval.{u, v} :=
  CGWH.homotopyIntervalIsoInterval.symm ≪≫ CGWH.literalTimeReflection ≪≫
    CGWH.homotopyIntervalIsoInterval

/-- The actual freely based coefficient reflection is the free-point image of that interval map. -/
theorem originalCoefficientReflection_eq_free :
    originalCoefficientReflection.{u, v} =
      (Under.costar CGWH.point.{u, v}).mapIso originalRealizedIntervalReflection := by
  apply Iso.ext
  let F := Under.costar CGWH.point.{u, v}
  let e := CGWH.literalTimeReflection.{u, v} ≪≫ CGWH.homotopyIntervalIsoInterval
  have he : e.inv ≫ CGWH.literalTimeReflection.hom ≫ e.hom =
      originalRealizedIntervalReflection.hom := by
    change (CGWH.homotopyIntervalIsoInterval.inv ≫ CGWH.literalTimeReflection.inv) ≫
        CGWH.literalTimeReflection.hom ≫
        (CGWH.literalTimeReflection.hom ≫ CGWH.homotopyIntervalIsoInterval.hom) =
      CGWH.homotopyIntervalIsoInterval.inv ≫ CGWH.literalTimeReflection.hom ≫
        CGWH.homotopyIntervalIsoInterval.hom
    simp only [Category.assoc]
    rw [Iso.inv_hom_id_assoc]
  change F.map e.inv ≫ F.map CGWH.literalTimeReflection.hom ≫ F.map e.hom =
    F.map originalRealizedIntervalReflection.hom
  rw [← Functor.map_comp, ← Functor.map_comp, he]

/-- The free interval summand of the disk comparison is the literal original interval reflection. -/
@[reassoc]
theorem originalCoefficientToDisk_free_leg :
    (coprod.inr : CGWH.interval.{u, v} ⟶
        CGWH.point.{u, v} ⨿ CGWH.interval.{u, v}) ≫ originalCoefficientToDisk.right =
      originalRealizedIntervalReflection.hom := by
  rw [originalCoefficientToDisk, Under.comp_right, originalCoefficientReflection_eq_free]
  change coprod.inr ≫
      (coprod.map (𝟙 CGWH.point) originalRealizedIntervalReflection.hom ≫
        coprod.desc CGWH.intervalOne (𝟙 CGWH.interval)) = _
  rw [coprod.inr_map_assoc, coprod.inr_desc, Category.comp_id]

/-- The actual native disk quotient retains its literal unpointed interval carrier. -/
def originalDiskSphereUnderlying : CGWH.interval.{u, v} ⟶ PointedCGWH.sphereOne.{u, v}.right :=
  originalDiskSphereQuotient.right

/-- The original realized reflection has the actual physical coordinate one minus t. -/
theorem originalRealizedIntervalReflection_parameter (t : TopCat.I.{v}) :
    CGWH.cgwhToTop.{u, v}.map originalRealizedIntervalReflection.{u, v}.hom
        (CGWH.intervalToTopIso.{u, v}.inv t) =
      CGWH.intervalToTopIso.{u, v}.inv
        (TopCat.I.homeomorph.symm (unitInterval.symm (TopCat.I.homeomorph t))) := by
  let R : TopCat.I.{v} ⟶ TopCat.I.{v} :=
    TopCat.ofHom ⟨fun x => TopCat.I.homeomorph.symm
      (unitInterval.symm (TopCat.I.homeomorph x)),
      TopCat.I.homeomorph.symm.continuous.comp
        (unitInterval.continuous_symm.comp TopCat.I.homeomorph.continuous)⟩
  have hR : CGWH.cgwhToTop.map CGWH.literalTimeReflection.{u, v}.hom = R := rfl
  have hInv : CGWH.cgwhToTop.map CGWH.homotopyIntervalIsoInterval.{u, v}.inv =
      CGWH.intervalToTopIso.hom := CGWH.cgwhToTop_map_homotopyIntervalIsoInterval_inv
  have hHom : CGWH.cgwhToTop.map CGWH.homotopyIntervalIsoInterval.{u, v}.hom =
      CGWH.intervalToTopIso.inv := CGWH.cgwhToTop_map_homotopyIntervalIsoInterval_hom
  have hMap : CGWH.cgwhToTop.map originalRealizedIntervalReflection.{u, v}.hom =
      CGWH.intervalToTopIso.hom ≫ R ≫ CGWH.intervalToTopIso.inv := by
    change CGWH.cgwhToTop.map
      (CGWH.homotopyIntervalIsoInterval.inv ≫ CGWH.literalTimeReflection.hom ≫
        CGWH.homotopyIntervalIsoInterval.hom) = _
    rw [Functor.map_comp, Functor.map_comp, hInv, hHom, hR]
    rfl
  have hWhole : CGWH.intervalToTopIso.{u, v}.inv ≫
      CGWH.cgwhToTop.map originalRealizedIntervalReflection.hom =
      R ≫ CGWH.intervalToTopIso.inv := by
    rw [hMap, Iso.inv_hom_id_assoc]
  exact ConcreteCategory.congr_hom hWhole t

/-- The actual original reflected interval quotient has exactly the corresponding sphere
  parameter. -/
theorem originalReflectedSphereQuotient_parameter (t : TopCat.I.{v}) :
    CGWH.cgwhToTop.{u, v}.map
        (originalRealizedIntervalReflection.{u, v}.hom ≫ originalDiskSphereUnderlying.{u, v})
        (CGWH.intervalToTopIso.{u, v}.inv t) =
      PointedCGWH.sphereOneParam.{u, v}
        (TopCat.I.homeomorph.symm (unitInterval.symm (TopCat.I.homeomorph t))) := by
  have hMap := CGWH.cgwhToTop.{u, v}.map_comp originalRealizedIntervalReflection.{u, v}.hom
    originalDiskSphereUnderlying.{u, v}
  have h := ConcreteCategory.congr_hom hMap (CGWH.intervalToTopIso.{u, v}.inv t)
  exact h.trans ((congrArg (fun x => CGWH.cgwhToTop.{u, v}.map originalDiskSphereUnderlying.{u,
    v} x)
    (originalRealizedIntervalReflection_parameter.{u, v} t)).trans
      (PointedCGWH.diskCofiberIsoSphereOne_param.{u, v} _))

end PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

namespace PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

open HomotopicalAlgebra.EnrichedProjective.Native
  HomotopicalAlgebra.EnrichedProjective.Native.FreeSphereHom
  CategoryTheory.EnrichedFunctorCat
  PointedCGWH.EnrichedIntervalCylinder

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
attribute [local instance] MonoidalClosed.enrichedCategorySelf
  PointedCGWH.EnrichedMapping.hasSmallLimits
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant
  HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.nativeHasZeroObject
  HasZeroObject.zeroMorphismsOfZeroObject

/-- Actual null cube classes in the original scalar cofiber have a literal space-suspension
  preimage.
The original source, target, native index, degree and all scalar/evaluation maps are unchanged. -/
theorem originalSpaceSuspensionClass_image_of_scalar_cofiber_null
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) (a : I) (n : ℕ)
    (x : PointedCGWH.piN n (f.right.toEnrichedFunctor.obj a))
    (hx : PointedCGWH.piNMap n
        (component (OriginalScalarCone.cofiberTarget EnrichedIntervalCylinder.functor
          (inclusionNatTrans 0) (inclusionNatTrans 1) f.hom) a) x =
      PointedCGWH.SphereHom.nullCube n
        ((originalScalarCofiberFunctor.obj f).toEnrichedFunctor.obj a)) :
    ∃ y : PointedCGWH.piN (n + 1)
        ((tensorLeftObject PointedCGWH.sphereOne f.left).toEnrichedFunctor.obj a),
      PointedCGWH.piNMap (n + 1) (component (tensorLeftMap PointedCGWH.sphereOne f.hom) a) y =
        PointedCGWH.SphereHom.sphereSuspensionClass n (f.right.toEnrichedFunctor.obj a) x := by
  let H := toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)
  let K : EnrichedFunctorCat PointedCGWH.{u, v} I :=
    (Free.functor a).obj (PointedCGWH.SphereHom.sphere.{u, v} n)
  let _ : IsCofibrant (PointedCGWH.SphereHom.sphere.{u, v} n) := sphere_isCofibrant n
  let _ : (Free.adjunction (V := PointedCGWH.{u, v}) a).IsQuillenAdjunction :=
    HomotopicalAlgebra.EnrichedProjective.Native.freeAtEvaluation_isQuillenAdjunction a
  let _ : IsCofibrant K :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := Free.adjunction a)
      (sphere_isCofibrant n)
  let c : f.right ⟶ originalScalarCofiberFunctor.obj f :=
    OriginalScalarCone.cofiberTarget EnrichedIntervalCylinder.functor
      (inclusionNatTrans 0) (inclusionNatTrans 1) f.hom
  let h : H.obj K ⟶ H.obj f.right := freeSpherePiHomEquiv (B := B) a n f.right x
  obtain ⟨g, hg⟩ := map_surjective_of_isLocalization H K f.right h
  have hG : H.map g = freeSpherePiHomEquiv (B := B) a n f.right x := hg
  have hN : freeSpherePiHomEquiv (B := B) a n (originalScalarCofiberFunctor.obj f)
      (PointedCGWH.SphereHom.nullCube n ((originalScalarCofiberFunctor.obj
        f).toEnrichedFunctor.obj a)) =
      H.map (0 : K ⟶ originalScalarCofiberFunctor.obj f) := by
    have h := freeSpherePiHomEquiv_null (B := B) a n (originalScalarCofiberFunctor.obj f)
    have hz : OrdinaryHoCofiberKernel.nullMap K (originalScalarCofiberFunctor.obj f) = 0 := by
      change HasZeroObject.zeroIsTerminal.from K ≫
        HasZeroObject.zeroIsInitial.to (originalScalarCofiberFunctor.obj f) = 0
      rw [(isZero_zero (EnrichedFunctorCat PointedCGWH.{u, v} I)).eq_of_tgt
        (HasZeroObject.zeroIsTerminal.from K) 0, zero_comp]
    exact h.trans (H.congr_map hz)
  have hn : H.map (g ≫ c) = H.map (0 : K ⟶ originalScalarCofiberFunctor.obj f) := by
    exact (H.map_comp g c).trans
      ((congrArg (fun t => t ≫ H.map c) hG).trans
        ((freeSpherePiHomEquiv_naturality (B := B) a n c x).symm.trans
          ((congrArg (freeSpherePiHomEquiv (B := B) a n (originalScalarCofiberFunctor.obj f))
            hx).trans hN)))
  obtain ⟨k, hk⟩ := originalSphereCoefficientLift_of_null f K g hn
  let e := H.mapIso (scalarFreeSphereIso a n)
  let t := e.inv ≫ k
  let y := (suspendedFreeSpherePiHomEquiv (B := B) a n
    (tensorLeftObject PointedCGWH.sphereOne f.left)).symm t
  refine ⟨y, ?_⟩
  have hMap : PointedCGWH.piNMap (n + 1)
      (component (tensorLeftMap PointedCGWH.sphereOne f.hom) a) y =
      (suspendedFreeSpherePiHomEquiv (B := B) a n
        (tensorLeftObject PointedCGWH.sphereOne f.right)).symm
        (t ≫ H.map (tensorLeftMap PointedCGWH.sphereOne f.hom)) :=
    (suspendedFreeSpherePiHomEquiv_inverse_naturality (B := B) a n
      (tensorLeftMap PointedCGWH.sphereOne f.hom) t).symm
  rw [hMap]
  apply (suspendedFreeSpherePiHomEquiv (B := B) a n
    (tensorLeftObject PointedCGWH.sphereOne f.right)).injective
  rw [Equiv.apply_symm_apply]
  change (e.inv ≫ k) ≫ H.map (tensorLeftMap PointedCGWH.sphereOne f.hom) = _
  rw [Category.assoc, hk]
  exact (H.map_comp _ _).symm.trans
    (suspendedFreeSpherePiHomEquiv_scalarMap (B := B) a n f.right x g hg).symm

end PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

namespace PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

open PointedCGWH.EnrichedIntervalCylinder
variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
attribute [local instance] MonoidalClosed.enrichedCategorySelf
  PointedCGWH.EnrichedMapping.hasSmallLimits
  HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.nativeHasZeroObject
  HasZeroObject.zeroMorphismsOfZeroObject

/-- The actual scalar cofiber boundary lands in the original native sphere tensor source. -/
def originalSphereCofiberBoundary
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    originalScalarCofiberFunctor.obj f ⟶ tensorLeftObject PointedCGWH.sphereOne f.left :=
  originalScalarBoundary f ≫ (originalScalarSuspensionSphereIso f.left).hom

/-- The entire original target leg is null under the actual sphere boundary. -/
@[reassoc]
theorem originalSphereCofiberBoundary_target
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    OriginalScalarCone.cofiberTarget EnrichedIntervalCylinder.functor
        (inclusionNatTrans 0) (inclusionNatTrans 1) f.hom ≫
      originalSphereCofiberBoundary f = 0 := by
  let i : f.right ⟶ originalScalarCofiberFunctor.obj f :=
    OriginalScalarCone.cofiberTarget EnrichedIntervalCylinder.functor
      (inclusionNatTrans 0) (inclusionNatTrans 1) f.hom
  let b : originalScalarCofiberFunctor.obj f ⟶ originalScalarSuspensionFunctor.obj f.left :=
    originalScalarBoundary f
  have hi : i ≫ b = 0 := OriginalScalarCone.boundary_target EnrichedIntervalCylinder.functor
    (inclusionNatTrans 0) (inclusionNatTrans 1)
    HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero f
  change i ≫ (b ≫ (originalScalarSuspensionSphereIso f.left).hom) = 0
  exact (Category.assoc i b (originalScalarSuspensionSphereIso f.left).hom).symm.trans
    ((congrArg (fun t => t ≫ (originalScalarSuspensionSphereIso f.left).hom) hi).trans
      (zero_comp (f := (originalScalarSuspensionSphereIso f.left).hom)))

/-- The full original cone leg becomes the exact reflected disk-sphere quotient. -/
@[reassoc]
theorem originalSphereCofiberBoundary_cone
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    OriginalScalarCone.cofiberCone EnrichedIntervalCylinder.functor
        (inclusionNatTrans 0) (inclusionNatTrans 1) f.hom ≫
      originalSphereCofiberBoundary f =
    (originalConeDiskIso f.left).hom ≫ scalarTensorMap originalDiskSphereQuotient f.left := by
  let q : originalConeFunctor.obj f.left ⟶ originalScalarCofiberFunctor.obj f :=
    OriginalScalarCone.cofiberCone EnrichedIntervalCylinder.functor
      (inclusionNatTrans 0) (inclusionNatTrans 1) f.hom
  let b : originalScalarCofiberFunctor.obj f ⟶ originalScalarSuspensionFunctor.obj f.left :=
    originalScalarBoundary f
  have hq : q ≫ b = originalScalarSuspensionQuotient f.left :=
    OriginalScalarCone.boundary_cone EnrichedIntervalCylinder.functor
      (inclusionNatTrans 0) (inclusionNatTrans 1)
      HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero f
  change q ≫ (b ≫ (originalScalarSuspensionSphereIso f.left).hom) = _
  exact (Category.assoc q b (originalScalarSuspensionSphereIso f.left).hom).symm.trans
    ((congrArg (fun t => t ≫ (originalScalarSuspensionSphereIso f.left).hom) hq).trans
      (originalScalarSuspensionSphereIso_quotient f.left))

/-- Every actual whole arrow square retains both source and target sphere-boundary maps. -/
@[reassoc]
theorem originalSphereCofiberBoundary_naturality
    {f g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)} (a : f ⟶ g) :
    originalScalarCofiberFunctor.map a ≫ originalSphereCofiberBoundary g =
      originalSphereCofiberBoundary f ≫ tensorLeftMap PointedCGWH.sphereOne a.left := by
  let bF : originalScalarCofiberFunctor.obj f ⟶ originalScalarSuspensionFunctor.obj f.left :=
    originalScalarBoundary f
  let bG : originalScalarCofiberFunctor.obj g ⟶ originalScalarSuspensionFunctor.obj g.left :=
    originalScalarBoundary g
  have hn : originalScalarCofiberFunctor.map a ≫ bG =
      bF ≫ originalScalarSuspensionFunctor.map a.left := originalScalarBoundary_naturality a
  have hs := originalScalarSuspensionSphereIso_naturality a.left
  change originalScalarCofiberFunctor.map a ≫
      (bG ≫ (originalScalarSuspensionSphereIso g.left).hom) =
    (bF ≫ (originalScalarSuspensionSphereIso f.left).hom) ≫ _
  rw [← Category.assoc, hn, Category.assoc, hs, ← Category.assoc]

/-- The entire original sphere boundary is a genuine natural transformation on all arrow maps. -/
def originalSphereCofiberBoundaryNatTrans : originalScalarCofiberFunctor (I := I) ⟶
    Arrow.leftFunc ⋙ EnrichedFunctorCat.tensorLeft PointedCGWH.sphereOne where
  app := originalSphereCofiberBoundary
  naturality _ _ a := originalSphereCofiberBoundary_naturality a

end PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

namespace PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

open PointedCGWH.EnrichedIntervalCylinder
variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
attribute [local instance] MonoidalClosed.enrichedCategorySelf
  PointedCGWH.EnrichedMapping.hasSmallLimits
  HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.nativeHasZeroObject
  HasZeroObject.zeroMorphismsOfZeroObject
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant

/-- Every map through the original scalar cone is null in the original level homotopy category. -/
theorem originalConeComposite_null
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    {A X Y : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (i : A ⟶ originalConeFunctor.obj X) (q : originalConeFunctor.obj X ⟶ Y) :
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map (i ≫ q) =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map (0 : A ⟶ Y) := by
  let H := toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)
  let Z : EnrichedFunctorCat PointedCGWH.{u, v} I := 0
  let r : originalConeFunctor.obj X ⟶ Z := 0
  let _ : WeakEquivalence r := originalConeProjection_weakEquivalence X
  let _ : IsIso (H.map r) := Localization.inverts H (weakEquivalences _) r (mem_weakEquivalences r)
  have hi : H.map i ≫ H.map r = H.map (0 : A ⟶ Z) := by
    rw [← H.map_comp, comp_zero]
  have hInv : H.map i = H.map (0 : A ⟶ Z) ≫ inv (H.map r) := by
    apply (cancel_mono (H.map r)).mp
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact hi
  let _ : Subsingleton (H.obj Z ⟶ H.obj Y) :=
    OrdinaryHoChosenPuppe.actualZeroHom_subsingleton Z (isZero_zero _) Y
  have hz : inv (H.map r) ≫ H.map q = H.map (0 : Z ⟶ Y) := Subsingleton.elim _ _
  rw [H.map_comp, hInv, Category.assoc, hz, ← H.map_comp, zero_comp]

/-- The source-to-scalar-cofiber composite is null on every original spectrum arrow. -/
theorem originalSourceCofiber_null
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
        (f.hom ≫ OriginalScalarCone.cofiberTarget EnrichedIntervalCylinder.functor
          (inclusionNatTrans 0) (inclusionNatTrans 1) f.hom) =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
        (0 : f.left ⟶ originalScalarCofiberFunctor.obj f) := by
  let i : f.left ⟶ originalConeFunctor.obj f.left := originalConeInclusion.app f.left
  let q : originalConeFunctor.obj f.left ⟶ originalScalarCofiberFunctor.obj f :=
    OriginalScalarCone.cofiberCone EnrichedIntervalCylinder.functor
      (inclusionNatTrans 0) (inclusionNatTrans 1) f.hom
  have h := OriginalScalarCone.cofiber_condition EnrichedIntervalCylinder.functor
    (inclusionNatTrans 0) (inclusionNatTrans 1) f.hom
  exact ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).congr_map h).trans
    (originalConeComposite_null i q)

/-- The boundary followed by the original suspended arrow is null for arbitrary endpoints. -/
theorem originalBoundarySuspension_null
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) :
    (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
        (originalScalarBoundary f ≫ originalScalarSuspensionFunctor.map f.hom) =
      (toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).map
        (0 : originalScalarCofiberFunctor.obj f ⟶ originalScalarSuspensionFunctor.obj f.right) := by
  let i : originalScalarCofiberFunctor.obj f ⟶ originalConeFunctor.obj f.right :=
    OriginalScalarCone.targetConeComparison EnrichedIntervalCylinder.functor
      (inclusionNatTrans 0) (inclusionNatTrans 1) f
  let q : originalConeFunctor.obj f.right ⟶ originalScalarSuspensionFunctor.obj f.right :=
    originalScalarSuspensionQuotient f.right
  have hWhole : originalScalarBoundary f ≫ originalScalarSuspensionFunctor.map f.hom = i ≫ q :=
    OriginalScalarCone.boundary_suspension_factors_targetCone EnrichedIntervalCylinder.functor
      (inclusionNatTrans 0) (inclusionNatTrans 1)
      HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero f
  exact ((toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)).congr_map hWhole).trans
    (originalConeComposite_null i q)

end PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing



namespace PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

open PointedCGWH.EnrichedIntervalCylinder
  PointedCGWH.SuspensionReflectionGeometry
  PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberSphereLift
variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
attribute [local instance] MonoidalClosed.enrichedCategorySelf
  PointedCGWH.EnrichedMapping.hasSmallLimits
  HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.nativeHasZeroObject
  HasZeroObject.zeroMorphismsOfZeroObject
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The actual original scalar cofiber kernel yields a positive group preimage of the original unit.
Both endpoints and every original native index are arbitrary. -/
theorem originalSpaceSuspensionGroup_image_of_scalar_cofiber_kernel
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) (a : I) (k : ℕ)
    (x : PointedCGWH.piN (k + 1) (f.right.toEnrichedFunctor.obj a))
    (hx : (PointedCGWH.piNPositiveMap k
        (component (OriginalScalarCone.cofiberTarget EnrichedIntervalCylinder.functor
          (inclusionNatTrans 0) (inclusionNatTrans 1) f.hom) a)).hom x = 1) :
    ∃ y : PointedCGWH.piN (k + 2)
        ((tensorLeftObject PointedCGWH.sphereOne f.left).toEnrichedFunctor.obj a),
      (PointedCGWH.piNPositiveMap (k + 1)
          (component (tensorLeftMap PointedCGWH.sphereOne f.hom) a)).hom y =
        ((spaceSuspensionGroupMap k).app (f.right.toEnrichedFunctor.obj a)).hom x := by
  have hNull : PointedCGWH.piNMap (k + 1)
      (component (OriginalScalarCone.cofiberTarget EnrichedIntervalCylinder.functor
        (inclusionNatTrans 0) (inclusionNatTrans 1) f.hom) a) x =
      PointedCGWH.SphereHom.nullCube (k + 1)
        ((originalScalarCofiberFunctor.obj f).toEnrichedFunctor.obj a) :=
    (PointedCGWH.piNPositiveMap_apply k _ x).symm.trans
      (hx.trans (PointedCGWH.SphereHom.nullCube_eq_one k _).symm)
  obtain ⟨y, hy⟩ := originalSpaceSuspensionClass_image_of_scalar_cofiber_null f a (k + 1) x hNull
  refine ⟨y, ?_⟩
  exact (PointedCGWH.piNPositiveMap_apply (k + 1) _ y).trans
    (hy.trans (spaceSuspensionGroupMap_eq_class k (f.right.toEnrichedFunctor.obj a) x).symm)

end PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

namespace PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

open PointedCGWH.SequentialSpectrum.HomotopyStructureGeometry
  PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
  PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionStageGeometry
  PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionLoopShiftGeometry
  PointedCGWH.SuspensionReflectionGeometry
  PointedCGWH.SequentialSpectrum.StableHomotopy
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.nativeHasZeroObject
  HasZeroObject.zeroMorphismsOfZeroObject

/-- The actual all-endpoint scalar kernel produces the original signed suspension-stage image. -/
theorem originalScalarStageForward_image_of_kernel
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) (n m k : ℕ)
    (x : (levelCubeGroupFunctor (m + n) (k + n)).obj f.right)
    (hx : ((levelCubeGroupFunctor (m + n) (k + n)).map
      (OriginalScalarCone.cofiberTarget PointedCGWH.EnrichedIntervalCylinder.functor
        (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
        (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) f.hom)).hom x = 1) :
    ∃ c : (levelCubeGroupFunctor (m + n) ((k + 1) + n)).obj
        (SuspensionGeometry.suspension.obj f.left),
      ((levelCubeGroupFunctor (m + n) ((k + 1) + n)).map
        (SuspensionGeometry.suspension.map f.hom)).hom c =
      ((stageForward n m k).app f.right).hom x := by
  let a := CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne (m + n)
  obtain ⟨b, hb⟩ := originalSpaceSuspensionGroup_image_of_scalar_cofiber_kernel
    f a (k + n) x hx
  let d := stageDegreeNatIso n m k
  let c := (d.hom.app (SuspensionGeometry.suspension.obj f.left)).hom b
  have hn := congrArg (fun g => g.hom b) (d.hom.naturality (SuspensionGeometry.suspension.map f.hom))
  have hu : ((levelCubeGroupFunctor (m + n) ((k + 1) + n)).map
      (SuspensionGeometry.suspension.map f.hom)).hom c =
      ((unsignedStageForward n m k).app f.right).hom x := by
    exact hn.symm.trans
      ((congrArg (d.hom.app (SuspensionGeometry.suspension.obj f.right)).hom hb).trans
        (congrArg (fun g => g.hom x) (unsignedStageForward_space n m k f.right)).symm)
  by_cases he : n % 2 = 0
  · exact ⟨c, hu.trans (congrArg (fun g => g.hom x) (stageForward_even n m k he f.right)).symm⟩
  · refine ⟨c⁻¹, ?_⟩
    rw [map_inv, hu]
    exact (stageForward_odd_apply n m k he f.right x).symm

end PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

namespace PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

open PointedCGWH.SequentialSpectrum.HomotopyStructureGeometry
  PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
  PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
  PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionStageGeometry
  PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionStablePiGeometry
  PointedCGWH.SequentialSpectrum.StableHomotopy.IntegerColimitNormalization
  PointedCGWH.SequentialSpectrum.StableHomotopy
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.nativeHasZeroObject
  HasZeroObject.zeroMorphismsOfZeroObject

end PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing


namespace PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

open PointedCGWH.SequentialSpectrum.HomotopyStructureGeometry
  PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
  PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
  PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionStageGeometry
  PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionStablePiGeometry
  PointedCGWH.SequentialSpectrum.StableHomotopy.IntegerColimitNormalization
  PointedCGWH.SequentialSpectrum.StableHomotopy
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- The literal signed original stage image gives a preimage of the same unsuspended integer leg. -/
theorem originalInteger_image_of_signed_scalar_stage
    (q : ℤ) (n : ℕ) {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (a : (levelCubeGroupFunctor (integerTailLevel q + n)
      (integerTailPositiveIndex q + n)).obj Y)
    (c : (levelCubeGroupFunctor (integerTailLevel q + n)
      ((integerTailPositiveIndex q + 1) + n)).obj (SuspensionGeometry.suspension.obj X))
    (hc : ((levelCubeGroupFunctor (integerTailLevel q + n)
      ((integerTailPositiveIndex q + 1) + n)).map
      (SuspensionGeometry.suspension.map f)).hom c =
      ((stageForward n (integerTailLevel q) (integerTailPositiveIndex q)).app Y).hom a) :
    ∃ y : (integerStablePiFunctor q).obj X,
      ((integerStablePiFunctor q).map f).hom y = (integerStablePiLeg q Y n).hom a := by
  let m := integerTailLevel q
  let k := integerTailPositiveIndex q
  let e := integerSuspensionPiNatIso q
  let sX : (levelCubeGroupFunctor (m + n) ((k + 1) + n)).obj (SuspensionGeometry.suspension.obj X) ⟶
      (diagonalColimitFunctor m (k + 1)).obj (SuspensionGeometry.suspension.obj X) :=
    diagonalLeg m (k + 1) (SuspensionGeometry.suspension.obj X) n
  let sY : (levelCubeGroupFunctor (m + n) ((k + 1) + n)).obj (SuspensionGeometry.suspension.obj Y) ⟶
      (diagonalColimitFunctor m (k + 1)).obj (SuspensionGeometry.suspension.obj Y) :=
    diagonalLeg m (k + 1) (SuspensionGeometry.suspension.obj Y) n
  let nX := (suspensionNormalizationNatIso q).hom.app (SuspensionGeometry.suspension.obj X)
  let nY := (suspensionNormalizationNatIso q).hom.app (SuspensionGeometry.suspension.obj Y)
  let dF := (diagonalColimitFunctor m (k + 1)).map (SuspensionGeometry.suspension.map f)
  let pF := (integerStablePiFunctor (q + 1)).map (SuspensionGeometry.suspension.map f)
  let gF := (levelCubeGroupFunctor (m + n) ((k + 1) + n)).map
    (SuspensionGeometry.suspension.map f)
  have hd : sX ≫ dF = gF ≫ sY :=
    GrpCat.FilteredColimits.colimitMap_ι
      ((diagonalDiagramFunctor m (k + 1)).map (SuspensionGeometry.suspension.map f)) n
  have hn : dF ≫ nY = nX ≫ pF :=
    (suspensionNormalizationNatIso q).hom.naturality (SuspensionGeometry.suspension.map f)
  have hL : gF ≫ (sY ≫ nY) = (sX ≫ nX) ≫ pF := by
    exact (Category.assoc gF sY nY).symm.trans
      ((congrArg (fun t => t ≫ nY) hd.symm).trans
        ((Category.assoc sX dF nY).trans
          ((congrArg (fun t => sX ≫ t) hn).trans (Category.assoc sX nX pF).symm)))
  have hLeg : integerStablePiLeg q Y n ≫ e.hom.app Y =
      (stageForward n m k).app Y ≫ (sY ≫ nY) :=
    (congrArg (fun t => integerStablePiLeg q Y n ≫ t)
      (integerSuspensionPiNatIso_hom_app q Y)).trans (integerSuspensionPiMap_leg q Y n)
  apply CategoryTheory.originalGroupNatIso_image e f ((sX ≫ nX).hom c) ((integerStablePiLeg q Y n).hom a)
  exact (ConcreteCategory.congr_hom hL c).symm.trans
    ((congrArg (sY ≫ nY).hom hc).trans (ConcreteCategory.congr_hom hLeg a).symm)

end PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

namespace PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

open PointedCGWH.SequentialSpectrum.HomotopyStructureGeometry
  PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
  PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
  PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionStageGeometry
  PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionStablePiGeometry
  PointedCGWH.SequentialSpectrum.StableHomotopy.IntegerColimitNormalization
  PointedCGWH.SequentialSpectrum.StableHomotopy
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.nativeHasZeroObject
  HasZeroObject.zeroMorphismsOfZeroObject

/-- The actual scalar cofiber inclusion has the full original unsuspended integer kernel preimage. -/
theorem originalScalarCofiber_integer_kernel_preimage
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v})
    (x : (integerStablePiFunctor q).obj f.right)
    (hx : ((integerStablePiFunctor q).map
      (OriginalScalarCone.cofiberTarget PointedCGWH.EnrichedIntervalCylinder.functor
        (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
        (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) f.hom)).hom x = 1) :
    ∃ y : (integerStablePiFunctor q).obj f.left,
      ((integerStablePiFunctor q).map f.hom).hom y = x := by
  let i : f.right ⟶ originalScalarCofiberFunctor.obj f :=
    OriginalScalarCone.cofiberTarget PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) f.hom
  let D := (integerDiagonalDiagramFunctor q).obj f.right
  let E := (integerDiagonalDiagramFunctor q).obj (originalScalarCofiberFunctor.obj f)
  let a : D ⟶ E := (integerDiagonalDiagramFunctor q).map i
  obtain ⟨n, l, hn, b, hb, hNull⟩ := GrpCat.FilteredColimits.colimitMap_kernel_representative a x hx
  let c : D.obj l := (D.map (homOfLE hn)).hom b
  have hRep : (integerStablePiLeg q f.right l).hom c = x := by
    exact (ConcreteCategory.congr_hom ((GrpCat.FilteredColimits.colimitCocone D).w (homOfLE hn)) b).trans hb
  have hcNull : a.app l c = 1 := (ConcreteCategory.congr_hom (a.naturality (homOfLE hn)) b).trans hNull
  let m := integerTailLevel q
  let k := integerTailPositiveIndex q
  obtain ⟨d, hd⟩ := originalScalarStageForward_image_of_kernel f l m k c hcNull
  obtain ⟨y, hy⟩ := originalInteger_image_of_signed_scalar_stage q l f.hom c d hd
  exact ⟨y, hy.trans hRep⟩

end PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

namespace PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
attribute [local instance] MonoidalClosed.enrichedCategorySelf
  PointedCGWH.EnrichedMapping.hasSmallLimits
  HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.nativeHasZeroObject
  HasZeroObject.zeroMorphismsOfZeroObject
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The literal pointed native zero has exactly one original cube class in every degree. -/
theorem originalPointedZero_piN_subsingleton (n : ℕ) :
    Subsingleton (PointedCGWH.piN n (Under.mk (𝟙 CGWH.point.{u, v}))) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨p, rfl⟩ := HomotopyGroup.mk_surjective x
  obtain ⟨q, rfl⟩ := HomotopyGroup.mk_surjective y
  apply congrArg HomotopyGroup.mk
  apply GenLoop.ext
  intro t
  have hP : Subsingleton (CGWH.cgwhToTop.{u, v}.obj
      (Under.mk (𝟙 CGWH.point.{u, v}) : PointedCGWH.{u, v}).right) := by
    change Subsingleton PUnit.{v + 1}
    infer_instance
  exact hP.elim _ _

/-- The original scalar cone has trivial positive groups at every actual native index. -/
theorem originalCone_positive_group_trivial
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) (a : I) (k : ℕ)
    (x : PointedCGWH.piN (k + 1) ((originalConeFunctor.obj X).toEnrichedFunctor.obj a)) :
    x = 1 := by
  let Z : EnrichedFunctorCat PointedCGWH.{u, v} I :=
    HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram
  let r : originalConeFunctor.obj X ⟶ Z :=
    HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.toZero (originalConeFunctor.obj X)
  have hWr : WeakEquivalence r := originalConeCollapse_weakEquivalence X
  have hW : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) r :=
    (HomotopicalAlgebra.weakEquivalence_iff r).mp hWr
  rw [HomotopicalAlgebra.EnrichedProjective.Native.weakEquivalences_eq] at hW
  have hEval := (EvaluationTransfer.evaluationProperty_iff
    (fun a : I => EnrichedFunctorCat.evaluation a) (weakEquivalences PointedCGWH.{u, v}) r).mp hW
  let _ : WeakEquivalence (component r a) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr (hEval a)
  let e := PointedCGWH.piNPositiveMulEquivOfWeakEquivalence k (component r a)
    (inferInstance : WeakEquivalence (component r a))
  let eZ := HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.initialDiagramComponentZeroIso (A := I) a
  let zP := (PointedCGWH.piNPositiveFunctor k).mapIso eZ
  have h0 : Subsingleton (PointedCGWH.piN (k + 1) (0 : PointedCGWH.{u, v})) := by
    let e0 : (0 : PointedCGWH.{u, v}) ≅ Under.mk (𝟙 CGWH.point.{u, v}) :=
      (isZero_zero PointedCGWH.{u, v}).iso
        { unique_to := fun Y =>
            ⟨{ default := Under.mkIdInitial.to Y
               uniq := fun f => Under.mkIdInitial.hom_ext f _ }⟩
          unique_from := fun Y =>
            ⟨{ default := Under.homMk (CGWH.point_isTerminal.from Y.right)
                  (CGWH.point_isTerminal.hom_ext _ _)
               uniq := fun f => Under.UnderMorphism.ext
                  (CGWH.point_isTerminal.hom_ext f.right _) }⟩ }
    let ep := (PointedCGWH.piNPositiveFunctor k).mapIso e0
    refine ⟨fun y z => ep.groupIsoToMulEquiv.injective ?_⟩
    exact (originalPointedZero_piN_subsingleton (k + 1)).elim _ _
  apply e.injective
  apply zP.groupIsoToMulEquiv.injective
  exact h0.elim _ _

end PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

namespace PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
  PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
  PointedCGWH.SequentialSpectrum.StableHomotopy
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.nativeHasZeroObject
  HasZeroObject.zeroMorphismsOfZeroObject

/-- Every original integer class on an actual native scalar cone is the group identity. -/
theorem originalScalarCone_integer_trivial
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (q : ℤ) (X : PointedCGWH.SequentialSpectrum.{u, v})
    (x : (integerStablePiFunctor q).obj (originalConeFunctor.obj X)) : x = 1 := by
  let D := (integerDiagonalDiagramFunctor q).obj (originalConeFunctor.obj X)
  obtain ⟨n, a, rfl⟩ := (D ⋙ forget GrpCat).ιColimitType_jointly_surjective x
  have ha : a = 1 := originalCone_positive_group_trivial X
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne (integerTailLevel q + n))
    (integerTailPositiveIndex q + n) a
  exact (congrArg (fun b => GrpCat.FilteredColimits.G.mk D ⟨n, b⟩) ha).trans
    (GrpCat.FilteredColimits.colimit_one_eq D n).symm

/-- Every original integer map factoring through the actual scalar cone is null. -/
theorem originalScalarCone_integer_composite_null
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (q : ℤ) {A X Y : PointedCGWH.SequentialSpectrum.{u, v}}
    (i : A ⟶ originalConeFunctor.obj X) (p : originalConeFunctor.obj X ⟶ Y)
    (x : (integerStablePiFunctor q).obj A) :
    ((integerStablePiFunctor q).map (i ≫ p)).hom x = 1 := by
  rw [(integerStablePiFunctor q).map_comp]
  exact (congrArg ((integerStablePiFunctor q).map p).hom
    (originalScalarCone_integer_trivial q X (((integerStablePiFunctor q).map i).hom x))).trans
      (map_one _)

/-- The actual source-to-scalar-cofiber integer composite is null in every degree. -/
theorem originalScalarSourceInteger_null
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v})
    (x : (integerStablePiFunctor q).obj f.left) :
    ((integerStablePiFunctor q).map
      (OriginalScalarCone.cofiberTarget PointedCGWH.EnrichedIntervalCylinder.functor
        (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
        (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) f.hom)).hom
        (((integerStablePiFunctor q).map f.hom).hom x) = 1 := by
  let i : f.left ⟶ originalConeFunctor.obj f.left := originalConeInclusion.app f.left
  let p : originalConeFunctor.obj f.left ⟶ originalScalarCofiberFunctor.obj f :=
    OriginalScalarCone.cofiberCone PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) f.hom
  have h := OriginalScalarCone.cofiber_condition PointedCGWH.EnrichedIntervalCylinder.functor
    (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
    (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) f.hom
  exact (ConcreteCategory.congr_hom ((integerStablePiFunctor q).map_comp _ _) x).symm.trans
    ((congrArg (fun k => ((integerStablePiFunctor q).map k).hom x) h).trans
      (originalScalarCone_integer_composite_null q i p x))

end PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

namespace PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
  PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionStablePiGeometry
  PointedCGWH.SequentialSpectrum.StableHomotopy
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.nativeHasZeroObject
  HasZeroObject.zeroMorphismsOfZeroObject

/-- The actual original cofiber inclusion is a genuine whole positive integer group map. -/
def originalScalarCofiberIntegerInclusion
    (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    (integerStablePiFunctor q).obj f.right ⟶
      (integerStablePiFunctor q).obj (originalScalarCofiberFunctor.obj f) :=
  (integerStablePiFunctor q).map
    (OriginalScalarCone.cofiberTarget PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) f.hom)

/-- The complete actual scalar cofiber connecting map retains the original sphere boundary and suspension inverse. -/
def originalScalarCofiberConnectingPlusOne
    (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    (integerStablePiFunctor (q + 1)).obj (originalScalarCofiberFunctor.obj f) ⟶
      (integerStablePiFunctor q).obj f.left :=
  (integerStablePiFunctor (q + 1)).map (originalSphereCofiberBoundary f) ≫
    (integerSuspensionPiNatIso q).inv.app f.left

/-- The entire original integer boundary is natural in every actual Arrow square. -/
@[reassoc]
theorem originalScalarCofiberConnectingPlusOne_naturality
    (q : ℤ) {f g : Arrow PointedCGWH.SequentialSpectrum.{u, v}} (a : f ⟶ g) :
    (integerStablePiFunctor (q + 1)).map (originalScalarCofiberFunctor.map a) ≫
        originalScalarCofiberConnectingPlusOne q g =
      originalScalarCofiberConnectingPlusOne q f ≫ (integerStablePiFunctor q).map a.left := by
  let P := integerStablePiFunctor (q + 1)
  let bF : P.obj (originalScalarCofiberFunctor.obj f) ⟶
      P.obj (tensorLeftObject PointedCGWH.sphereOne f.left) :=
    P.map (originalSphereCofiberBoundary f)
  let bG : P.obj (originalScalarCofiberFunctor.obj g) ⟶
      P.obj (tensorLeftObject PointedCGWH.sphereOne g.left) :=
    P.map (originalSphereCofiberBoundary g)
  let vF : P.obj (tensorLeftObject PointedCGWH.sphereOne f.left) ⟶
      (integerStablePiFunctor q).obj f.left := (integerSuspensionPiNatIso q).inv.app f.left
  let vG : P.obj (tensorLeftObject PointedCGWH.sphereOne g.left) ⟶
      (integerStablePiFunctor q).obj g.left := (integerSuspensionPiNatIso q).inv.app g.left
  let t : P.obj (tensorLeftObject PointedCGWH.sphereOne f.left) ⟶
      P.obj (tensorLeftObject PointedCGWH.sphereOne g.left) :=
    P.map (tensorLeftMap PointedCGWH.sphereOne a.left)
  have hb : P.map (originalScalarCofiberFunctor.map a) ≫ bG = bF ≫ t :=
    (P.map_comp _ _).symm.trans
      ((P.congr_map (originalSphereCofiberBoundary_naturality a)).trans (P.map_comp _ _))
  have hs : t ≫ vG = vF ≫ (integerStablePiFunctor q).map a.left :=
    (integerSuspensionPiNatIso q).inv.naturality a.left
  change P.map (originalScalarCofiberFunctor.map a) ≫ (bG ≫ vG) =
    (bF ≫ vF) ≫ (integerStablePiFunctor q).map a.left
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun h => h ≫ vG) hb).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun h => bF ≫ h) hs).trans (Category.assoc _ _ _).symm)))

/-- The target kernel/image law is derived on the same original scalar cofiber in every integer degree. -/
theorem originalScalarCofiber_exact_at_target
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v})
    (x : (integerStablePiFunctor q).obj f.right) :
    (originalScalarCofiberIntegerInclusion q f).hom x = 1 ↔
      ∃ y : (integerStablePiFunctor q).obj f.left,
        ((integerStablePiFunctor q).map f.hom).hom y = x := by
  constructor
  · exact originalScalarCofiber_integer_kernel_preimage q f x
  · rintro ⟨y, rfl⟩
    exact originalScalarSourceInteger_null q f y

end PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

namespace PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
  PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionStablePiGeometry
  PointedCGWH.SequentialSpectrum.StableHomotopy
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.nativeHasZeroObject
  HasZeroObject.zeroMorphismsOfZeroObject

/-- The original connecting kernel is exactly the original sphere boundary kernel before desuspension. -/
theorem originalScalarConnectingPlusOne_eq_one_iff
    (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v})
    (x : (integerStablePiFunctor (q + 1)).obj (originalScalarCofiberFunctor.obj f)) :
    (originalScalarCofiberConnectingPlusOne q f).hom x = 1 ↔
      ((integerStablePiFunctor (q + 1)).map (originalSphereCofiberBoundary f)).hom x = 1 := by
  let e := (integerSuspensionPiNatIso q).app f.left
  let b := (integerStablePiFunctor (q + 1)).map (originalSphereCofiberBoundary f)
  change e.inv.hom (b.hom x) = 1 ↔ b.hom x = 1
  exact map_eq_one_iff e.inv.hom e.groupIsoToMulEquiv.symm.injective

end PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing


namespace PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
  PointedCGWH.SequentialSpectrum.MappingTelescope.StageIntegerStablePiGeometry
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.nativeHasZeroObject
  HasZeroObject.zeroMorphismsOfZeroObject

/-- The full original integer scalar boundary uses the actual original scalar suspension. -/
def originalScalarIntegerBoundary
    (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    (integerStablePiFunctor q).obj (originalScalarCofiberFunctor.obj f) ⟶
      (integerStablePiFunctor q).obj (originalScalarSuspensionFunctor.obj f.left) :=
  (integerStablePiFunctor q).map (originalScalarBoundary f)

/-- Rotation retains the same actual cofiber target and boundary on original integer maps. -/
theorem originalScalarRotation_integer_leg
    (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    originalScalarCofiberIntegerInclusion q
        ((OriginalScalarCone.rotationArrowFunctor PointedCGWH.EnrichedIntervalCylinder.functor
          (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
          (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1)).obj f) ≫
      (integerStablePiFunctor q).map (originalScalarRotationComparison f) =
        originalScalarIntegerBoundary q f := by
  let P := integerStablePiFunctor q
  let i : f.right ⟶ originalScalarCofiberFunctor.obj f :=
    OriginalScalarCone.cofiberTarget PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) f.hom
  let g : Arrow PointedCGWH.SequentialSpectrum.{u, v} := Arrow.mk i
  let j : g.right ⟶ originalScalarCofiberFunctor.obj g :=
    OriginalScalarCone.cofiberTarget PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) g.hom
  let r : originalScalarCofiberFunctor.obj g ⟶ originalScalarSuspensionFunctor.obj f.left :=
    originalScalarRotationComparison f
  let d : originalScalarCofiberFunctor.obj f ⟶ originalScalarSuspensionFunctor.obj f.left :=
    originalScalarBoundary f
  have h : j ≫ r = d :=
    OriginalScalarCone.rotationComparison_cofiber PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1)
      HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero f
  change P.map j ≫ P.map r = P.map d
  exact (P.map_comp j r).symm.trans (P.congr_map h)

/-- The actual original scalar cofiber is exact at its whole integer group. -/
theorem originalScalarCofiber_exact_at_cofiber
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v})
    (x : (integerStablePiFunctor q).obj (originalScalarCofiberFunctor.obj f)) :
    (originalScalarIntegerBoundary q f).hom x = 1 ↔
      ∃ y : (integerStablePiFunctor q).obj f.right,
        (originalScalarCofiberIntegerInclusion q f).hom y = x := by
  let i : f.right ⟶ originalScalarCofiberFunctor.obj f :=
    OriginalScalarCone.cofiberTarget PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) f.hom
  let g : Arrow PointedCGWH.SequentialSpectrum.{u, v} := Arrow.mk i
  let r : originalScalarCofiberFunctor.obj g ⟶ originalScalarSuspensionFunctor.obj f.left :=
    originalScalarRotationComparison f
  let P := integerStablePiFunctor q
  let _ : WeakEquivalence r := originalScalarRotationComparison_weakEquivalence f
  let _ : IsIso (P.map r) := integerStablePiLevelWeak_isIso q r
    (HomotopicalAlgebra.mem_weakEquivalences r)
  have h : originalScalarCofiberIntegerInclusion q g ≫ P.map r =
      originalScalarIntegerBoundary q f := originalScalarRotation_integer_leg q f
  rw [← h, CategoryTheory.originalGroupMap_kernel_post_iso]
  exact originalScalarCofiber_exact_at_target q g x

end PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

namespace PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
  PointedCGWH.SequentialSpectrum.MappingTelescope.StageIntegerStablePiGeometry
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.nativeHasZeroObject
  HasZeroObject.zeroMorphismsOfZeroObject

/-- The actual double cone retains the two original scalar cone copies. -/
def originalSequentialDoubleCone (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    PointedCGWH.SequentialSpectrum.{u, v} :=
  originalScalarCofiberFunctor.obj (Arrow.mk (originalConeInclusion.app X))

/-- The actual first double-cone collapse keeps the original target-cone quotient. -/
def originalSequentialCollapseLeft (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    originalSequentialDoubleCone X ⟶ originalScalarSuspensionFunctor.obj X :=
  (OriginalScalarCone.cofiberIsPushout PointedCGWH.EnrichedIntervalCylinder.functor
    (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
    (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1)
    (originalConeInclusion.app X)).desc (originalScalarSuspensionQuotient X) 0 (by
      rw [OriginalScalarCone.inclusion_suspensionQuotient, comp_zero])

/-- The actual second double-cone collapse is the literal original scalar boundary. -/
def originalSequentialCollapseRight (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    originalSequentialDoubleCone X ⟶ originalScalarSuspensionFunctor.obj X :=
  originalScalarBoundary (Arrow.mk (originalConeInclusion.app X))

/-- The actual next scalar cofiber maps by both original legs to the target double cone. -/
def originalSequentialRotationToDoubleCone
    (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    originalScalarRotationFunctor.obj f ⟶ originalSequentialDoubleCone f.right := by
  let i : f.right ⟶ originalScalarCofiberFunctor.obj f :=
    OriginalScalarCone.cofiberTarget PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) f.hom
  let a : originalScalarCofiberFunctor.obj f ⟶ originalConeFunctor.obj f.right :=
    OriginalScalarCone.targetConeComparison PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) f
  let l : originalConeFunctor.obj f.right ⟶ originalSequentialDoubleCone f.right :=
    OriginalScalarCone.cofiberTarget PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1)
      (originalConeInclusion.app f.right)
  let r : originalConeFunctor.obj f.right ⟶ originalSequentialDoubleCone f.right :=
    OriginalScalarCone.cofiberCone PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1)
      (originalConeInclusion.app f.right)
  exact (OriginalScalarCone.cofiberIsPushout PointedCGWH.EnrichedIntervalCylinder.functor
    (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
    (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) i).desc (a ≫ l) r (by
      have h : i ≫ a = originalConeInclusion.app f.right :=
        OriginalScalarCone.targetConeComparison_target PointedCGWH.EnrichedIntervalCylinder.functor
          (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
          (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) f
      exact (Category.assoc i a l).symm.trans
        ((congrArg (fun k => k ≫ l) h).trans
          (OriginalScalarCone.cofiber_condition PointedCGWH.EnrichedIntervalCylinder.functor
            (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
            (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1)
            (originalConeInclusion.app f.right))))


/-- Both original double-cone legs identify the first collapse with the accepted native collapse. -/
theorem originalSequentialCollapseLeft_eq_original
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    originalSequentialCollapseLeft X =
      OrdinaryHoChosenPuppeRotation.collapseLeft originalConeFunctor originalConeInclusion
        originalChosenScalarCofiberCone originalChosenScalarCofiberIsColimit
        (HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram
          : PointedCGWH.SequentialSpectrum.{u, v})
        HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero X := by
  let j : X ⟶ originalConeFunctor.obj X := originalConeInclusion.app X
  let l : originalConeFunctor.obj X ⟶ originalSequentialDoubleCone X :=
    OriginalScalarCone.cofiberTarget PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) j
  let r : originalConeFunctor.obj X ⟶ originalSequentialDoubleCone X :=
    OriginalScalarCone.cofiberCone PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) j
  let old : originalSequentialDoubleCone X ⟶ originalScalarSuspensionFunctor.obj X :=
    OrdinaryHoChosenPuppeRotation.collapseLeft originalConeFunctor originalConeInclusion
      originalChosenScalarCofiberCone originalChosenScalarCofiberIsColimit
      (HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram
        : PointedCGWH.SequentialSpectrum.{u, v})
      HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero X
  let sq : IsPushout j j l r :=
    OriginalScalarCone.cofiberIsPushout PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) j
  have hOldL : l ≫ old = originalScalarSuspensionQuotient X :=
    OrdinaryHoChosenPuppeRotation.collapseLeft_right originalConeFunctor originalConeInclusion
      originalChosenScalarCofiberCone originalChosenScalarCofiberIsColimit
      (HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram
        : PointedCGWH.SequentialSpectrum.{u, v})
      HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero X
  have hOldR : r ≫ old = 0 := by
    have h : r ≫ old =
        (HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero
          (A := CategoryTheory.Spectra.Sequential.Index PointedCGWH.sphereOne)).from_
          (originalConeFunctor.obj X) ≫
        OriginalScalarCone.suspensionZeroLeg PointedCGWH.EnrichedIntervalCylinder.functor
          (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
          (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1)
          HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero X :=
      OrdinaryHoChosenPuppeRotation.collapseLeft_left originalConeFunctor originalConeInclusion
        originalChosenScalarCofiberCone originalChosenScalarCofiberIsColimit
        (HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram
          : PointedCGWH.SequentialSpectrum.{u, v})
        HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero X
    exact h.trans (by
      rw [HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero.eq_of_tgt
        (HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero.from_
          (originalConeFunctor.obj X)) 0, zero_comp])
  change originalSequentialCollapseLeft X = old
  apply sq.hom_ext
  · exact (sq.inl_desc _ _ _).trans hOldL.symm
  · exact (sq.inr_desc _ _ _).trans hOldR.symm

/-- Both original double-cone legs identify the second collapse with the accepted native collapse. -/
theorem originalSequentialCollapseRight_eq_original
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    originalSequentialCollapseRight X =
      OrdinaryHoChosenPuppeRotation.collapseRight originalConeFunctor originalConeInclusion
        originalChosenScalarCofiberCone originalChosenScalarCofiberIsColimit
        (HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram
          : PointedCGWH.SequentialSpectrum.{u, v})
        HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero X := by
  let f : Arrow PointedCGWH.SequentialSpectrum.{u, v} := Arrow.mk (originalConeInclusion.app X)
  let old : originalSequentialDoubleCone X ⟶ originalScalarSuspensionFunctor.obj X :=
    OrdinaryHoChosenPuppeRotation.collapseRight originalConeFunctor originalConeInclusion
      originalChosenScalarCofiberCone originalChosenScalarCofiberIsColimit
      (HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram
        : PointedCGWH.SequentialSpectrum.{u, v})
      HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero X
  let l : originalConeFunctor.obj X ⟶ originalSequentialDoubleCone X :=
    OriginalScalarCone.cofiberTarget PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) f.hom
  let r : originalConeFunctor.obj X ⟶ originalSequentialDoubleCone X :=
    OriginalScalarCone.cofiberCone PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) f.hom
  let sq : IsPushout f.hom (originalConeInclusion.app X) l r :=
    OriginalScalarCone.cofiberIsPushout PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) f.hom
  have hOldL : l ≫ old = 0 := by
    let Z : PointedCGWH.SequentialSpectrum.{u, v} :=
      HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram
    let z : originalConeFunctor.obj X ⟶ Z :=
      HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero.from_
        (originalConeFunctor.obj X)
    let k : Z ⟶ originalScalarSuspensionFunctor.obj X :=
      OriginalScalarCone.suspensionZeroLeg PointedCGWH.EnrichedIntervalCylinder.functor
        (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
        (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1)
        HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero X
    have h : l ≫ old = z ≫ k :=
      OrdinaryHoChosenPuppeRotation.collapseRight_right originalConeFunctor
        originalConeInclusion originalChosenScalarCofiberCone originalChosenScalarCofiberIsColimit Z
        HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero X
    have hz : z = 0 := HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero.eq_of_tgt z 0
    exact h.trans ((congrArg (fun t => t ≫ k) hz).trans (zero_comp (f := k)))
  have hOldR : r ≫ old = originalScalarSuspensionQuotient X :=
    OrdinaryHoChosenPuppeRotation.collapseRight_left originalConeFunctor originalConeInclusion
      originalChosenScalarCofiberCone originalChosenScalarCofiberIsColimit
      (HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram
        : PointedCGWH.SequentialSpectrum.{u, v})
      HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero X
  have hL : l ≫ originalSequentialCollapseRight X = 0 :=
    OriginalScalarCone.boundary_target PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1)
      HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero f
  have hR : r ≫ originalSequentialCollapseRight X = originalScalarSuspensionQuotient X :=
    OriginalScalarCone.boundary_cone PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1)
      HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero f
  change originalSequentialCollapseRight X = old
  apply sq.hom_ext
  · exact hL.trans hOldL.symm
  · exact hR.trans hOldR.symm

/-- The first actual collapse is level weak for every original source. -/
theorem originalSequentialCollapseLeft_weakEquivalence
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (X : PointedCGWH.SequentialSpectrum.{u, v}) : WeakEquivalence (originalSequentialCollapseLeft X) :=
  (originalSequentialCollapseLeft_eq_original X).symm ▸ originalPuppeCollapseLeft_weakEquivalence X

/-- The second actual collapse is level weak for every original source. -/
theorem originalSequentialCollapseRight_weakEquivalence
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (X : PointedCGWH.SequentialSpectrum.{u, v}) : WeakEquivalence (originalSequentialCollapseRight X) :=
  (originalSequentialCollapseRight_eq_original X).symm ▸ originalPuppeCollapseRight_weakEquivalence X

/-- The first collapse retains the entire original scalar suspended input map. -/
theorem originalSequentialRotation_collapseLeft
    (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    originalSequentialRotationToDoubleCone f ≫ originalSequentialCollapseLeft f.right =
      originalScalarRotationComparison f ≫ originalScalarSuspensionFunctor.map f.hom := by
  let i : f.right ⟶ originalScalarCofiberFunctor.obj f :=
    OriginalScalarCone.cofiberTarget PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) f.hom
  let g : Arrow PointedCGWH.SequentialSpectrum.{u, v} := Arrow.mk i
  let l : g.right ⟶ originalScalarCofiberFunctor.obj g :=
    OriginalScalarCone.cofiberTarget PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) g.hom
  let r : originalConeFunctor.obj g.left ⟶ originalScalarCofiberFunctor.obj g :=
    OriginalScalarCone.cofiberCone PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) g.hom
  let t : originalScalarCofiberFunctor.obj g ⟶ originalSequentialDoubleCone f.right :=
    originalSequentialRotationToDoubleCone f
  let L : originalSequentialDoubleCone f.right ⟶ originalScalarSuspensionFunctor.obj f.right :=
    originalSequentialCollapseLeft f.right
  let ρ : originalScalarCofiberFunctor.obj g ⟶ originalScalarSuspensionFunctor.obj f.left :=
    originalScalarRotationComparison f
  let Sf : originalScalarSuspensionFunctor.obj f.left ⟶
      originalScalarSuspensionFunctor.obj f.right := originalScalarSuspensionFunctor.map f.hom
  let a : originalScalarCofiberFunctor.obj f ⟶ originalConeFunctor.obj f.right :=
    OriginalScalarCone.targetConeComparison PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) f
  let dL : originalConeFunctor.obj f.right ⟶ originalSequentialDoubleCone f.right :=
    OriginalScalarCone.cofiberTarget PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) (originalConeInclusion.app f.right)
  let dR : originalConeFunctor.obj f.right ⟶ originalSequentialDoubleCone f.right :=
    OriginalScalarCone.cofiberCone PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) (originalConeInclusion.app f.right)
  let sq : IsPushout i (originalConeInclusion.app f.right) l r :=
    OriginalScalarCone.cofiberIsPushout PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) i
  have hTL : l ≫ t = a ≫ dL := IsPushout.inl_desc _ _ _ _
  have hTR : r ≫ t = dR := IsPushout.inr_desc _ _ _ _
  have hLL : dL ≫ L = originalScalarSuspensionQuotient f.right := IsPushout.inl_desc _ _ _ _
  have hLR : dR ≫ L = 0 := IsPushout.inr_desc _ _ _ _
  have hρL : l ≫ ρ = originalScalarBoundary f :=
    OriginalScalarCone.rotationComparison_cofiber PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1)
      HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero f
  have hρR : r ≫ ρ = 0 :=
    OriginalScalarCone.rotationComparison_cone PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1)
      HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero f
  have ha : a ≫ originalScalarSuspensionQuotient f.right = originalScalarBoundary f ≫ Sf :=
    (OriginalScalarCone.boundary_suspension_factors_targetCone
      PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1)
      HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero f).symm
  change t ≫ L = ρ ≫ Sf
  apply sq.hom_ext
  · exact (Category.assoc l t L).symm.trans
      ((congrArg (fun h => h ≫ L) hTL).trans
        ((Category.assoc a dL L).trans
          ((congrArg (fun h => a ≫ h) hLL).trans
            (ha.trans ((congrArg (fun h => h ≫ Sf) hρL).symm.trans (Category.assoc l ρ Sf))))))
  · exact (Category.assoc r t L).symm.trans
      ((congrArg (fun h => h ≫ L) hTR).trans
        (hLR.trans ((zero_comp (f := Sf)).symm.trans
          ((congrArg (fun h => h ≫ Sf) hρR).symm.trans (Category.assoc r ρ Sf)))))

/-- The actual next scalar boundary uses the complete original target-inclusion Arrow. -/
def originalSequentialNextBoundary (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    originalScalarRotationFunctor.obj f ⟶ originalScalarSuspensionFunctor.obj f.right :=
  originalScalarBoundary
    ((OriginalScalarCone.rotationArrowFunctor PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1)).obj f)

/-- The entire original scalar rotation's target-to-double-cone leg is retained. -/
theorem originalSequentialRotationToDoubleCone_target
    (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    OriginalScalarCone.cofiberTarget PointedCGWH.EnrichedIntervalCylinder.functor
        (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
        (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1)
        (OriginalScalarCone.cofiberTarget PointedCGWH.EnrichedIntervalCylinder.functor
          (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
          (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) f.hom) ≫
      originalSequentialRotationToDoubleCone f =
        OriginalScalarCone.targetConeComparison PointedCGWH.EnrichedIntervalCylinder.functor
          (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
          (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) f ≫
        OriginalScalarCone.cofiberTarget PointedCGWH.EnrichedIntervalCylinder.functor
          (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
          (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) (originalConeInclusion.app f.right) :=
  IsPushout.inl_desc _ _ _ _

/-- The whole original scalar rotation keeps its cone-to-double-cone leg. -/
theorem originalSequentialRotationToDoubleCone_cone
    (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    OriginalScalarCone.cofiberCone PointedCGWH.EnrichedIntervalCylinder.functor
        (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
        (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1)
        (OriginalScalarCone.cofiberTarget PointedCGWH.EnrichedIntervalCylinder.functor
          (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
          (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) f.hom) ≫
      originalSequentialRotationToDoubleCone f =
        OriginalScalarCone.cofiberCone PointedCGWH.EnrichedIntervalCylinder.functor
          (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
          (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) (originalConeInclusion.app f.right) :=
  IsPushout.inr_desc _ _ _ _

/-- The actual second collapse kills the entire original target cone leg. -/
theorem originalSequentialCollapseRight_target (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    OriginalScalarCone.cofiberTarget PointedCGWH.EnrichedIntervalCylinder.functor
        (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
        (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) (originalConeInclusion.app X) ≫
      originalSequentialCollapseRight X = 0 :=
  OriginalScalarCone.boundary_target PointedCGWH.EnrichedIntervalCylinder.functor
    (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
    (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1)
    HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero
    (Arrow.mk (originalConeInclusion.app X) : Arrow PointedCGWH.SequentialSpectrum.{u, v})

/-- The actual second collapse keeps the full original cone-to-suspension leg. -/
theorem originalSequentialCollapseRight_cone (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    OriginalScalarCone.cofiberCone PointedCGWH.EnrichedIntervalCylinder.functor
        (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
        (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) (originalConeInclusion.app X) ≫
      originalSequentialCollapseRight X = originalScalarSuspensionQuotient X :=
  OriginalScalarCone.boundary_cone PointedCGWH.EnrichedIntervalCylinder.functor
    (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
    (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1)
    HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero
    (Arrow.mk (originalConeInclusion.app X) : Arrow PointedCGWH.SequentialSpectrum.{u, v})

/-- The actual next boundary kills the original next target leg. -/
theorem originalSequentialNextBoundary_target
    (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    OriginalScalarCone.cofiberTarget PointedCGWH.EnrichedIntervalCylinder.functor
        (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
        (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1)
        (OriginalScalarCone.cofiberTarget PointedCGWH.EnrichedIntervalCylinder.functor
          (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
          (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) f.hom) ≫
      originalSequentialNextBoundary f = 0 :=
  OriginalScalarCone.boundary_target PointedCGWH.EnrichedIntervalCylinder.functor
    (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
    (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1)
    HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero
    (Arrow.mk (OriginalScalarCone.cofiberTarget PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) f.hom)
      : Arrow PointedCGWH.SequentialSpectrum.{u, v})

/-- The actual next boundary retains the entire original target cone quotient. -/
theorem originalSequentialNextBoundary_cone
    (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    OriginalScalarCone.cofiberCone PointedCGWH.EnrichedIntervalCylinder.functor
        (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
        (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1)
        (OriginalScalarCone.cofiberTarget PointedCGWH.EnrichedIntervalCylinder.functor
          (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
          (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) f.hom) ≫
      originalSequentialNextBoundary f = originalScalarSuspensionQuotient f.right :=
  OriginalScalarCone.boundary_cone PointedCGWH.EnrichedIntervalCylinder.functor
    (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
    (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1)
    HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram_isZero
    (Arrow.mk (OriginalScalarCone.cofiberTarget PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) f.hom)
      : Arrow PointedCGWH.SequentialSpectrum.{u, v})

/-- The second collapse retains the exact original next scalar boundary. -/
theorem originalSequentialRotation_collapseRight
    (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    originalSequentialRotationToDoubleCone f ≫ originalSequentialCollapseRight f.right =
      originalSequentialNextBoundary f := by
  let i : f.right ⟶ originalScalarCofiberFunctor.obj f :=
    OriginalScalarCone.cofiberTarget PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) f.hom
  let g : Arrow PointedCGWH.SequentialSpectrum.{u, v} := Arrow.mk i
  let l : g.right ⟶ originalScalarCofiberFunctor.obj g :=
    OriginalScalarCone.cofiberTarget PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) i
  let r : originalConeFunctor.obj f.right ⟶ originalScalarCofiberFunctor.obj g :=
    OriginalScalarCone.cofiberCone PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) i
  let t : originalScalarCofiberFunctor.obj g ⟶ originalSequentialDoubleCone f.right :=
    originalSequentialRotationToDoubleCone f
  let R : originalSequentialDoubleCone f.right ⟶ originalScalarSuspensionFunctor.obj f.right :=
    originalSequentialCollapseRight f.right
  let b : originalScalarCofiberFunctor.obj g ⟶ originalScalarSuspensionFunctor.obj f.right :=
    originalSequentialNextBoundary f
  let a : originalScalarCofiberFunctor.obj f ⟶ originalConeFunctor.obj f.right :=
    OriginalScalarCone.targetConeComparison PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) f
  let dL : originalConeFunctor.obj f.right ⟶ originalSequentialDoubleCone f.right :=
    OriginalScalarCone.cofiberTarget PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) (originalConeInclusion.app f.right)
  let dR : originalConeFunctor.obj f.right ⟶ originalSequentialDoubleCone f.right :=
    OriginalScalarCone.cofiberCone PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) (originalConeInclusion.app f.right)
  let sq : IsPushout i (originalConeInclusion.app f.right) l r :=
    OriginalScalarCone.cofiberIsPushout PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) i
  have hTL : l ≫ t = a ≫ dL := originalSequentialRotationToDoubleCone_target f
  have hTR : r ≫ t = dR := originalSequentialRotationToDoubleCone_cone f
  have hRL : dL ≫ R = 0 := originalSequentialCollapseRight_target f.right
  have hRR : dR ≫ R = originalScalarSuspensionQuotient f.right :=
    originalSequentialCollapseRight_cone f.right
  have hbL : l ≫ b = 0 := originalSequentialNextBoundary_target f
  have hbR : r ≫ b = originalScalarSuspensionQuotient f.right :=
    originalSequentialNextBoundary_cone f
  change t ≫ R = b
  apply sq.hom_ext
  · exact (Category.assoc l t R).symm.trans
      ((congrArg (fun h => h ≫ R) hTL).trans
        ((Category.assoc a dL R).trans
          ((congrArg (fun h => a ≫ h) hRL).trans ((comp_zero (f := a)).trans hbL.symm))))
  · exact (Category.assoc r t R).symm.trans
      ((congrArg (fun h => h ≫ R) hTR).trans (hRR.trans hbR.symm))

/-- Every original scalar-suspension source kernel is the image of the actual original boundary. -/
theorem originalScalarCofiber_exact_at_scalar_source
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v})
    (x : (integerStablePiFunctor q).obj (originalScalarSuspensionFunctor.obj f.left)) :
    ((integerStablePiFunctor q).map (originalScalarSuspensionFunctor.map f.hom)).hom x = 1 ↔
      ∃ y : (integerStablePiFunctor q).obj (originalScalarCofiberFunctor.obj f),
        (originalScalarIntegerBoundary q f).hom y = x := by
  let P := integerStablePiFunctor q
  let i : f.right ⟶ originalScalarCofiberFunctor.obj f :=
    OriginalScalarCone.cofiberTarget PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) f.hom
  let g : Arrow PointedCGWH.SequentialSpectrum.{u, v} := Arrow.mk i
  let ρ : originalScalarCofiberFunctor.obj g ⟶ originalScalarSuspensionFunctor.obj f.left :=
    originalScalarRotationComparison f
  let Rf : originalScalarCofiberFunctor.obj g ⟶ originalSequentialDoubleCone f.right :=
    originalSequentialRotationToDoubleCone f
  let LY : originalSequentialDoubleCone f.right ⟶ originalScalarSuspensionFunctor.obj f.right :=
    originalSequentialCollapseLeft f.right
  let RY : originalSequentialDoubleCone f.right ⟶ originalScalarSuspensionFunctor.obj f.right :=
    originalSequentialCollapseRight f.right
  let _ : WeakEquivalence ρ := originalScalarRotationComparison_weakEquivalence f
  let _ : IsIso (P.map ρ) := integerStablePiLevelWeak_isIso q ρ (mem_weakEquivalences ρ)
  let _ : WeakEquivalence LY := originalSequentialCollapseLeft_weakEquivalence f.right
  let _ : WeakEquivalence RY := originalSequentialCollapseRight_weakEquivalence f.right
  let _ : IsIso (P.map LY) := integerStablePiLevelWeak_isIso q LY (mem_weakEquivalences LY)
  let _ : IsIso (P.map RY) := integerStablePiLevelWeak_isIso q RY (mem_weakEquivalences RY)
  let s := originalScalarSuspensionFunctor.map f.hom
  let b := originalScalarBoundary g
  have hL : P.map Rf ≫ P.map LY = P.map ρ ≫ P.map s :=
    (P.map_comp _ _).symm.trans
      ((P.congr_map (originalSequentialRotation_collapseLeft f)).trans (P.map_comp _ _))
  have hR : P.map Rf ≫ P.map RY = P.map b :=
    (P.map_comp _ _).symm.trans (P.congr_map (originalSequentialRotation_collapseRight f))
  let e := asIso (P.map ρ)
  let z := e.inv.hom x
  have hz : (P.map ρ).hom z = x := ConcreteCategory.congr_hom e.inv_hom_id x
  have hKernel := CategoryTheory.originalGroupMap_double_collapse_kernel
    (P.map Rf) (P.map LY) (P.map RY) (P.map ρ) (P.map s) (P.map b) hL hR z
  constructor
  · intro hx
    have hb : (originalScalarIntegerBoundary q g).hom z = 1 :=
      hKernel.mp (by rw [hz]; exact hx)
    obtain ⟨y, hy⟩ := (originalScalarCofiber_exact_at_cofiber q g z).mp hb
    refine ⟨y, ?_⟩
    have hLeg := ConcreteCategory.congr_hom (originalScalarRotation_integer_leg q f) y
    exact hLeg.symm.trans ((congrArg (P.map ρ).hom hy).trans hz)
  · rintro ⟨y, rfl⟩
    have hj := originalScalarRotation_integer_leg q f
    have hNull := (originalScalarCofiber_exact_at_cofiber q g
      ((originalScalarCofiberIntegerInclusion q g).hom y)).mpr ⟨y, rfl⟩
    have hk := CategoryTheory.originalGroupMap_double_collapse_kernel
      (P.map Rf) (P.map LY) (P.map RY) (P.map ρ) (P.map s) (P.map b) hL hR
      ((originalScalarCofiberIntegerInclusion q g).hom y)
    have hOut := hk.mpr hNull
    exact (congrArg (P.map s).hom (ConcreteCategory.congr_hom hj y)).symm.trans hOut

end PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

namespace PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
  PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionStablePiGeometry
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.nativeHasZeroObject
  HasZeroObject.zeroMorphismsOfZeroObject

/-- The original integer scalar suspension isomorphism uses the actual native sphere comparison. -/
def originalScalarIntegerSuspensionIso
    (q : ℤ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (integerStablePiFunctor q).obj X ≅
      (integerStablePiFunctor (q + 1)).obj (originalScalarSuspensionFunctor.obj X) :=
  by
    let P := integerStablePiFunctor (q + 1)
    let SX : PointedCGWH.SequentialSpectrum.{u, v} := tensorLeftObject PointedCGWH.sphereOne X
    let e : (integerStablePiFunctor q).obj X ≅ P.obj SX := (integerSuspensionPiNatIso q).app X
    let h : originalScalarSuspensionFunctor.obj X ≅ SX := originalScalarSuspensionSphereIso X
    let eh : P.obj SX ≅ P.obj (originalScalarSuspensionFunctor.obj X) := P.mapIso h.symm
    exact e ≪≫ eh

/-- The full original scalar suspension Iso retains every actual source map. -/
theorem originalScalarIntegerSuspensionIso_hom_naturality
    (q : ℤ) {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (integerStablePiFunctor q).map f ≫ (originalScalarIntegerSuspensionIso q Y).hom =
      (originalScalarIntegerSuspensionIso q X).hom ≫
        (integerStablePiFunctor (q + 1)).map (originalScalarSuspensionFunctor.map f) := by
  let eX : originalScalarSuspensionFunctor.obj X ≅
      tensorLeftObject PointedCGWH.sphereOne X := originalScalarSuspensionSphereIso X
  let eY : originalScalarSuspensionFunctor.obj Y ≅
      tensorLeftObject PointedCGWH.sphereOne Y := originalScalarSuspensionSphereIso Y
  let P := integerStablePiFunctor (q + 1)
  have hn : tensorLeftMap PointedCGWH.sphereOne f ≫ eY.inv =
      eX.inv ≫ originalScalarSuspensionFunctor.map f :=
    (originalScalarSuspensionSphereNatIso).inv.naturality f
  let vX : P.obj (tensorLeftObject PointedCGWH.sphereOne X) ⟶
      P.obj (originalScalarSuspensionFunctor.obj X) := P.map eX.inv
  let vY : P.obj (tensorLeftObject PointedCGWH.sphereOne Y) ⟶
      P.obj (originalScalarSuspensionFunctor.obj Y) := P.map eY.inv
  have hp : P.map (tensorLeftMap PointedCGWH.sphereOne f) ≫ vY =
      vX ≫ P.map (originalScalarSuspensionFunctor.map f) :=
    (P.map_comp _ _).symm.trans ((P.congr_map hn).trans (P.map_comp _ _))
  let uX : (integerStablePiFunctor q).obj X ⟶ P.obj (tensorLeftObject PointedCGWH.sphereOne X) :=
    (integerSuspensionPiNatIso q).hom.app X
  let uY : (integerStablePiFunctor q).obj Y ⟶ P.obj (tensorLeftObject PointedCGWH.sphereOne Y) :=
    (integerSuspensionPiNatIso q).hom.app Y
  have hu : (integerStablePiFunctor q).map f ≫ uY =
      uX ≫ P.map (tensorLeftMap PointedCGWH.sphereOne f) :=
    (integerSuspensionPiNatIso q).hom.naturality f
  change (integerStablePiFunctor q).map f ≫ (uY ≫ vY) =
    (uX ≫ vX) ≫ P.map (originalScalarSuspensionFunctor.map f)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun h => h ≫ vY) hu).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun h => uX ≫ h) hp).trans (Category.assoc _ _ _).symm)))

/-- Genuine original integer isomorphisms induce the same actual scalar-suspension isomorphisms. -/
theorem originalScalarSuspension_integerPi_isIso
    (q : ℤ) {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hf : IsIso ((integerStablePiFunctor (q - 1)).map f)) :
    IsIso ((integerStablePiFunctor q).map (originalScalarSuspensionFunctor.map f)) := by
  let _ : IsIso ((integerStablePiFunctor (q - 1)).map f) := hf
  let eX := originalScalarIntegerSuspensionIso (q - 1) X
  let eY := originalScalarIntegerSuspensionIso (q - 1) Y
  let p := (integerStablePiFunctor (q - 1)).map f
  let r := (integerStablePiFunctor ((q - 1) + 1)).map
    (originalScalarSuspensionFunctor.map f)
  have h : p ≫ eY.hom = eX.hom ≫ r :=
    originalScalarIntegerSuspensionIso_hom_naturality (q - 1) f
  let _ : IsIso (p ≫ eY.hom) := inferInstance
  let _ : IsIso (eX.hom ≫ r) := h ▸ inferInstanceAs (IsIso (p ≫ eY.hom))
  have hr : IsIso r := IsIso.of_isIso_comp_left eX.hom r
  have hq : (q - 1) + 1 = q := by omega
  exact Eq.mp (congrArg (fun t : ℤ =>
    IsIso ((integerStablePiFunctor t).map (originalScalarSuspensionFunctor.map f))) hq) hr

end PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing


namespace PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
  PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionStablePiGeometry
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.nativeHasZeroObject
  HasZeroObject.zeroMorphismsOfZeroObject

/-- The actual integer connecting map is scalar boundary followed by the inverse of the original scalar suspension Iso. -/
def originalScalarIntegerConnectingPlusOne
    (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    (integerStablePiFunctor (q + 1)).obj (originalScalarCofiberFunctor.obj f) ⟶
      (integerStablePiFunctor q).obj f.left :=
  originalScalarIntegerBoundary (q + 1) f ≫
    (originalScalarIntegerSuspensionIso q f.left).inv

/-- The actual complete connecting function equals the original sphere-boundary definition. -/
theorem originalScalarIntegerConnectingPlusOne_eq
    (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    originalScalarIntegerConnectingPlusOne q f = originalScalarCofiberConnectingPlusOne q f := by
  let P := integerStablePiFunctor (q + 1)
  let b : P.obj (originalScalarCofiberFunctor.obj f) ⟶
      P.obj (originalScalarSuspensionFunctor.obj f.left) :=
    P.map (originalScalarBoundary f)
  let e : P.obj (originalScalarSuspensionFunctor.obj f.left) ⟶
      P.obj (tensorLeftObject PointedCGWH.sphereOne f.left) :=
    P.map (originalScalarSuspensionSphereIso f.left).hom
  let u : P.obj (tensorLeftObject PointedCGWH.sphereOne f.left) ⟶
      (integerStablePiFunctor q).obj f.left := (integerSuspensionPiNatIso q).inv.app f.left
  have hb : b ≫ e = P.map (originalSphereCofiberBoundary f) :=
    (P.map_comp _ _).symm
  change b ≫ (e ≫ u) = P.map (originalSphereCofiberBoundary f) ≫ u
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun h => h ≫ u) hb)

/-- The same original cofiber sequence is exact at its unsuspended source in every integer degree. -/
theorem originalScalarCofiber_exact_at_source
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v})
    (x : (integerStablePiFunctor q).obj f.left) :
    ((integerStablePiFunctor q).map f.hom).hom x = 1 ↔
      ∃ y : (integerStablePiFunctor (q + 1)).obj (originalScalarCofiberFunctor.obj f),
        (originalScalarCofiberConnectingPlusOne q f).hom y = x := by
  let eX := originalScalarIntegerSuspensionIso q f.left
  let eY := originalScalarIntegerSuspensionIso q f.right
  let P := integerStablePiFunctor q
  let R := integerStablePiFunctor (q + 1)
  let s := originalScalarSuspensionFunctor.map f.hom
  have hn : P.map f.hom ≫ eY.hom = eX.hom ≫ R.map s :=
    originalScalarIntegerSuspensionIso_hom_naturality q f.hom
  have hk : (P.map f.hom).hom x = 1 ↔ (R.map s).hom (eX.hom.hom x) = 1 := by
    have h := ConcreteCategory.congr_hom hn x
    constructor
    · intro hx
      exact h.symm.trans ((congrArg eY.hom.hom hx).trans (map_one _))
    · intro hx
      apply eY.groupIsoToMulEquiv.injective
      exact h.trans hx |>.trans (map_one _).symm
  rw [hk]
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (originalScalarCofiber_exact_at_scalar_source (q + 1) f
      (eX.hom.hom x)).mp hx
    refine ⟨y, ?_⟩
    rw [← originalScalarIntegerConnectingPlusOne_eq]
    change eX.inv.hom ((originalScalarIntegerBoundary (q + 1) f).hom y) = x
    exact (congrArg eX.inv.hom hy).trans (ConcreteCategory.congr_hom eX.hom_inv_id x)
  · rintro ⟨y, hy⟩
    have h : (originalScalarIntegerBoundary (q + 1) f).hom y = eX.hom.hom x := by
      rw [← originalScalarIntegerConnectingPlusOne_eq] at hy
      change eX.inv.hom ((originalScalarIntegerBoundary (q + 1) f).hom y) = x at hy
      have hp := congrArg eX.hom.hom hy
      exact (ConcreteCategory.congr_hom eX.inv_hom_id
        ((originalScalarIntegerBoundary (q + 1) f).hom y)).symm.trans hp
    exact (originalScalarCofiber_exact_at_scalar_source (q + 1) f
      (eX.hom.hom x)).mpr ⟨y, h⟩

end PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing


namespace PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
  PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionStablePiGeometry
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.nativeHasZeroObject
  HasZeroObject.zeroMorphismsOfZeroObject

/-- The original signed connecting kernel is precisely the original cofiber inclusion image. -/
theorem originalScalarCofiberConnecting_exact_at_cofiber
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v})
    (x : (integerStablePiFunctor (q + 1)).obj (originalScalarCofiberFunctor.obj f)) :
    (originalScalarCofiberConnectingPlusOne q f).hom x = 1 ↔
      ∃ y : (integerStablePiFunctor (q + 1)).obj f.right,
        (originalScalarCofiberIntegerInclusion (q + 1) f).hom y = x := by
  rw [← originalScalarIntegerConnectingPlusOne_eq]
  let e := originalScalarIntegerSuspensionIso q f.left
  have h : originalScalarIntegerBoundary (q + 1) f ≫ e.inv =
      originalScalarIntegerConnectingPlusOne q f := rfl
  rw [← h, CategoryTheory.originalGroupMap_kernel_post_iso]
  exact originalScalarCofiber_exact_at_cofiber (q + 1) f x

/-- The same original inclusion and signed connecting map form a genuine group exact pair. -/
theorem originalScalarCofiberInteger_mulExact_connecting
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    Function.MulExact (originalScalarCofiberIntegerInclusion (q + 1) f).hom
      (originalScalarCofiberConnectingPlusOne q f).hom :=
  originalScalarCofiberConnecting_exact_at_cofiber q f

/-- The actual signed connecting map and input map form the genuine original group exact pair. -/
theorem originalScalarCofiberInteger_mulExact_source
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    Function.MulExact (originalScalarCofiberConnectingPlusOne q f).hom
      ((integerStablePiFunctor q).map f.hom).hom :=
  originalScalarCofiber_exact_at_source q f

end PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing


namespace PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.nativeHasZeroObject
  HasZeroObject.zeroMorphismsOfZeroObject

/-- The original scalar cofiber target inclusion retains every integer Arrow square. -/
@[reassoc]
theorem originalScalarCofiberIntegerInclusion_naturality
    (q : ℤ) {f g : Arrow PointedCGWH.SequentialSpectrum.{u, v}} (a : f ⟶ g) :
    (integerStablePiFunctor q).map a.right ≫ originalScalarCofiberIntegerInclusion q g =
      originalScalarCofiberIntegerInclusion q f ≫
        (integerStablePiFunctor q).map (originalScalarCofiberFunctor.map a) := by
  let P := integerStablePiFunctor q
  exact (P.map_comp _ _).symm.trans
    ((P.congr_map (OriginalScalarCone.cofiberTarget_map
      PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) a).symm).trans
      (P.map_comp _ _))

/-- Every original scalar boundary retains the complete actual integer naturality square. -/
@[reassoc]
theorem originalScalarIntegerBoundary_naturality
    (q : ℤ) {f g : Arrow PointedCGWH.SequentialSpectrum.{u, v}} (a : f ⟶ g) :
    (integerStablePiFunctor q).map (originalScalarCofiberFunctor.map a) ≫
      originalScalarIntegerBoundary q g =
        originalScalarIntegerBoundary q f ≫
          (integerStablePiFunctor q).map (originalScalarSuspensionFunctor.map a.left) := by
  let P := integerStablePiFunctor q
  exact (P.map_comp _ _).symm.trans
    ((P.congr_map (originalScalarBoundary_naturality a)).trans (P.map_comp _ _))

/-- Exactness at the original target is the genuine group exact pair on its actual two maps. -/
theorem originalScalarCofiberInteger_mulExact_target
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    Function.MulExact ((integerStablePiFunctor q).map f.hom).hom
      (originalScalarCofiberIntegerInclusion q f).hom :=
  originalScalarCofiber_exact_at_target q f

/-- Exactness at the actual scalar cofiber is the original group exact pair. -/
theorem originalScalarCofiberInteger_mulExact_cofiber
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    Function.MulExact (originalScalarCofiberIntegerInclusion q f).hom
      (originalScalarIntegerBoundary q f).hom :=
  originalScalarCofiber_exact_at_cofiber q f

/-- The actual scalar-suspension source keeps the genuine original group exact pair. -/
theorem originalScalarCofiberInteger_mulExact_scalar_source
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    Function.MulExact (originalScalarIntegerBoundary q f).hom
      ((integerStablePiFunctor q).map (originalScalarSuspensionFunctor.map f.hom)).hom :=
  originalScalarCofiber_exact_at_scalar_source q f

end PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing









namespace PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.nativeHasZeroObject
  HasZeroObject.zeroMorphismsOfZeroObject

/-- The original integer degree has its literal minus-one plus-one equality. -/
theorem originalIntegerMinusOnePlusOne (q : ℤ) : (q - 1) + 1 = q := by omega

/-- Both actual integer degree functors are compared by their literal equality Iso. -/
def originalIntegerMinusOneDegreeIso (q : ℤ) :
    integerStablePiFunctor q ≅ integerStablePiFunctor ((q - 1) + 1) :=
  eqToIso (congrArg integerStablePiFunctor (originalIntegerMinusOnePlusOne q).symm)

/-- The original connecting map keeps its degree cast and complete genuine connecting map. -/
def originalScalarCofiberConnecting
    (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    (integerStablePiFunctor q).obj (originalScalarCofiberFunctor.obj f) ⟶
      (integerStablePiFunctor (q - 1)).obj f.left :=
  (originalIntegerMinusOneDegreeIso q).hom.app (originalScalarCofiberFunctor.obj f) ≫
    originalScalarCofiberConnectingPlusOne (q - 1) f

/-- Every original Arrow square retains the entire degree-minus-one boundary square. -/
@[reassoc]
theorem originalScalarCofiberConnecting_naturality
    (q : ℤ) {f g : Arrow PointedCGWH.SequentialSpectrum.{u, v}} (a : f ⟶ g) :
    (integerStablePiFunctor q).map (originalScalarCofiberFunctor.map a) ≫
      originalScalarCofiberConnecting q g =
        originalScalarCofiberConnecting q f ≫ (integerStablePiFunctor (q - 1)).map a.left := by
  let e := originalIntegerMinusOneDegreeIso q
  let m := originalScalarCofiberFunctor.map a
  let bf := originalScalarCofiberConnectingPlusOne (q - 1) f
  let bg := originalScalarCofiberConnectingPlusOne (q - 1) g
  have hn := e.hom.naturality m
  have hb := originalScalarCofiberConnectingPlusOne_naturality (q - 1) a
  change (integerStablePiFunctor q).map m ≫ (e.hom.app _ ≫ bg) =
    (e.hom.app _ ≫ bf) ≫ (integerStablePiFunctor (q - 1)).map a.left
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun h => h ≫ bg) hn).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun h => e.hom.app (originalScalarCofiberFunctor.obj f) ≫ h) hb).trans
          (Category.assoc _ _ _).symm)))

end PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing


namespace PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.nativeHasZeroObject
  HasZeroObject.zeroMorphismsOfZeroObject

/-- The original degree-minus-one connecting map retains the whole original exact pair. -/
theorem originalScalarCofiberInteger_mulExact_connecting_minusOne
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    Function.MulExact (originalScalarCofiberIntegerInclusion q f).hom
      (originalScalarCofiberConnecting q f).hom := by
  let e := originalIntegerMinusOneDegreeIso q
  let C := originalScalarCofiberFunctor.obj f
  let g := originalScalarCofiberConnectingPlusOne (q - 1) f
  have hn : e.hom.app f.right ≫ originalScalarCofiberIntegerInclusion ((q - 1) + 1) f =
      originalScalarCofiberIntegerInclusion q f ≫ e.hom.app C :=
    (e.hom.naturality
      (OriginalScalarCone.cofiberTarget PointedCGWH.EnrichedIntervalCylinder.functor
        (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
        (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) f.hom)).symm
  apply GrpCat.mulExact_of_iso_ladder
    (e.app f.right) (e.app C) (Iso.refl ((integerStablePiFunctor (q - 1)).obj f.left))
    (originalScalarCofiberIntegerInclusion q f) (originalScalarCofiberConnecting q f)
    (originalScalarCofiberIntegerInclusion ((q - 1) + 1) f) g
  · exact hn.symm
  · exact Category.comp_id _
  · exact originalScalarCofiberInteger_mulExact_connecting (q - 1) f

end PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

namespace PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.nativeHasZeroObject
  HasZeroObject.zeroMorphismsOfZeroObject

/-- The complete original unsuspended five-term scalar row retains its actual group carriers. -/
def originalScalarFiveTermObject (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    Fin 5 → GrpCat.{v}
  | 0 => (integerStablePiFunctor q).obj f.left
  | 1 => (integerStablePiFunctor q).obj f.right
  | 2 => (integerStablePiFunctor q).obj (originalScalarCofiberFunctor.obj f)
  | 3 => (integerStablePiFunctor q).obj (originalScalarSuspensionFunctor.obj f.left)
  | 4 => (integerStablePiFunctor q).obj (originalScalarSuspensionFunctor.obj f.right)

/-- The complete signed five-term scalar row retains all actual integer degrees and source objects. -/
def originalScalarSignedFiveTermObject (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    Fin 5 → GrpCat.{v}
  | 0 => (integerStablePiFunctor (q + 1)).obj (originalScalarCofiberFunctor.obj f)
  | 1 => (integerStablePiFunctor q).obj f.left
  | 2 => (integerStablePiFunctor q).obj f.right
  | 3 => (integerStablePiFunctor q).obj (originalScalarCofiberFunctor.obj f)
  | 4 => (integerStablePiFunctor (q - 1)).obj f.left

/-- The actual original input integer map occupies the first unsuspended row position. -/
def originalScalarRowMapOne (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    originalScalarFiveTermObject q f 0 ⟶ originalScalarFiveTermObject q f 1 :=
  (integerStablePiFunctor q).map f.hom

/-- The actual original cofiber inclusion occupies the second unsuspended row position. -/
def originalScalarRowMapTwo (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    originalScalarFiveTermObject q f 1 ⟶ originalScalarFiveTermObject q f 2 :=
  originalScalarCofiberIntegerInclusion q f

/-- The actual full original boundary occupies the third unsuspended row position. -/
def originalScalarRowMapThree (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    originalScalarFiveTermObject q f 2 ⟶ originalScalarFiveTermObject q f 3 :=
  originalScalarIntegerBoundary q f

/-- The actual original suspended input map occupies the fourth unsuspended row position. -/
def originalScalarRowMapFour (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    originalScalarFiveTermObject q f 3 ⟶ originalScalarFiveTermObject q f 4 :=
  (integerStablePiFunctor q).map (originalScalarSuspensionFunctor.map f.hom)

/-- Every original source integer map retains the first complete vertical row map. -/
def originalScalarRowVerticalOne (q : ℤ)
    {f g : Arrow PointedCGWH.SequentialSpectrum.{u, v}} (a : f ⟶ g) :
    originalScalarFiveTermObject q f 0 ⟶ originalScalarFiveTermObject q g 0 :=
  (integerStablePiFunctor q).map a.left

/-- Every original target integer map retains the second complete vertical row map. -/
def originalScalarRowVerticalTwo (q : ℤ)
    {f g : Arrow PointedCGWH.SequentialSpectrum.{u, v}} (a : f ⟶ g) :
    originalScalarFiveTermObject q f 1 ⟶ originalScalarFiveTermObject q g 1 :=
  (integerStablePiFunctor q).map a.right

/-- Every actual original cofiber map retains the third complete vertical row map. -/
def originalScalarRowVerticalThree (q : ℤ)
    {f g : Arrow PointedCGWH.SequentialSpectrum.{u, v}} (a : f ⟶ g) :
    originalScalarFiveTermObject q f 2 ⟶ originalScalarFiveTermObject q g 2 :=
  (integerStablePiFunctor q).map (originalScalarCofiberFunctor.map a)

/-- Every actual original suspended source map retains the fourth complete vertical row map. -/
def originalScalarRowVerticalFour (q : ℤ)
    {f g : Arrow PointedCGWH.SequentialSpectrum.{u, v}} (a : f ⟶ g) :
    originalScalarFiveTermObject q f 3 ⟶ originalScalarFiveTermObject q g 3 :=
  (integerStablePiFunctor q).map (originalScalarSuspensionFunctor.map a.left)

/-- Every actual original suspended target map retains the fifth complete vertical row map. -/
def originalScalarRowVerticalFive (q : ℤ)
    {f g : Arrow PointedCGWH.SequentialSpectrum.{u, v}} (a : f ⟶ g) :
    originalScalarFiveTermObject q f 4 ⟶ originalScalarFiveTermObject q g 4 :=
  (integerStablePiFunctor q).map (originalScalarSuspensionFunctor.map a.right)

/-- The whole first original row square is the actual input Arrow equation. -/
theorem originalScalarRowSquareOne (q : ℤ)
    {f g : Arrow PointedCGWH.SequentialSpectrum.{u, v}} (a : f ⟶ g) :
    originalScalarRowVerticalOne q a ≫ originalScalarRowMapOne q g =
      originalScalarRowMapOne q f ≫ originalScalarRowVerticalTwo q a := by
  let P := integerStablePiFunctor q
  let l : f.left ⟶ g.left := a.left
  let r : f.right ⟶ g.right := a.right
  let ff : f.left ⟶ f.right := f.hom
  let gg : g.left ⟶ g.right := g.hom
  have h : l ≫ gg = ff ≫ r := a.w
  have hmap : P.map (l ≫ gg) = P.map (ff ≫ r) := P.congr_map h
  change P.map l ≫ P.map gg = P.map ff ≫ P.map r
  exact (P.map_comp l gg).symm.trans (hmap.trans (P.map_comp ff r))

/-- The entire second original row square is the actual cofiber target naturality. -/
theorem originalScalarRowSquareTwo (q : ℤ)
    {f g : Arrow PointedCGWH.SequentialSpectrum.{u, v}} (a : f ⟶ g) :
    originalScalarRowVerticalTwo q a ≫ originalScalarRowMapTwo q g =
      originalScalarRowMapTwo q f ≫ originalScalarRowVerticalThree q a :=
  originalScalarCofiberIntegerInclusion_naturality q a

/-- The entire third original row square is the actual scalar boundary naturality. -/
theorem originalScalarRowSquareThree (q : ℤ)
    {f g : Arrow PointedCGWH.SequentialSpectrum.{u, v}} (a : f ⟶ g) :
    originalScalarRowVerticalThree q a ≫ originalScalarRowMapThree q g =
      originalScalarRowMapThree q f ≫ originalScalarRowVerticalFour q a :=
  originalScalarIntegerBoundary_naturality q a

/-- The full fourth original row square retains the actual scalar suspended input equation. -/
theorem originalScalarRowSquareFour (q : ℤ)
    {f g : Arrow PointedCGWH.SequentialSpectrum.{u, v}} (a : f ⟶ g) :
    originalScalarRowVerticalFour q a ≫ originalScalarRowMapFour q g =
      originalScalarRowMapFour q f ≫ originalScalarRowVerticalFive q a := by
  let P := integerStablePiFunctor q
  let S : PointedCGWH.SequentialSpectrum.{u, v} ⥤ PointedCGWH.SequentialSpectrum.{u, v} :=
    originalScalarSuspensionFunctor
  let l : f.left ⟶ g.left := a.left
  let r : f.right ⟶ g.right := a.right
  let ff : f.left ⟶ f.right := f.hom
  let gg : g.left ⟶ g.right := g.hom
  have h0 : l ≫ gg = ff ≫ r := a.w
  have hS : S.map (l ≫ gg) = S.map (ff ≫ r) := S.congr_map h0
  have h : S.map l ≫ S.map gg = S.map ff ≫ S.map r :=
    (S.map_comp l gg).symm.trans (hS.trans (S.map_comp ff r))
  let sl : S.obj f.left ⟶ S.obj g.left := S.map l
  let sr : S.obj f.right ⟶ S.obj g.right := S.map r
  let sf : S.obj f.left ⟶ S.obj f.right := S.map ff
  let sg : S.obj g.left ⟶ S.obj g.right := S.map gg
  have hp : P.map (sl ≫ sg) = P.map (sf ≫ sr) := P.congr_map h
  change P.map sl ≫ P.map sg = P.map sf ≫ P.map sr
  exact (P.map_comp sl sg).symm.trans (hp.trans (P.map_comp sf sr))

/-- The first original group exact pair is derived from the actual target kernel. -/
theorem originalScalarRowExactOne [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    Function.MulExact (originalScalarRowMapOne q f).hom (originalScalarRowMapTwo q f).hom :=
  originalScalarCofiberInteger_mulExact_target q f

/-- The second original exact pair is derived on the actual scalar cofiber. -/
theorem originalScalarRowExactTwo [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    Function.MulExact (originalScalarRowMapTwo q f).hom (originalScalarRowMapThree q f).hom :=
  originalScalarCofiberInteger_mulExact_cofiber q f

/-- The third original exact pair is derived from both original double-cone collapses. -/
theorem originalScalarRowExactThree [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    Function.MulExact (originalScalarRowMapThree q f).hom (originalScalarRowMapFour q f).hom :=
  originalScalarCofiberInteger_mulExact_scalar_source q f

/-- Every original Arrow square with genuine all-integer endpoint equivalences has
its actual scalar-cofiber map as an original all-integer equivalence. -/
theorem originalScalarCofiberMap_integer_isIso
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (q : ℤ)
    {f g : Arrow PointedCGWH.SequentialSpectrum.{u, v}} (a : f ⟶ g)
    (hL : IsIso ((integerStablePiFunctor q).map a.left))
    (hR : IsIso ((integerStablePiFunctor q).map a.right))
    (hSL : IsIso ((integerStablePiFunctor q).map (originalScalarSuspensionFunctor.map a.left)))
    (hSR : IsIso ((integerStablePiFunctor q).map (originalScalarSuspensionFunctor.map a.right))) :
    IsIso ((integerStablePiFunctor q).map (originalScalarCofiberFunctor.map a)) := by
  let _ : IsIso (originalScalarRowVerticalOne q a) := hL
  let _ : IsIso (originalScalarRowVerticalTwo q a) := hR
  let _ : IsIso (originalScalarRowVerticalFour q a) := hSL
  let _ : IsIso (originalScalarRowVerticalFive q a) := hSR
  exact CategoryTheory.originalGrpCat_fiveLemma
    (originalScalarRowMapOne q f) (originalScalarRowMapTwo q f)
    (originalScalarRowMapThree q f) (originalScalarRowMapFour q f)
    (originalScalarRowMapOne q g) (originalScalarRowMapTwo q g)
    (originalScalarRowMapThree q g) (originalScalarRowMapFour q g)
    (originalScalarRowVerticalOne q a) (originalScalarRowVerticalTwo q a)
    (originalScalarRowVerticalThree q a) (originalScalarRowVerticalFour q a)
    (originalScalarRowVerticalFive q a)
    (originalScalarRowSquareOne q a) (originalScalarRowSquareTwo q a)
    (originalScalarRowSquareThree q a) (originalScalarRowSquareFour q a)
    (originalScalarRowExactOne q f) (originalScalarRowExactTwo q f) (originalScalarRowExactThree q f)
    (originalScalarRowExactOne q g) (originalScalarRowExactTwo q g) (originalScalarRowExactThree q g)


/-- All original integer degrees retain the genuine actual cofiber-map equivalence. -/
theorem originalScalarCofiberMap_integerPiStarEquivalence
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    {f g : Arrow PointedCGWH.SequentialSpectrum.{u, v}} (a : f ⟶ g)
    (hL : integerPiStarEquivalences a.left) (hR : integerPiStarEquivalences a.right) :
    integerPiStarEquivalences (originalScalarCofiberFunctor.map a) := by
  apply (integerPiStarEquivalences_iff _).mpr
  intro q
  have hl := (integerPiStarEquivalences_iff _).mp hL
  have hr := (integerPiStarEquivalences_iff _).mp hR
  exact originalScalarCofiberMap_integer_isIso q a (hl q) (hr q)
    (originalScalarSuspension_integerPi_isIso q a.left (hl (q - 1)))
    (originalScalarSuspension_integerPi_isIso q a.right (hr (q - 1)))

end PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing


namespace PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.nativeHasZeroObject
  HasZeroObject.zeroMorphismsOfZeroObject


open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.nativeHasZeroObject
  HasZeroObject.zeroMorphismsOfZeroObject

/-- The actual signed row retains its complete original map at position one. -/
def originalScalarSignedRowMapOne (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    originalScalarSignedFiveTermObject q f 0 ⟶ originalScalarSignedFiveTermObject q f 1 :=
  originalScalarCofiberConnectingPlusOne q f

/-- The actual signed row retains its complete original map at position two. -/
def originalScalarSignedRowMapTwo (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    originalScalarSignedFiveTermObject q f 1 ⟶ originalScalarSignedFiveTermObject q f 2 :=
  (integerStablePiFunctor q).map f.hom

/-- The actual signed row retains its complete original map at position three. -/
def originalScalarSignedRowMapThree (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    originalScalarSignedFiveTermObject q f 2 ⟶ originalScalarSignedFiveTermObject q f 3 :=
  originalScalarCofiberIntegerInclusion q f

/-- The actual signed row retains its complete original map at position four. -/
def originalScalarSignedRowMapFour (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    originalScalarSignedFiveTermObject q f 3 ⟶ originalScalarSignedFiveTermObject q f 4 :=
  originalScalarCofiberConnecting q f

/-- The actual signed row retains its complete original vertical map at position one. -/
def originalScalarSignedRowVerticalOne (q : ℤ)
    {f g : Arrow PointedCGWH.SequentialSpectrum.{u, v}} (a : f ⟶ g) :
    originalScalarSignedFiveTermObject q f 0 ⟶ originalScalarSignedFiveTermObject q g 0 :=
  (integerStablePiFunctor (q + 1)).map (originalScalarCofiberFunctor.map a)

/-- The actual signed row retains its complete original vertical map at position two. -/
def originalScalarSignedRowVerticalTwo (q : ℤ)
    {f g : Arrow PointedCGWH.SequentialSpectrum.{u, v}} (a : f ⟶ g) :
    originalScalarSignedFiveTermObject q f 1 ⟶ originalScalarSignedFiveTermObject q g 1 :=
  (integerStablePiFunctor q).map a.left

/-- The actual signed row retains its complete original vertical map at position three. -/
def originalScalarSignedRowVerticalThree (q : ℤ)
    {f g : Arrow PointedCGWH.SequentialSpectrum.{u, v}} (a : f ⟶ g) :
    originalScalarSignedFiveTermObject q f 2 ⟶ originalScalarSignedFiveTermObject q g 2 :=
  (integerStablePiFunctor q).map a.right

/-- The actual signed row retains its complete original vertical map at position four. -/
def originalScalarSignedRowVerticalFour (q : ℤ)
    {f g : Arrow PointedCGWH.SequentialSpectrum.{u, v}} (a : f ⟶ g) :
    originalScalarSignedFiveTermObject q f 3 ⟶ originalScalarSignedFiveTermObject q g 3 :=
  (integerStablePiFunctor q).map (originalScalarCofiberFunctor.map a)

/-- The actual signed row retains its complete original vertical map at position five. -/
def originalScalarSignedRowVerticalFive (q : ℤ)
    {f g : Arrow PointedCGWH.SequentialSpectrum.{u, v}} (a : f ⟶ g) :
    originalScalarSignedFiveTermObject q f 4 ⟶ originalScalarSignedFiveTermObject q g 4 :=
  (integerStablePiFunctor (q - 1)).map a.left

/-- The original signed row square one retains every actual map. -/
theorem originalScalarSignedRowSquareOne (q : ℤ)
    {f g : Arrow PointedCGWH.SequentialSpectrum.{u, v}} (a : f ⟶ g) :
    originalScalarSignedRowVerticalOne q a ≫ originalScalarSignedRowMapOne q g =
      originalScalarSignedRowMapOne q f ≫ originalScalarSignedRowVerticalTwo q a :=
  originalScalarCofiberConnectingPlusOne_naturality q a

/-- The original signed row square two retains every actual map. -/
theorem originalScalarSignedRowSquareTwo (q : ℤ)
    {f g : Arrow PointedCGWH.SequentialSpectrum.{u, v}} (a : f ⟶ g) :
    originalScalarSignedRowVerticalTwo q a ≫ originalScalarSignedRowMapTwo q g =
      originalScalarSignedRowMapTwo q f ≫ originalScalarSignedRowVerticalThree q a :=
  by
    let P := integerStablePiFunctor q
    let l : f.left ⟶ g.left := a.left
    let r : f.right ⟶ g.right := a.right
    let ff : f.left ⟶ f.right := f.hom
    let gg : g.left ⟶ g.right := g.hom
    have h : l ≫ gg = ff ≫ r := a.w
    have hmap : P.map (l ≫ gg) = P.map (ff ≫ r) := P.congr_map h
    change P.map l ≫ P.map gg = P.map ff ≫ P.map r
    exact (P.map_comp l gg).symm.trans (hmap.trans (P.map_comp ff r))

/-- The original signed row square three retains every actual map. -/
theorem originalScalarSignedRowSquareThree (q : ℤ)
    {f g : Arrow PointedCGWH.SequentialSpectrum.{u, v}} (a : f ⟶ g) :
    originalScalarSignedRowVerticalThree q a ≫ originalScalarSignedRowMapThree q g =
      originalScalarSignedRowMapThree q f ≫ originalScalarSignedRowVerticalFour q a :=
  originalScalarCofiberIntegerInclusion_naturality q a

/-- The original signed row square four retains every actual map. -/
theorem originalScalarSignedRowSquareFour (q : ℤ)
    {f g : Arrow PointedCGWH.SequentialSpectrum.{u, v}} (a : f ⟶ g) :
    originalScalarSignedRowVerticalFour q a ≫ originalScalarSignedRowMapFour q g =
      originalScalarSignedRowMapFour q f ≫ originalScalarSignedRowVerticalFive q a :=
  originalScalarCofiberConnecting_naturality q a

/-- The original signed row exact pair one is genuinely derived from the actual scalar cofiber. -/
theorem originalScalarSignedRowExactOne [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    Function.MulExact (originalScalarSignedRowMapOne q f).hom
      (originalScalarSignedRowMapTwo q f).hom :=
  originalScalarCofiberInteger_mulExact_source q f

/-- The original signed row exact pair two is genuinely derived from the actual scalar cofiber. -/
theorem originalScalarSignedRowExactTwo [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    Function.MulExact (originalScalarSignedRowMapTwo q f).hom
      (originalScalarSignedRowMapThree q f).hom :=
  originalScalarCofiberInteger_mulExact_target q f

/-- The original signed row exact pair three is genuinely derived from the actual scalar cofiber. -/
theorem originalScalarSignedRowExactThree [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (q : ℤ) (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    Function.MulExact (originalScalarSignedRowMapThree q f).hom
      (originalScalarSignedRowMapFour q f).hom :=
  originalScalarCofiberInteger_mulExact_connecting_minusOne q f



/-- The second genuine group five lemma recovers each original target integer map. -/
theorem originalScalarTarget_integer_isIso
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    (q : ℤ)
    {f g : Arrow PointedCGWH.SequentialSpectrum.{u, v}} (a : f ⟶ g)
    (hL : IsIso ((integerStablePiFunctor q).map a.left))
    (hC : IsIso ((integerStablePiFunctor q).map (originalScalarCofiberFunctor.map a)))
    (hCplus : IsIso ((integerStablePiFunctor (q + 1)).map (originalScalarCofiberFunctor.map a)))
    (hLminus : IsIso ((integerStablePiFunctor (q - 1)).map a.left)) :
    IsIso ((integerStablePiFunctor q).map a.right) := by
  let _ : IsIso (originalScalarSignedRowVerticalOne q a) := hCplus
  let _ : IsIso (originalScalarSignedRowVerticalTwo q a) := hL
  let _ : IsIso (originalScalarSignedRowVerticalFour q a) := hC
  let _ : IsIso (originalScalarSignedRowVerticalFive q a) := hLminus
  exact CategoryTheory.originalGrpCat_fiveLemma
    (originalScalarSignedRowMapOne q f) (originalScalarSignedRowMapTwo q f)
    (originalScalarSignedRowMapThree q f) (originalScalarSignedRowMapFour q f)
    (originalScalarSignedRowMapOne q g) (originalScalarSignedRowMapTwo q g)
    (originalScalarSignedRowMapThree q g) (originalScalarSignedRowMapFour q g)
    (originalScalarSignedRowVerticalOne q a) (originalScalarSignedRowVerticalTwo q a)
    (originalScalarSignedRowVerticalThree q a) (originalScalarSignedRowVerticalFour q a)
    (originalScalarSignedRowVerticalFive q a)
    (originalScalarSignedRowSquareOne q a) (originalScalarSignedRowSquareTwo q a)
    (originalScalarSignedRowSquareThree q a) (originalScalarSignedRowSquareFour q a)
    (originalScalarSignedRowExactOne q f) (originalScalarSignedRowExactTwo q f)
    (originalScalarSignedRowExactThree q f)
    (originalScalarSignedRowExactOne q g) (originalScalarSignedRowExactTwo q g)
    (originalScalarSignedRowExactThree q g)


/-- All original integer degrees recover the actual target map from source and cofiber tests. -/
theorem originalScalarTarget_integerPiStarEquivalence_of_source_cofiber
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    {f g : Arrow PointedCGWH.SequentialSpectrum.{u, v}} (a : f ⟶ g)
    (hL : integerPiStarEquivalences a.left)
    (hC : integerPiStarEquivalences (originalScalarCofiberFunctor.map a)) :
    integerPiStarEquivalences a.right := by
  apply (integerPiStarEquivalences_iff _).mpr
  intro q
  have hl := (integerPiStarEquivalences_iff _).mp hL
  have hc := (integerPiStarEquivalences_iff _).mp hC
  exact originalScalarTarget_integer_isIso q a (hl q) (hc q) (hc (q + 1)) (hl (q - 1))

end PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing


namespace PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing

open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.nativeHasZeroObject
  HasZeroObject.zeroMorphismsOfZeroObject

/-- The actual full raw-pi HEP gluing statement retains both caller pushouts and every original map. -/
theorem originalRawPiHEPpushoutGluing
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    {A X Z P A' X' Z' P' : PointedCGWH.SequentialSpectrum.{u, v}}
    (i : A ⟶ X) (z : A ⟶ Z) (kX : X ⟶ P) (kZ : Z ⟶ P)
    (i' : A' ⟶ X') (z' : A' ⟶ Z') (kX' : X' ⟶ P') (kZ' : Z' ⟶ P')
    (sq : IsPushout i z kX kZ) (sq' : IsPushout i' z' kX' kZ')
    (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property i)
    (hi' : PointedCGWH.EnrichedBasedHomotopyExtension.property i')
    (a : A ⟶ A') (b : X ⟶ X') (c : Z ⟶ Z') (d : P ⟶ P')
    (hI : a ≫ i' = i ≫ b) (hZ : a ≫ z' = z ≫ c)
    (hX : b ≫ kX' = kX ≫ d) (hP : c ≫ kZ' = kZ ≫ d)
    (ha : integerPiStarEquivalences a) (hb : integerPiStarEquivalences b)
    (hc : integerPiStarEquivalences c) : integerPiStarEquivalences d := by
  let f : Arrow PointedCGWH.SequentialSpectrum.{u, v} := Arrow.mk i
  let f' : Arrow PointedCGWH.SequentialSpectrum.{u, v} := Arrow.mk i'
  let g : Arrow PointedCGWH.SequentialSpectrum.{u, v} := Arrow.mk kZ
  let g' : Arrow PointedCGWH.SequentialSpectrum.{u, v} := Arrow.mk kZ'
  let af : f ⟶ f' := Arrow.homMk a b hI
  let ag : g ⟶ g' := Arrow.homMk c d hP
  let t : f ⟶ g := Arrow.homMk z kX sq.w.symm
  let t' : f' ⟶ g' := Arrow.homMk z' kX' sq'.w.symm
  have hcf : integerPiStarEquivalences (originalScalarCofiberFunctor.map af) :=
    originalScalarCofiberMap_integerPiStarEquivalence af ha hb
  have hwT : WeakEquivalence (originalScalarCofiberFunctor.map t) :=
    originalScalarCofiberMap_weakEquivalence_of_isPushout i hi z kX kZ sq
  have hwT' : WeakEquivalence (originalScalarCofiberFunctor.map t') :=
    originalScalarCofiberMap_weakEquivalence_of_isPushout i' hi' z' kX' kZ' sq'
  have hSquare : originalScalarCofiberFunctor.map af ≫ originalScalarCofiberFunctor.map t' =
      originalScalarCofiberFunctor.map t ≫ originalScalarCofiberFunctor.map ag :=
    OriginalScalarCone.originalCallerPushoutCofiber_square
      PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1)
      i z kX kZ i' z' kX' kZ' sq sq' a b c d hI hZ hX hP
  have hcg : integerPiStarEquivalences (originalScalarCofiberFunctor.map ag) := by
    rw [integerPiStarEquivalences_iff] at hcf ⊢
    intro q
    let Q := integerStablePiFunctor q
    let _ : WeakEquivalence (originalScalarCofiberFunctor.map t) := hwT
    let _ : WeakEquivalence (originalScalarCofiberFunctor.map t') := hwT'
    let _ : IsIso (Q.map (originalScalarCofiberFunctor.map t)) :=
      PointedCGWH.SequentialSpectrum.MappingTelescope.StageIntegerStablePiGeometry.integerStablePiLevelWeak_isIso
        q _ (mem_weakEquivalences _)
    let _ : IsIso (Q.map (originalScalarCofiberFunctor.map t')) :=
      PointedCGWH.SequentialSpectrum.MappingTelescope.StageIntegerStablePiGeometry.integerStablePiLevelWeak_isIso
        q _ (mem_weakEquivalences _)
    let _ : IsIso (Q.map (originalScalarCofiberFunctor.map af)) := hcf q
    let mf : Q.obj (originalScalarCofiberFunctor.obj f) ⟶
        Q.obj (originalScalarCofiberFunctor.obj f') := Q.map (originalScalarCofiberFunctor.map af)
    let mt : Q.obj (originalScalarCofiberFunctor.obj f) ⟶
        Q.obj (originalScalarCofiberFunctor.obj g) := Q.map (originalScalarCofiberFunctor.map t)
    let mt' : Q.obj (originalScalarCofiberFunctor.obj f') ⟶
        Q.obj (originalScalarCofiberFunctor.obj g') := Q.map (originalScalarCofiberFunctor.map t')
    let mg : Q.obj (originalScalarCofiberFunctor.obj g) ⟶
        Q.obj (originalScalarCofiberFunctor.obj g') := Q.map (originalScalarCofiberFunctor.map ag)
    have h : mf ≫ mt' = mt ≫ mg :=
      (Q.map_comp _ _).symm.trans ((Q.congr_map hSquare).trans (Q.map_comp _ _))
    let _ : IsIso (mf ≫ mt') := inferInstance
    let _ : IsIso (mt ≫ mg) := h ▸ inferInstanceAs (IsIso (mf ≫ mt'))
    exact IsIso.of_isIso_comp_left mt mg
  exact originalScalarTarget_integerPiStarEquivalence_of_source_cofiber ag hc hcg

end PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing
