/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.BGLScalarCarrierMap
public import MathlibExt.KTheory.Ring.StableGeneralLinear.IndependentPlusNativePresentation
public import MathlibExt.AlgebraicTopology.PlusConstruction.PointRelativeMapping

/-!
# Point-relative plus extension of the actual mixed-ring source map

A unital homomorphism between independent ring universes supplies the actual
scalar BGL map. Its derived subgroup-image law extends this map from the
existing native point model of the original source plus to the original
lifted target plus. The whole source triangle and both point-relative
uniqueness families are conclusions, not inputs.
-/

noncomputable section

open CategoryTheory HomotopicalAlgebra
open scoped ContinuousMap TopCat.modelCategory

universe uR uS uCarrier uProbe

namespace AlgebraicKTheory.StableGL

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- The actual scalar source map has a derived based extension between the original plus targets. -/
public theorem independentBGLScalarNativeExtension_exists (f : R →+* S) :
    ∃ F : (independentBGLCellNativePointModelOfRing.{uR, max uS uCarrier, uProbe} R).space.toTop ⟶
        independentBGLCellTargetLift.{uS, max uR uCarrier} S,
      F (independentBGLCellNativePointModelOfRing.{uR, max uS uCarrier, uProbe} R).point =
          independentBGLCellPointLift.{uS, max uR uCarrier} S ∧
      Nonempty (ContinuousMap.HomotopyRel
        (independentBGLCellNativeInclusion.{uR, max uS uCarrier, uProbe} R ≫ F).hom
        (ordinaryBGLScalarCarrierMap.{uR, uS, uCarrier} f ≫
          independentBGLCellInclusionLift.{uS, max uR uCarrier} S).hom
        {independentBGLSourcePointLift.{uR, max uS uCarrier} R}) ∧
      ∀ G : (independentBGLCellNativePointModelOfRing.{uR, max uS uCarrier, uProbe} R).space.toTop ⟶
          independentBGLCellTargetLift.{uS, max uR uCarrier} S,
        Nonempty (ContinuousMap.HomotopyRel
          (independentBGLCellNativeInclusion.{uR, max uS uCarrier, uProbe} R ≫ G).hom
          (ordinaryBGLScalarCarrierMap.{uR, uS, uCarrier} f ≫
            independentBGLCellInclusionLift.{uS, max uR uCarrier} S).hom
          {independentBGLSourcePointLift.{uR, max uS uCarrier} R}) →
        Nonempty (ContinuousMap.HomotopyRel F.hom G.hom
          {(independentBGLCellNativePointModelOfRing.{uR, max uS uCarrier, uProbe} R).point}) ∧
        Nonempty (ContinuousMap.HomotopyRel G.hom F.hom
          {(independentBGLCellNativePointModelOfRing.{uR, max uS uCarrier, uProbe} R).point}) := by
  let X := independentBGLSourceLift.{uR, max uS uCarrier} R
  let x := independentBGLSourcePointLift.{uR, max uS uCarrier} R
  let M := independentBGLCellNativePointModelOfRing.{uR, max uS uCarrier, uProbe} R
  let A := M.space.toTop
  letI : PathConnectedSpace M.space :=
    independentBGLCellNativePointModel_pathConnected.{uR, max uS uCarrier, uProbe} R
  letI : Cofibration (TopCat.const x : TopCat.of PUnit.{max uR uS uCarrier + 1} ⟶ X) :=
    independentBGLSourceLift_pointCofibration.{uR, max uS uCarrier} R
  letI : Cofibration (TopCat.const M.point : TopCat.of PUnit.{max uR uS uCarrier + 1} ⟶ A) :=
    M.pointCofibration
  have hCWX : ∃ C : TopCat.{max uR uS uCarrier}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ X) :=
    independentBGLSourceLift_cwType.{uR, max uS uCarrier} R
  have hCWA : ∃ C : TopCat.{max uR uS uCarrier}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ A) :=
    ⟨A, M.isT2, M.cwComplex, ⟨ContinuousMap.HomotopyEquiv.refl A⟩⟩
  exact TopCat.IsPlusConstructionAt.exists_point_relative_subgroup_preserving_extension_of_cwType
    hCWX hCWA
    (independentBGLCellNativeInclusion_isPlus.{uR, max uS uCarrier, uProbe} R)
    (independentBGLCellInclusionLift_isPlus.{uS, max uR uCarrier} S)
    (ordinaryBGLScalarCarrierMap.{uR, uS, uCarrier} f)
    (ordinaryBGLScalarCarrierMap_point.{uR, uS, uCarrier} f)
    (ordinaryBGLScalarCarrierMap_preservesPlusSubgroup.{uR, uS, uCarrier} f)

/-- An internally constructed plus extension retains its actual point, source triangle and
  uniqueness. -/
public structure IndependentBGLScalarNativeExtensionData (f : R →+* S) where
  /-- The actual map from the source native point model to the original lifted cell target. -/
  map : (independentBGLCellNativePointModelOfRing.{uR, max uS uCarrier, uProbe} R).space.toTop ⟶
    independentBGLCellTargetLift.{uS, max uR uCarrier} S
  /-- Its actual marked point is the lifted original target point. -/
  point : map (independentBGLCellNativePointModelOfRing.{uR, max uS uCarrier, uProbe} R).point =
    independentBGLCellPointLift.{uS, max uR uCarrier} S
  /-- The whole source-point-relative triangle is derived from the literal scalar source map. -/
  triangle : ContinuousMap.HomotopyRel
    (independentBGLCellNativeInclusion.{uR, max uS uCarrier, uProbe} R ≫ map).hom
    (ordinaryBGLScalarCarrierMap.{uR, uS, uCarrier} f ≫
      independentBGLCellInclusionLift.{uS, max uR uCarrier} S).hom
    {independentBGLSourcePointLift.{uR, max uS uCarrier} R}
  /-- Any extension with this same source triangle has both whole point-relative comparison
    families. -/
  unique : ∀ G : (independentBGLCellNativePointModelOfRing.{uR, max uS uCarrier, uProbe}
      R).space.toTop ⟶
      independentBGLCellTargetLift.{uS, max uR uCarrier} S,
    Nonempty (ContinuousMap.HomotopyRel
      (independentBGLCellNativeInclusion.{uR, max uS uCarrier, uProbe} R ≫ G).hom
      (ordinaryBGLScalarCarrierMap.{uR, uS, uCarrier} f ≫
        independentBGLCellInclusionLift.{uS, max uR uCarrier} S).hom
      {independentBGLSourcePointLift.{uR, max uS uCarrier} R}) →
    Nonempty (ContinuousMap.HomotopyRel map.hom G.hom
      {(independentBGLCellNativePointModelOfRing.{uR, max uS uCarrier, uProbe} R).point}) ∧
    Nonempty (ContinuousMap.HomotopyRel G.hom map.hom
      {(independentBGLCellNativePointModelOfRing.{uR, max uS uCarrier, uProbe} R).point})

/-- A ring homomorphism alone supplies all of this actual extension data. -/
public theorem independentBGLScalarNativeExtensionData_nonempty (f : R →+* S) :
    Nonempty (IndependentBGLScalarNativeExtensionData.{uR, uS, uCarrier, uProbe} f) := by
  obtain ⟨F, hF, hTriangle, hUnique⟩ :=
    independentBGLScalarNativeExtension_exists.{uR, uS, uCarrier, uProbe} f
  exact ⟨{ map := F, point := hF, triangle := hTriangle.some, unique := hUnique }⟩

/-- Select a proven extension together with its actual source triangle and both uniqueness families.
-/
public def independentBGLScalarNativeExtensionDataOfHom (f : R →+* S) :
    IndependentBGLScalarNativeExtensionData.{uR, uS, uCarrier, uProbe} f :=
  Classical.choice (independentBGLScalarNativeExtensionData_nonempty.{uR, uS, uCarrier, uProbe} f)

end AlgebraicKTheory.StableGL

end
