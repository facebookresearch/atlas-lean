/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.IndependentPlusUniverseLift
public import MathlibExt.AlgebraicTopology.PlusConstruction.HomotopyEquivSquare
public import MathlibExt.Topology.Category.TopCat.RealizedPointCofibration
public import Mathlib.Topology.Homotopy.Path

/-!
# The original plus inclusion in its actual native point model

The native space is the existing independent-probe realization of the
original cell target. Its inverse and both point-relative families are
internally derived. Composing the original inclusion with that inverse
retains the original subgroup and all integer local coefficients.
-/

noncomputable section

open CategoryTheory HomotopicalAlgebra AlgebraicTopology
open scoped ContinuousMap Simplicial TopCat.modelCategory

universe uR uCarrier uProbe

namespace AlgebraicKTheory.StableGL

/-- The literal lifted original BGL vertex is a cofibrant marked point. -/
public theorem independentBGLSourceLift_pointCofibration (R : Type uR) [Ring R] :
    Cofibration (TopCat.const (independentBGLSourcePointLift.{uR, uCarrier} R) :
      TopCat.of PUnit.{max uR uCarrier + 1} ⟶ independentBGLSourceLift.{uR, uCarrier} R) := by
  let K := SSet.uliftFunctor.{uCarrier, uR}.obj (classifyingNerve R)
  let C := SSet.toTop.obj K
  let e : C ≅ independentBGLSourceLift.{uR, uCarrier} R :=
    SSet.toTopULiftIso.{uR, uCarrier}.app (classifyingNerve R)
  let v : C := SSet.realizedVertex (X := K) (ULift.up (classifyingVertex R))
  have he : e.hom v = independentBGLSourcePointLift.{uR, uCarrier} R :=
    SSet.toTopULiftIso_hom_realizedVertex.{uR, uCarrier}
      (classifyingNerve R) (classifyingVertex R)
  let : Cofibration (TopCat.const v : TopCat.of PUnit.{max uR uCarrier + 1} ⟶ C) :=
    SSet.realizedVertex_pointMap_cofibration K (ULift.up (classifyingVertex R))
  have hPoint :
      (TopCat.const (independentBGLSourcePointLift.{uR, uCarrier} R) :
        TopCat.of PUnit.{max uR uCarrier + 1} ⟶ independentBGLSourceLift.{uR, uCarrier} R) =
      TopCat.const v ≫ e.hom := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro a
    exact he.symm
  rw [hPoint]
  infer_instance

/-- The same lifted source has the actual CW realization of its lifted nerve. -/
public theorem independentBGLSourceLift_cwType (R : Type uR) [Ring R] :
    ∃ C : TopCat.{max uR uCarrier}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C),
        Nonempty (C ≃ₕ independentBGLSourceLift.{uR, uCarrier} R) := by
  let K := SSet.uliftFunctor.{uCarrier, uR}.obj (classifyingNerve R)
  let C := SSet.toTop.obj K
  let e : C ≅ independentBGLSourceLift.{uR, uCarrier} R :=
    SSet.toTopULiftIso.{uR, uCarrier}.app (classifyingNerve R)
  exact ⟨C, SSet.realization_t2Space K, SSet.instCWComplexToTop K,
    ⟨(TopCat.homeoOfIso e).toHomotopyEquiv⟩⟩

private theorem nativePointModel_pathConnected_computed (R : Type uR) [Ring R] :
    PathConnectedSpace
      (independentBGLCellNativePointModelOfRing.{uR, uCarrier, uProbe} R).space := by
  let M := independentBGLCellNativePointModelOfRing.{uR, uCarrier, uProbe} R
  let L := M.leftFamily.toHomotopy
  let : PathConnectedSpace (independentBGLCellTargetLift.{uR, uCarrier} R) :=
    independentBGLCellTargetLift_pathConnected.{uR, uCarrier} R
  refine ⟨⟨M.point⟩, ?_⟩
  intro a b
  exact ⟨(L.evalAt a).symm.trans
    (((PathConnectedSpace.somePath (M.equiv.toFun a) (M.equiv.toFun b)).map
      M.equiv.invFun.continuous).trans (L.evalAt b))⟩

/-- Connectedness of the actual native point model is derived from its stored inverse family. -/
public theorem independentBGLCellNativePointModel_pathConnected (R : Type uR) [Ring R] :
    PathConnectedSpace (independentBGLCellNativePointModelOfRing.{uR, uCarrier, uProbe} R).space :=
  nativePointModel_pathConnected_computed.{uR, uCarrier, uProbe} R

/-- The actual original inclusion followed by the derived native-model inverse. -/
public def independentBGLCellNativeInclusion (R : Type uR) [Ring R] :
    independentBGLSourceLift.{uR, uCarrier} R ⟶
      (independentBGLCellNativePointModelOfRing.{uR, uCarrier, uProbe} R).space.toTop :=
  TopCat.ofHom
    ((independentBGLCellNativePointModelOfRing.{uR, uCarrier, uProbe} R).equiv.invFun.comp
      (independentBGLCellInclusionLift.{uR, uCarrier} R).hom)

private theorem nativeInclusion_point_computed (R : Type uR) [Ring R] :
    independentBGLCellNativeInclusion.{uR, uCarrier, uProbe} R
      (independentBGLSourcePointLift.{uR, uCarrier} R) =
        (independentBGLCellNativePointModelOfRing.{uR, uCarrier, uProbe} R).point := by
  let M := independentBGLCellNativePointModelOfRing.{uR, uCarrier, uProbe} R
  change M.equiv.invFun ((independentBGLCellInclusionLift.{uR, uCarrier} R)
    (independentBGLSourcePointLift.{uR, uCarrier} R)) = M.point
  rw [independentBGLCellInclusionLift_point.{uR, uCarrier} R]
  exact M.backwardPoint

/-- The native inverse retains the original lifted marked source point. -/
public theorem independentBGLCellNativeInclusion_point (R : Type uR) [Ring R] :
    independentBGLCellNativeInclusion.{uR, uCarrier, uProbe} R
      (independentBGLSourcePointLift.{uR, uCarrier} R) =
        (independentBGLCellNativePointModelOfRing.{uR, uCarrier, uProbe} R).point :=
  nativeInclusion_point_computed.{uR, uCarrier, uProbe} R

/-- The whole actual target inverse family gives the source-point-relative inclusion triangle. -/
public def independentBGLCellNativeInclusionSourceTriangle (R : Type uR) [Ring R] :
    ContinuousMap.HomotopyRel
      (independentBGLCellNativeInclusion.{uR, uCarrier, uProbe} R ≫
        TopCat.ofHom
          (independentBGLCellNativePointModelOfRing.{uR, uCarrier, uProbe} R).equiv.toFun).hom
      (independentBGLCellInclusionLift.{uR, uCarrier} R).hom
      {independentBGLSourcePointLift.{uR, uCarrier} R} := by
  let M := independentBGLCellNativePointModelOfRing.{uR, uCarrier, uProbe} R
  let H := M.rightFamily.precomposePointRelative
    (independentBGLCellInclusionLift.{uR, uCarrier} R).hom
    (independentBGLSourcePointLift.{uR, uCarrier} R)
    (independentBGLCellInclusionLift_point.{uR, uCarrier} R)
  exact H.cast (by apply ContinuousMap.ext; intro x; rfl)
    (by apply ContinuousMap.ext; intro x; rfl)

/-- The same native inclusion is a plus map for the exact original transported subgroup. -/
public theorem independentBGLCellNativeInclusion_isPlus (R : Type uR) [Ring R] :
    TopCat.IsPlusConstructionAt (independentBGLCellNativeInclusion.{uR, uCarrier, uProbe} R)
      (independentBGLSourcePointLift.{uR, uCarrier} R)
      (independentBGLCellNativePointModelOfRing.{uR, uCarrier, uProbe} R).point
      (independentBGLCellNativeInclusion_point.{uR, uCarrier, uProbe} R)
      (BGLPlusSubgroupLift.{uR, uCarrier} R) := by
  let X := independentBGLSourceLift.{uR, uCarrier} R
  let x := independentBGLSourcePointLift.{uR, uCarrier} R
  let M := independentBGLCellNativePointModelOfRing.{uR, uCarrier, uProbe} R
  let i := independentBGLCellInclusionLift.{uR, uCarrier} R
  let P := BGLPlusSubgroupLift.{uR, uCarrier} R
  let : PathConnectedSpace M.space :=
    independentBGLCellNativePointModel_pathConnected.{uR, uCarrier, uProbe} R
  let : PathConnectedSpace (independentBGLCellTargetLift.{uR, uCarrier} R) :=
    independentBGLCellTargetLift_pathConnected.{uR, uCarrier} R
  let H := (independentBGLCellNativeInclusionSourceTriangle.{uR, uCarrier, uProbe}
      R).toHomotopy.cast
    rfl (congrArg TopCat.Hom.hom (Category.id_comp i).symm)
  obtain ⟨hN, hPerfect, hPlus⟩ :=
    TopCat.IsPlusConstructionAt.of_sourceIso_targetEquiv_homotopySquare
      (Iso.refl X) M.equiv H x M.point x (independentBGLCellPointLift.{uR, uCarrier} R)
      (independentBGLCellNativeInclusion_point.{uR, uCarrier, uProbe} R)
      rfl M.forwardPoint (independentBGLCellInclusionLift_point.{uR, uCarrier} R)
      P (independentBGLCellInclusionLift_isPlus.{uR, uCarrier} R)
  let Q := P.comap (FundamentalGroup.mapOfEq (Iso.refl X).hom.hom (show (Iso.refl X).hom x = x from
      rfl))
  let : Q.Normal := hN
  let : Group.IsPerfect Q := hPerfect
  have hIdMap :
      FundamentalGroup.mapOfEq (ContinuousMap.id (independentBGLSourceLift.{uR, uCarrier} R))
        (rfl : (ContinuousMap.id (independentBGLSourceLift.{uR, uCarrier} R))
          (independentBGLSourcePointLift.{uR, uCarrier} R) =
            independentBGLSourcePointLift.{uR, uCarrier} R) =
      MonoidHom.id (FundamentalGroup (independentBGLSourceLift.{uR, uCarrier} R)
        (independentBGLSourcePointLift.{uR, uCarrier} R)) :=
    FundamentalGroup.mapOfEq_id (independentBGLSourcePointLift.{uR, uCarrier} R) rfl
  have hIdHom : (Iso.refl (independentBGLSourceLift.{uR, uCarrier} R)).hom.hom =
      ContinuousMap.id (independentBGLSourceLift.{uR, uCarrier} R) := TopCat.hom_id
  have hIsoMap :
      FundamentalGroup.mapOfEq (Iso.refl (independentBGLSourceLift.{uR, uCarrier} R)).hom.hom
        (rfl : (Iso.refl (independentBGLSourceLift.{uR, uCarrier} R)).hom
          (independentBGLSourcePointLift.{uR, uCarrier} R) =
            independentBGLSourcePointLift.{uR, uCarrier} R) =
      MonoidHom.id (FundamentalGroup (independentBGLSourceLift.{uR, uCarrier} R)
        (independentBGLSourcePointLift.{uR, uCarrier} R)) :=
    (FundamentalGroup.mapOfEq_congr hIdHom rfl rfl).trans hIdMap
  have hQ : Q = P :=
    (congrArg (fun f : FundamentalGroup (independentBGLSourceLift.{uR, uCarrier} R)
        (independentBGLSourcePointLift.{uR, uCarrier} R) →*
        FundamentalGroup (independentBGLSourceLift.{uR, uCarrier} R)
          (independentBGLSourcePointLift.{uR, uCarrier} R) =>
      (BGLPlusSubgroupLift.{uR, uCarrier} R).comap f) hIsoMap).trans
        (Subgroup.comap_id (BGLPlusSubgroupLift.{uR, uCarrier} R))
  exact { acyclic := hPlus.acyclic, kernel_eq := hPlus.kernel_eq.trans hQ }


private theorem nativeInclusion_apply_computed (R : Type uR) [Ring R]
    (x : independentBGLSourceLift.{uR, uCarrier} R) :
    independentBGLCellNativeInclusion.{uR, uCarrier, uProbe} R x =
      (independentBGLCellNativePointModelOfRing.{uR, uCarrier, uProbe} R).equiv.invFun
        (independentBGLCellInclusionLift.{uR, uCarrier} R x) := rfl

/-- The actual native inclusion is computed on every original lifted source value. -/
public theorem independentBGLCellNativeInclusion_apply (R : Type uR) [Ring R]
    (x : independentBGLSourceLift.{uR, uCarrier} R) :
    independentBGLCellNativeInclusion.{uR, uCarrier, uProbe} R x =
      (independentBGLCellNativePointModelOfRing.{uR, uCarrier, uProbe} R).equiv.invFun
        (independentBGLCellInclusionLift.{uR, uCarrier} R x) :=
  nativeInclusion_apply_computed.{uR, uCarrier, uProbe} R x

end AlgebraicKTheory.StableGL

end
