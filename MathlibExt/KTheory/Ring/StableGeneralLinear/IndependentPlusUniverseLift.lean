/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.IndependentPlusPoint
public import MathlibExt.AlgebraicTopology.PlusConstruction.CarrierLift
public import MathlibExt.Topology.CWComplex.UniverseLift
public import MathlibExt.Topology.CWComplex.NativeSingularModel
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationUniverseLift
public import MathlibExt.AlgebraicTopology.SingularHomology.UniverseLiftIntegral
public import MathlibExt.Topology.Category.TopCat.HomotopyFiberUniverseLift
public import MathlibExt.AlgebraicTopology.PlusConstruction.HomologyEquivalence
public import MathlibExt.Topology.Category.TopCat.HomotopyFiberFundamentalSurjectivity
public import Mathlib.Topology.Category.TopCat.ULift
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The same independent BGL cell plus in a larger native carrier

The target is the canonical lift of the original ring-only two/three-cell
construction. The ring, subgroup and original cells are unchanged. The
plain carrier depends only on the ring universe and the requested carrier
universe; a native CW model uses its separate probe universe.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology HomotopicalAlgebra
open scoped ContinuousMap Simplicial TopCat.modelCategory

universe uR uCarrier uProbe

namespace AlgebraicKTheory.StableGL

private local instance originalBGLPathConnected (R : Type uR) [Ring R] :
    PathConnectedSpace (ordinaryBGL R) :=
  CategoryTheory.groupClassifyingOrdinary_pathConnected (StableGL R)

private local instance originalBGLHausdorff (R : Type uR) [Ring R] :
    T2Space (ordinaryBGL R) := SSet.realization_t2Space (classifyingNerve R)

private local instance originalBGLClassicalCW (R : Type uR) [Ring R] :
    Topology.CWComplex (Set.univ : Set (ordinaryBGL R)) :=
  SSet.instCWComplexToTop (classifyingNerve R)

attribute [local instance] AlgebraicKTheory.StableGL.ordinaryBGLPathConnected

/-- The actual ordinary BGL source in the requested carrier universe. -/
public abbrev independentBGLSourceLift (R : Type uR) [Ring R] :
    TopCat.{max uR uCarrier} :=
  TopCat.uliftFunctor.{uCarrier, uR}.obj (ordinaryBGL R)

/-- The canonical carrier lift of the SAME ring-only cell-built plus target. -/
public abbrev independentBGLCellTargetLift (R : Type uR) [Ring R] :
    TopCat.{max uR uCarrier} :=
  TopCat.uliftFunctor.{uCarrier, uR}.obj (independentBGLCellTarget R)

/-- The original two/three-cell inclusion transported by the actual lift functor. -/
public abbrev independentBGLCellInclusionLift (R : Type uR) [Ring R] :
    independentBGLSourceLift.{uR, uCarrier} R ⟶
      independentBGLCellTargetLift.{uR, uCarrier} R :=
  TopCat.uliftFunctor.{uCarrier, uR}.map (independentBGLCellInclusion R)

/-- The lifted original BGL vertex. -/
public abbrev independentBGLSourcePointLift (R : Type uR) [Ring R] :
    independentBGLSourceLift.{uR, uCarrier} R :=
  ULift.up (ordinaryBGLBasepoint R)

/-- The lifted original point of the actual independent cell target. -/
public abbrev independentBGLCellPointLift (R : Type uR) [Ring R] :
    independentBGLCellTargetLift.{uR, uCarrier} R :=
  ULift.up (independentBGLCellPoint R)

/-- The canonical carrier homeomorphism retains the original cell target. -/
public def independentBGLCellTargetLiftHomeomorph (R : Type uR) [Ring R] :
    independentBGLCellTarget R ≃ₜ independentBGLCellTargetLift.{uR, uCarrier} R :=
  TopCat.uliftFunctorObjHomeo.{uCarrier, uR} (independentBGLCellTarget R)

/-- The actual upward continuous map of the original target. -/
public def independentBGLCellTargetUp (R : Type uR) [Ring R] :
    C(independentBGLCellTarget R, independentBGLCellTargetLift.{uR, uCarrier} R) :=
  (independentBGLCellTargetLiftHomeomorph.{uR, uCarrier} R).toHomotopyEquiv.toFun

/-- The actual downward continuous map to the original target. -/
public def independentBGLCellTargetDown (R : Type uR) [Ring R] :
    C(independentBGLCellTargetLift.{uR, uCarrier} R, independentBGLCellTarget R) :=
  (independentBGLCellTargetLiftHomeomorph.{uR, uCarrier} R).toHomotopyEquiv.invFun

/-- Every original target point is carried by literal `ULift.up`. -/
public theorem independentBGLCellTargetUp_apply (R : Type uR) [Ring R]
    (z : independentBGLCellTarget R) :
    independentBGLCellTargetUp.{uR, uCarrier} R z = ULift.up z := by
  rfl

/-- Every lifted target point is carried back by literal `ULift.down`. -/
public theorem independentBGLCellTargetDown_apply (R : Type uR) [Ring R]
    (z : independentBGLCellTargetLift.{uR, uCarrier} R) :
    independentBGLCellTargetDown.{uR, uCarrier} R z = z.down := by
  rfl

/-- The two target carrier maps compose to the original identity. -/
public theorem independentBGLCellTargetDown_comp_up (R : Type uR) [Ring R] :
    (independentBGLCellTargetDown.{uR, uCarrier} R).comp
        (independentBGLCellTargetUp.{uR, uCarrier} R) =
      ContinuousMap.id (independentBGLCellTarget R) := by
  apply ContinuousMap.ext
  intro z
  rfl

/-- The two target carrier maps compose to the lifted identity. -/
public theorem independentBGLCellTargetUp_comp_down (R : Type uR) [Ring R] :
    (independentBGLCellTargetUp.{uR, uCarrier} R).comp
        (independentBGLCellTargetDown.{uR, uCarrier} R) =
      ContinuousMap.id (independentBGLCellTargetLift.{uR, uCarrier} R) := by
  apply ContinuousMap.ext
  intro z
  exact ULift.up_down z

/-- The lifted inclusion computes its exact original marked point. -/
public theorem independentBGLCellInclusionLift_point (R : Type uR) [Ring R] :
    independentBGLCellInclusionLift.{uR, uCarrier} R
        (independentBGLSourcePointLift.{uR, uCarrier} R) =
      independentBGLCellPointLift.{uR, uCarrier} R := by
  change ULift.up (independentBGLCellInclusion R (ordinaryBGLBasepoint R)) =
    ULift.up (independentBGLCellPoint R)
  exact congrArg ULift.up (independentBGLCellInclusion_point R)

/-- The upward carrier map sends the original target point to the SAME lifted point. -/
public theorem independentBGLCellTargetUp_point (R : Type uR) [Ring R] :
    independentBGLCellTargetUp.{uR, uCarrier} R (independentBGLCellPoint R) =
      independentBGLCellPointLift.{uR, uCarrier} R := by
  rfl

/-- The downward carrier map returns the SAME original target point. -/
public theorem independentBGLCellTargetDown_point (R : Type uR) [Ring R] :
    independentBGLCellTargetDown.{uR, uCarrier} R
        (independentBGLCellPointLift.{uR, uCarrier} R) =
      independentBGLCellPoint R := by
  rfl

/-- The actual lifted inclusion is the up/original-inclusion/down composite. -/
public theorem independentBGLCellInclusionLift_apply (R : Type uR) [Ring R]
    (x : independentBGLSourceLift.{uR, uCarrier} R) :
    independentBGLCellInclusionLift.{uR, uCarrier} R x =
      ULift.up (independentBGLCellInclusion R x.down) := by
  rfl

/-- The intermediate space is the lift of the original two-cell attachment,
with its original subgroup index and attaching loops. -/
public abbrev independentBGLTwoCellTargetLift (R : Type uR) [Ring R] :
    TopCat.{max uR uCarrier} :=
  TopCat.uliftFunctor.{uCarrier, uR}.obj
    (LoopCellAttachment.space (ordinaryBGL R) (ordinaryBGLBasepoint R) (BGLPlusSubgroup R))

/-- The actual original two-cell inclusion in the requested carrier. -/
public abbrev independentBGLTwoCellInclusionLift (R : Type uR) [Ring R] :
    independentBGLSourceLift.{uR, uCarrier} R ⟶
      independentBGLTwoCellTargetLift.{uR, uCarrier} R :=
  TopCat.uliftFunctor.{uCarrier, uR}.map
    (LoopCellAttachment.inclusion (ordinaryBGL R) (ordinaryBGLBasepoint R) (BGLPlusSubgroup R))

/-- The actual original three-cell inclusion, with the same spherical
representatives as the ring-only construction, in the requested carrier. -/
public abbrev independentBGLThreeCellInclusionLift (R : Type uR) [Ring R] :
    independentBGLTwoCellTargetLift.{uR, uCarrier} R ⟶
      independentBGLCellTargetLift.{uR, uCarrier} R :=
  TopCat.uliftFunctor.{uCarrier, uR}.map
    (LoopCellRegularThreeComparison.originalThreeInclusion
      (ordinaryBGL R) (ordinaryBGLBasepoint R) (BGLPlusSubgroup R))

/-- The SAME two/three-cell presentation is retained literally by the lift.
No target is selected from a Q construction or a zero-component model. -/
public theorem independentBGLCellInclusionLift_eq_two_three (R : Type uR) [Ring R] :
    independentBGLCellInclusionLift.{uR, uCarrier} R =
      independentBGLTwoCellInclusionLift.{uR, uCarrier} R ≫
        independentBGLThreeCellInclusionLift.{uR, uCarrier} R := by
  have hI := congrArg
    (fun f : ordinaryBGL R ⟶ independentBGLCellTarget R =>
      TopCat.uliftFunctor.{uCarrier, uR}.map f)
    (independentBGLCellInclusion_eq_original R)
  exact hI.trans (TopCat.uliftFunctor.{uCarrier, uR}.map_comp
    (LoopCellAttachment.inclusion (ordinaryBGL R) (ordinaryBGLBasepoint R) (BGLPlusSubgroup R))
    (LoopCellRegularThreeComparison.originalThreeInclusion
      (ordinaryBGL R) (ordinaryBGLBasepoint R) (BGLPlusSubgroup R)))

/-- The original downward inclusion square is strict on every source value. -/
public theorem independentBGLCellInclusionLift_down_square (R : Type uR) [Ring R] :
    (independentBGLCellTargetDown.{uR, uCarrier} R).comp
        (independentBGLCellInclusionLift.{uR, uCarrier} R).hom =
      (independentBGLCellInclusion R).hom.comp
        (TopCat.uliftFunctorObjHomeo.{uCarrier, uR} (ordinaryBGL R)).toHomotopyEquiv.invFun := by
  apply ContinuousMap.ext
  intro x
  rfl

/-- The transported plus subgroup is the comap through the actual based
carrier projection. The original ring and subgroup are unchanged. -/
public abbrev BGLPlusSubgroupLift (R : Type uR) [Ring R] :
    Subgroup (FundamentalGroup (independentBGLSourceLift.{uR, uCarrier} R)
      (independentBGLSourcePointLift.{uR, uCarrier} R)) :=
  FundamentalGroup.UniverseLift.comapSubgroup.{uR, uCarrier}
    (ordinaryBGL R) (ordinaryBGLBasepoint R) (BGLPlusSubgroup R)

public instance BGLPlusSubgroupLift.instNormal (R : Type uR) [Ring R] :
    (BGLPlusSubgroupLift.{uR, uCarrier} R).Normal :=
  FundamentalGroup.UniverseLift.comapSubgroup_normal.{uR, uCarrier}
    (ordinaryBGL R) (ordinaryBGLBasepoint R) (BGLPlusSubgroup R)

public instance BGLPlusSubgroupLift.instIsPerfect (R : Type uR) [Ring R] :
    Group.IsPerfect (BGLPlusSubgroupLift.{uR, uCarrier} R) :=
  FundamentalGroup.UniverseLift.comapSubgroup_isPerfect.{uR, uCarrier}
    (ordinaryBGL R) (ordinaryBGLBasepoint R) (BGLPlusSubgroup R)

/-- The lifted target retains the actual connectedness of the old cell target. -/
public instance independentBGLCellTargetLift_pathConnected (R : Type uR) [Ring R] :
    PathConnectedSpace (independentBGLCellTargetLift.{uR, uCarrier} R) := by
  let : PathConnectedSpace (independentBGLCellTarget R) :=
    independentBGLCellTarget_pathConnected R
  exact (independentBGLCellTargetLiftHomeomorph.{uR, uCarrier} R).pathConnectedSpace

/-- The actual pi1 square computes the same inclusion under both canonical
carrier projections, with the exact original point equations. -/
public theorem independentBGLCellInclusionLift_pi1_down_square (R : Type uR) [Ring R] :
    (FundamentalGroup.UniverseLift.downMap.{uR, uCarrier}
        (independentBGLCellTarget R) (independentBGLCellPoint R)).comp
      (FundamentalGroup.mapOfEq
        (independentBGLCellInclusionLift.{uR, uCarrier} R).hom
        (independentBGLCellInclusionLift_point.{uR, uCarrier} R)) =
    (FundamentalGroup.mapOfEq (independentBGLCellInclusion R).hom
        (independentBGLCellInclusion_point R)).comp
      (FundamentalGroup.UniverseLift.downMap.{uR, uCarrier}
        (ordinaryBGL R) (ordinaryBGLBasepoint R)) := by
  let X := independentBGLSourceLift.{uR, uCarrier} R
  let x := independentBGLSourcePointLift.{uR, uCarrier} R
  let B := independentBGLCellTarget R
  let b := independentBGLCellPoint R
  let f := (independentBGLCellInclusionLift.{uR, uCarrier} R).hom
  let g := independentBGLCellTargetDown.{uR, uCarrier} R
  let d := (TopCat.uliftFunctorObjHomeo.{uCarrier, uR} (ordinaryBGL R)).toHomotopyEquiv.invFun
  let i := (independentBGLCellInclusion R).hom
  have hL : (g.comp f) x = b :=
    (congrArg g (independentBGLCellInclusionLift_point.{uR, uCarrier} R)).trans rfl
  have hR : (i.comp d) x = b := independentBGLCellInclusion_point R
  have hMaps : (⟨g.comp f, hL⟩ : {k : C(X, B) // k x = b}) =
      ⟨i.comp d, hR⟩ :=
    Subtype.ext (independentBGLCellInclusionLift_down_square.{uR, uCarrier} R)
  have hEq := congrArg
    (fun k : {k : C(X, B) // k x = b} => FundamentalGroup.mapOfEq k.val k.property) hMaps
  have hCompL := FundamentalGroup.mapOfEq_comp f g
    (independentBGLCellInclusionLift_point.{uR, uCarrier} R) rfl hL
  have hCompR := FundamentalGroup.mapOfEq_comp d i rfl
    (independentBGLCellInclusion_point R) hR
  exact hCompL.symm.trans (hEq.trans hCompR)

/-- The kernel of the literal lifted inclusion is exactly the transported
original stable-elementary subgroup. -/
public theorem independentBGLCellInclusionLift_kernel (R : Type uR) [Ring R] :
    MonoidHom.ker (FundamentalGroup.mapOfEq
      (independentBGLCellInclusionLift.{uR, uCarrier} R).hom
      (independentBGLCellInclusionLift_point.{uR, uCarrier} R)) =
        BGLPlusSubgroupLift.{uR, uCarrier} R := by
  let fN := FundamentalGroup.mapOfEq
    (independentBGLCellInclusionLift.{uR, uCarrier} R).hom
    (independentBGLCellInclusionLift_point.{uR, uCarrier} R)
  let f0 := FundamentalGroup.mapOfEq (independentBGLCellInclusion R).hom
    (independentBGLCellInclusion_point R)
  let dX := FundamentalGroup.UniverseLift.downMap.{uR, uCarrier}
    (ordinaryBGL R) (ordinaryBGLBasepoint R)
  let dB := FundamentalGroup.UniverseLift.downMap.{uR, uCarrier}
    (independentBGLCellTarget R) (independentBGLCellPoint R)
  have hk0 : MonoidHom.ker f0 = BGLPlusSubgroup R :=
    (independentBGLCellInclusion_isPlus R).kernel_eq
  have hInjective : Function.Injective dB := by
    change Function.Injective (FundamentalGroup.UniverseLift.downMap.{uR, uCarrier}
      (independentBGLCellTarget R) (independentBGLCellPoint R))
    rw [← FundamentalGroup.UniverseLift.downMulEquiv_toMonoidHom.{uR, uCarrier}
      (independentBGLCellTarget R) (independentBGLCellPoint R)]
    exact (FundamentalGroup.UniverseLift.downMulEquiv.{uR, uCarrier}
      (independentBGLCellTarget R) (independentBGLCellPoint R)).injective
  have hSquare : dB.comp fN = f0.comp dX :=
    independentBGLCellInclusionLift_pi1_down_square.{uR, uCarrier} R
  apply Subgroup.ext
  intro q
  change fN q = 1 ↔ dX q ∈ BGLPlusSubgroup R
  have hMem : dX q ∈ BGLPlusSubgroup R ↔ f0 (dX q) = 1 := by
    have hPred := congrArg
      (fun P : Subgroup (FundamentalGroup (ordinaryBGL R) (ordinaryBGLBasepoint R)) =>
        dX q ∈ P) hk0
    simpa only [MonoidHom.mem_ker] using Iff.of_eq hPred.symm
  have hValue : dB (fN q) = f0 (dX q) :=
    congrArg (fun k => k q) hSquare
  constructor
  · intro hq
    apply hMem.2
    exact hValue.symm.trans ((congrArg dB hq).trans dB.map_one)
  · intro hq
    apply hInjective
    exact hValue.trans ((hMem.1 hq).trans dB.map_one.symm)

/-- The actual image homotopy fiber is acyclic in the new integral
coefficient universe. This uses the actual fiber Iso and chain lift. -/
public theorem independentBGLCellInclusionLift_acyclic (R : Type uR) [Ring R] :
    TopCat.IsAcyclicMapAt (independentBGLCellInclusionLift.{uR, uCarrier} R)
      (independentBGLCellPointLift.{uR, uCarrier} R) := by
  let i := independentBGLCellInclusion R
  let x := ordinaryBGLBasepoint R
  let b := independentBGLCellPoint R
  have hPoint : i x = b := independentBGLCellInclusion_point R
  have hOld : TopCat.IsAcyclicMapAt i (i x) :=
    Eq.mp (congrArg (fun y => TopCat.IsAcyclicMapAt i y) hPoint.symm)
      (independentBGLCellInclusion_isPlus R).acyclic
  have hLift := TopCat.UniverseLift.isAcyclicMapAt_ulift_at_image.{uR, uCarrier} i x hOld
  exact Eq.mp (congrArg
    (fun y : independentBGLCellTargetLift.{uR, uCarrier} R =>
      TopCat.IsAcyclicMapAt (independentBGLCellInclusionLift.{uR, uCarrier} R) y)
      (congrArg ULift.up hPoint)) hLift

/-- Plus recognition for the SAME ring-only cell construction in the new
native carrier is derived, with no supplied plus, model or inverse data. -/
public theorem independentBGLCellInclusionLift_isPlus (R : Type uR) [Ring R] :
    TopCat.IsPlusConstructionAt (independentBGLCellInclusionLift.{uR, uCarrier} R)
      (independentBGLSourcePointLift.{uR, uCarrier} R)
      (independentBGLCellPointLift.{uR, uCarrier} R)
      (independentBGLCellInclusionLift_point.{uR, uCarrier} R)
      (BGLPlusSubgroupLift.{uR, uCarrier} R) := by
  exact
    { acyclic := independentBGLCellInclusionLift_acyclic.{uR, uCarrier} R
      kernel_eq := independentBGLCellInclusionLift_kernel.{uR, uCarrier} R }

/-- Every original integer target local system, including nonflat systems,
is preserved by the actual lifted inclusion. -/
public theorem independentBGLCellInclusionLift_allLocalCoefficients (R : Type uR) [Ring R] :
    TopCat.IsLocalCoefficientHomologyEquivalence
      (independentBGLCellInclusionLift.{uR, uCarrier} R) :=
  (independentBGLCellInclusionLift_isPlus.{uR, uCarrier} R).localCoefficientHomologyEquivalence

/-- Every original target point has an acyclic actual ending-path fiber. -/
public theorem independentBGLCellInclusionLift_acyclic_all (R : Type uR) [Ring R]
    (b : independentBGLCellTargetLift.{uR, uCarrier} R) :
    TopCat.IsAcyclicMapAt (independentBGLCellInclusionLift.{uR, uCarrier} R) b :=
  (independentBGLCellInclusionLift_isPlus.{uR, uCarrier} R).homotopyFiber_acyclic_all b

/-- The literal lifted pi1 map is surjective, derived from the same acyclic
image fiber and original source point. -/
public theorem independentBGLCellInclusionLift_pi1_surjective (R : Type uR) [Ring R] :
    Function.Surjective (FundamentalGroup.mapOfEq
      (independentBGLCellInclusionLift.{uR, uCarrier} R).hom
      (independentBGLCellInclusionLift_point.{uR, uCarrier} R)) :=
  (independentBGLCellInclusionLift_isPlus.{uR, uCarrier} R).pi1Map_surjective


/-! ## The actual independent-probe native CW model of the same cell target -/

/-- The fixed native model uses the actual independent compact-probe universe. -/
public abbrev independentBGLCellNativeModelSpace (R : Type uR) [Ring R] :
    CGWH.{uProbe, max uR uCarrier} :=
  SSet.toCGWH.{uProbe, max uR uCarrier}.obj
    (SSet.uliftFunctor.{uCarrier, uR}.obj
      (TopCat.toSSet.obj (independentBGLCellTarget R)))

/-- The literal lifted singular vertex of the original cell-plus point. -/
public abbrev independentBGLCellNativeModelPoint (R : Type uR) [Ring R] :
    independentBGLCellNativeModelSpace.{uR, uCarrier, uProbe} R :=
  SSet.realizedVertex
    (X := SSet.uliftFunctor.{uCarrier, uR}.obj
      (TopCat.toSSet.obj (independentBGLCellTarget R)))
    (ULift.up (TopCat.toSSetObj₀Equiv.symm (independentBGLCellPoint R)))

private def independentBGLCellModelCarrierIso (R : Type uR) [Ring R] :
    (independentBGLCellNativeModelSpace.{uR, uCarrier, uProbe} R).toTop ≅
      TopCat.uliftFunctor.{uCarrier, uR}.obj
        ((TopCat.nativeSingularSpace (independentBGLCellTarget R)).toTop) :=
  (SSet.realizationToTopIso.{uProbe, max uR uCarrier}.app
    (SSet.uliftFunctor.{uCarrier, uR}.obj
      (TopCat.toSSet.obj (independentBGLCellTarget R)))) ≪≫
    (SSet.toTopULiftIso.{uR, uCarrier}.app
      (TopCat.toSSet.obj (independentBGLCellTarget R))) ≪≫
    (TopCat.uliftFunctor.{uCarrier, uR}).mapIso
      (TopCat.nativeSingularToTopIso (independentBGLCellTarget R)).symm

private def independentBGLCellModelCarrierHomeomorph (R : Type uR) [Ring R] :
    independentBGLCellNativeModelSpace.{uR, uCarrier, uProbe} R ≃ₜ
      TopCat.nativeSingularSpace (independentBGLCellTarget R) :=
  (TopCat.homeoOfIso (independentBGLCellModelCarrierIso.{uR, uCarrier, uProbe} R)).trans
    Homeomorph.ulift

private theorem independentBGLCellModelCarrierPoint (R : Type uR) [Ring R] :
    independentBGLCellModelCarrierHomeomorph.{uR, uCarrier, uProbe} R
      (independentBGLCellNativeModelPoint.{uR, uCarrier, uProbe} R) =
        TopCat.nativeSingularPoint (independentBGLCellTarget R) (independentBGLCellPoint R) := by
  let X := independentBGLCellTarget R
  let x := independentBGLCellPoint R
  let K := TopCat.toSSet.obj X
  let v₀ := TopCat.toSSetObj₀Equiv.symm x
  change ((TopCat.uliftFunctor.{uCarrier, uR}).map
      (TopCat.nativeSingularToTopIso X).inv
      ((SSet.toTopULiftIso.{uR, uCarrier}.hom.app K)
        (SSet.realizedVertex (X := SSet.uliftFunctor.{uCarrier, uR}.obj K)
          (ULift.up v₀)))).down = TopCat.nativeSingularPoint X x
  rw [SSet.toTopULiftIso_hom_realizedVertex]
  rfl

private def independentBGLCellOriginalPointModel (R : Type uR) [Ring R] :
    TopCat.NativeSingularPointModel (independentBGLCellTarget R) (independentBGLCellPoint R) := by
  letI : Cofibration (TopCat.const (independentBGLCellPoint R) :
      TopCat.of PUnit.{uR + 1} ⟶ independentBGLCellTarget R) :=
    independentBGLCellPoint_cofibration R
  exact TopCat.nativeSingularPointModelOfCofibrantPoint
    (independentBGLCellTarget R) (independentBGLCellPoint R)

/-- The canonical comparison, original singular counit, and literal target-up map. -/
public def independentBGLCellNativeModelForward (R : Type uR) [Ring R] :
    C(independentBGLCellNativeModelSpace.{uR, uCarrier, uProbe} R,
      independentBGLCellTargetLift.{uR, uCarrier} R) :=
  ((SSet.realizationToTopIso.{uProbe, max uR uCarrier}.hom.app
      (SSet.uliftFunctor.{uCarrier, uR}.obj
        (TopCat.toSSet.obj (independentBGLCellTarget R)))) ≫
    (SSet.toTopULiftIso.{uR, uCarrier}.hom.app
      (TopCat.toSSet.obj (independentBGLCellTarget R))) ≫
    (TopCat.uliftFunctor.{uCarrier, uR}).map
      (sSetTopAdj.counit.app (independentBGLCellTarget R))).hom

private def independentBGLCellModelEquivalence (R : Type uR) [Ring R] :
    independentBGLCellNativeModelSpace.{uR, uCarrier, uProbe} R ≃ₕ
      independentBGLCellTargetLift.{uR, uCarrier} R :=
  (independentBGLCellModelCarrierHomeomorph.{uR, uCarrier, uProbe} R).toHomotopyEquiv.trans
    ((independentBGLCellOriginalPointModel R).equiv.trans
      (independentBGLCellTargetLiftHomeomorph.{uR, uCarrier} R).toHomotopyEquiv)

private theorem independentBGLCellModelForwardEq (R : Type uR) [Ring R] :
    (independentBGLCellModelEquivalence.{uR, uCarrier, uProbe} R).toFun =
      independentBGLCellNativeModelForward.{uR, uCarrier, uProbe} R := by
  change (independentBGLCellTargetLiftHomeomorph.{uR, uCarrier} R).toHomotopyEquiv.toFun.comp
      ((independentBGLCellOriginalPointModel R).equiv.toFun.comp
        (independentBGLCellModelCarrierHomeomorph.{uR, uCarrier, uProbe} R).toHomotopyEquiv.toFun) = _
  unfold independentBGLCellNativeModelForward
  rw [(independentBGLCellOriginalPointModel R).forward_eq]
  apply ContinuousMap.ext
  intro x
  rfl

private theorem independentBGLCellModelForwardPoint (R : Type uR) [Ring R] :
    (independentBGLCellModelEquivalence.{uR, uCarrier, uProbe} R).toFun
        (independentBGLCellNativeModelPoint.{uR, uCarrier, uProbe} R) =
      independentBGLCellPointLift.{uR, uCarrier} R := by
  change independentBGLCellTargetLiftHomeomorph.{uR, uCarrier} R
      ((independentBGLCellOriginalPointModel R).equiv.toFun
        (independentBGLCellModelCarrierHomeomorph.{uR, uCarrier, uProbe} R
          (independentBGLCellNativeModelPoint.{uR, uCarrier, uProbe} R))) = _
  rw [independentBGLCellModelCarrierPoint,
    (independentBGLCellOriginalPointModel R).forwardPoint]
  exact independentBGLCellTargetUp_point.{uR, uCarrier} R

private theorem independentBGLCellModelBackwardPoint (R : Type uR) [Ring R] :
    (independentBGLCellModelEquivalence.{uR, uCarrier, uProbe} R).invFun
        (independentBGLCellPointLift.{uR, uCarrier} R) =
      independentBGLCellNativeModelPoint.{uR, uCarrier, uProbe} R := by
  let h := independentBGLCellModelCarrierHomeomorph.{uR, uCarrier, uProbe} R
  let hb := independentBGLCellTargetLiftHomeomorph.{uR, uCarrier} R
  have hbPoint : hb.symm (independentBGLCellPointLift.{uR, uCarrier} R) =
      independentBGLCellPoint R := by
    rw [← independentBGLCellTargetUp_point.{uR, uCarrier} R]
    exact hb.symm_apply_apply (independentBGLCellPoint R)
  change h.symm ((independentBGLCellOriginalPointModel R).equiv.invFun
      (hb.symm (independentBGLCellPointLift.{uR, uCarrier} R))) = _
  rw [hbPoint, (independentBGLCellOriginalPointModel R).backwardPoint]
  rw [← independentBGLCellModelCarrierPoint.{uR, uCarrier, uProbe} R]
  exact h.symm_apply_apply (independentBGLCellNativeModelPoint.{uR, uCarrier, uProbe} R)

private def independentBGLCellModelLeftFamily (R : Type uR) [Ring R] :
    ContinuousMap.HomotopyRel
      ((independentBGLCellModelEquivalence.{uR, uCarrier, uProbe} R).invFun.comp
        (independentBGLCellModelEquivalence.{uR, uCarrier, uProbe} R).toFun)
      (ContinuousMap.id (independentBGLCellNativeModelSpace.{uR, uCarrier, uProbe} R))
      {independentBGLCellNativeModelPoint.{uR, uCarrier, uProbe} R} := by
  let h := independentBGLCellModelCarrierHomeomorph.{uR, uCarrier, uProbe} R
  let hb := independentBGLCellTargetLiftHomeomorph.{uR, uCarrier} R
  let M := independentBGLCellOriginalPointModel R
  let L := (M.leftFamily.precomposePointRelative h.toHomotopyEquiv.toFun
    (independentBGLCellNativeModelPoint.{uR, uCarrier, uProbe} R)
    (independentBGLCellModelCarrierPoint.{uR, uCarrier, uProbe} R)).compContinuousMap
      h.toHomotopyEquiv.invFun
  refine L.cast ?_ ?_
  · apply ContinuousMap.ext
    intro x
    change h.symm (M.equiv.invFun (M.equiv.toFun (h x))) =
      h.symm (M.equiv.invFun (hb.symm (hb (M.equiv.toFun (h x)))))
    rw [hb.symm_apply_apply]
  · apply ContinuousMap.ext
    intro x
    change h.symm (h x) = x
    exact h.symm_apply_apply x

private def independentBGLCellModelRightFamily (R : Type uR) [Ring R] :
    ContinuousMap.HomotopyRel
      ((independentBGLCellModelEquivalence.{uR, uCarrier, uProbe} R).toFun.comp
        (independentBGLCellModelEquivalence.{uR, uCarrier, uProbe} R).invFun)
      (ContinuousMap.id (independentBGLCellTargetLift.{uR, uCarrier} R))
      {independentBGLCellPointLift.{uR, uCarrier} R} := by
  let h := independentBGLCellModelCarrierHomeomorph.{uR, uCarrier, uProbe} R
  let hb := independentBGLCellTargetLiftHomeomorph.{uR, uCarrier} R
  let M := independentBGLCellOriginalPointModel R
  have hbPoint : hb.symm (independentBGLCellPointLift.{uR, uCarrier} R) =
      independentBGLCellPoint R := by
    rw [← independentBGLCellTargetUp_point.{uR, uCarrier} R]
    exact hb.symm_apply_apply (independentBGLCellPoint R)
  let H := (M.rightFamily.precomposePointRelative hb.toHomotopyEquiv.invFun
    (independentBGLCellPointLift.{uR, uCarrier} R) hbPoint).compContinuousMap hb.toHomotopyEquiv.toFun
  refine H.cast ?_ ?_
  · apply ContinuousMap.ext
    intro x
    change hb (M.equiv.toFun (M.equiv.invFun (hb.symm x))) =
      hb (M.equiv.toFun (h (h.symm (M.equiv.invFun (hb.symm x)))))
    rw [h.apply_symm_apply]
  · apply ContinuousMap.ext
    intro x
    change hb (hb.symm x) = x
    exact hb.apply_symm_apply x

private theorem independentBGLCellModelT2 (R : Type uR) [Ring R] :
    T2Space (independentBGLCellNativeModelSpace.{uR, uCarrier, uProbe} R) :=
  SSet.realization_t2Space (SSet.uliftFunctor.{uCarrier, uR}.obj
    (TopCat.toSSet.obj (independentBGLCellTarget R)))

private def independentBGLCellModelCW (R : Type uR) [Ring R] :
    Topology.CWComplex (Set.univ : Set (independentBGLCellNativeModelSpace.{uR, uCarrier, uProbe} R)) :=
  SSet.instCWComplexToTop (SSet.uliftFunctor.{uCarrier, uR}.obj
    (TopCat.toSSet.obj (independentBGLCellTarget R)))

private theorem independentBGLCellModelPointCofibration (R : Type uR) [Ring R] :
    Cofibration (TopCat.const (independentBGLCellNativeModelPoint.{uR, uCarrier, uProbe} R) :
      TopCat.of PUnit.{max uR uCarrier + 1} ⟶
        (independentBGLCellNativeModelSpace.{uR, uCarrier, uProbe} R).toTop) :=
  SSet.realizedVertex_pointMap_cofibration
    (SSet.uliftFunctor.{uCarrier, uR}.obj (TopCat.toSSet.obj (independentBGLCellTarget R)))
    (ULift.up (TopCat.toSSetObj₀Equiv.symm (independentBGLCellPoint R)))

/-- A genuine native CW/based model with its actual independent compact-probe data. -/
public structure IndependentBGLCellNativePointModel (R : Type uR) [Ring R] where
  /-- The actual CGWH model, including its independent compact probes. -/
  space : CGWH.{uProbe, max uR uCarrier}
  /-- Its source is the fixed realization of the original lifted singular set. -/
  space_eq : space = independentBGLCellNativeModelSpace.{uR, uCarrier, uProbe} R
  /-- The actual selected point of that same model. -/
  point : space
  /-- The selected point is the fixed original lifted singular vertex. -/
  point_eq : (space_eq ▸ point) = independentBGLCellNativeModelPoint.{uR, uCarrier, uProbe} R
  /-- The actual complete equivalence to the same original lifted cell target. -/
  equiv : space ≃ₕ independentBGLCellTargetLift.{uR, uCarrier} R
  /-- Its forward map is the canonical comparison and original counit. -/
  forward_eq : (space_eq ▸ equiv.toFun) = independentBGLCellNativeModelForward.{uR, uCarrier, uProbe} R
  /-- The original native vertex maps to the same lifted cell point. -/
  forwardPoint : equiv.toFun point = independentBGLCellPointLift.{uR, uCarrier} R
  /-- The derived inverse maps the same lifted point back to that vertex. -/
  backwardPoint : equiv.invFun (independentBGLCellPointLift.{uR, uCarrier} R) = point
  /-- The complete source inverse family fixes the actual model point. -/
  leftFamily : ContinuousMap.HomotopyRel (equiv.invFun.comp equiv.toFun)
    (ContinuousMap.id space) {point}
  /-- The complete target inverse family fixes the same cell point. -/
  rightFamily : ContinuousMap.HomotopyRel (equiv.toFun.comp equiv.invFun)
    (ContinuousMap.id (independentBGLCellTargetLift.{uR, uCarrier} R))
    {independentBGLCellPointLift.{uR, uCarrier} R}
  /-- Hausdorffness of the actual native realization. -/
  isT2 : T2Space space
  /-- The actual classical CW structure on that realization. -/
  cwComplex : Topology.CWComplex (Set.univ : Set space)
  /-- The actual marked vertex is a cofibration, not a supplied model premise. -/
  pointCofibration : Cofibration (TopCat.const point :
    TopCat.of PUnit.{max uR uCarrier + 1} ⟶ space.toTop)

/-- Construct the actual independent-probe native model from the Ring-only cell plus. -/
public def independentBGLCellNativePointModelOfRing (R : Type uR) [Ring R] :
    IndependentBGLCellNativePointModel.{uR, uCarrier, uProbe} R :=
  { space := independentBGLCellNativeModelSpace.{uR, uCarrier, uProbe} R
    space_eq := rfl
    point := independentBGLCellNativeModelPoint.{uR, uCarrier, uProbe} R
    point_eq := rfl
    equiv := independentBGLCellModelEquivalence.{uR, uCarrier, uProbe} R
    forward_eq := independentBGLCellModelForwardEq.{uR, uCarrier, uProbe} R
    forwardPoint := independentBGLCellModelForwardPoint.{uR, uCarrier, uProbe} R
    backwardPoint := independentBGLCellModelBackwardPoint.{uR, uCarrier, uProbe} R
    leftFamily := independentBGLCellModelLeftFamily.{uR, uCarrier, uProbe} R
    rightFamily := independentBGLCellModelRightFamily.{uR, uCarrier, uProbe} R
    isT2 := independentBGLCellModelT2.{uR, uCarrier, uProbe} R
    cwComplex := independentBGLCellModelCW.{uR, uCarrier, uProbe} R
    pointCofibration := independentBGLCellModelPointCofibration.{uR, uCarrier, uProbe} R }


/-- The SAME lifted cell target has a genuine classical CW homotopy type.
This convenience conclusion makes no demand on an independently chosen
probe level; the model producer above remains fully probe-polymorphic. -/
public theorem independentBGLCellTargetLift_cwType (R : Type uR) [Ring R] :
    ∃ C : TopCat.{max uR uCarrier}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C),
        Nonempty (C ≃ₕ independentBGLCellTargetLift.{uR, uCarrier} R) := by
  let M := independentBGLCellNativePointModelOfRing.{uR, uCarrier, 0} R
  exact ⟨M.space.toTop, M.isT2, M.cwComplex, ⟨M.equiv⟩⟩

end AlgebraicKTheory.StableGL
