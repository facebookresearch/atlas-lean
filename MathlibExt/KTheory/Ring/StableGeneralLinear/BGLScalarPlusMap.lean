/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.IndependentPlusScalarExtension
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.PathTransportNaturality

/-!
# The scalar plus map on the original cell targets

The actual mixed-ring source map is extended using the existing native point
model, then descended by the literal carrier maps. Both rings retain their
independent universes. The internal common-carrier and native-probe choices
are used only to construct this original-target representative, whose whole
source triangle and point-relative universal property are proved below.
-/

noncomputable section

open CategoryTheory
open scoped ContinuousMap

universe uR uS

namespace AlgebraicKTheory.StableGL

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- The proven native extension descended to the two ORIGINAL ring-only cell targets. -/
public def independentBGLScalarPlusMap (f : R →+* S) :
    C(independentBGLCellTarget R, independentBGLCellTarget S) :=
  let M := independentBGLCellNativePointModelOfRing.{uR, uS, 0} R
  let E := independentBGLScalarNativeExtensionDataOfHom.{uR, uS, 0, 0} f
  (independentBGLCellTargetDown.{uS, uR} S).comp
    (E.map.hom.comp (M.equiv.invFun.comp (independentBGLCellTargetUp.{uR, uS} R)))

private theorem scalarPlusMap_point_computed (f : R →+* S) :
    independentBGLScalarPlusMap f (independentBGLCellPoint R) = independentBGLCellPoint S := by
  let M := independentBGLCellNativePointModelOfRing.{uR, uS, 0} R
  let E := independentBGLScalarNativeExtensionDataOfHom.{uR, uS, 0, 0} f
  change (independentBGLCellTargetDown.{uS, uR} S)
    (E.map (M.equiv.invFun
      ((independentBGLCellTargetUp.{uR, uS} R) (independentBGLCellPoint R)))) =
        independentBGLCellPoint S
  rw [independentBGLCellTargetUp_point.{uR, uS} R, M.backwardPoint, E.point]
  exact independentBGLCellTargetDown_point.{uS, uR} S

/-- The actual scalar plus map retains the two original marked cell points. -/
public theorem independentBGLScalarPlusMap_point (f : R →+* S) :
    independentBGLScalarPlusMap f (independentBGLCellPoint R) = independentBGLCellPoint S :=
  scalarPlusMap_point_computed f

private def scalarPlusMap_sourceTriangle (f : R →+* S) :
    ContinuousMap.HomotopyRel
      ((independentBGLScalarPlusMap f).comp (independentBGLCellInclusion R).hom)
      ((independentBGLCellInclusion S).hom.comp (ordinaryBGLScalarMap f))
      {ordinaryBGLBasepoint R} := by
  let M := independentBGLCellNativePointModelOfRing.{uR, uS, 0} R
  let E := independentBGLScalarNativeExtensionDataOfHom.{uR, uS, 0, 0} f
  let U : C(ordinaryBGL R, independentBGLSourceLift.{uR, uS} R) :=
    ⟨ULift.up, continuous_uliftUp⟩
  let D := independentBGLCellTargetDown.{uS, uR} S
  let H := (E.triangle.precomposePointRelative U (ordinaryBGLBasepoint R) rfl).compContinuousMap D
  refine H.cast ?_ ?_
  · apply ContinuousMap.ext
    intro x
    let z : independentBGLSourceLift.{uR, uS} R := U x
    have hz : z.down = x := rfl
    have hNative : independentBGLCellNativeInclusion.{uR, uS, 0} R z =
        M.equiv.invFun (independentBGLCellInclusionLift.{uR, uS} R z) :=
      independentBGLCellNativeInclusion_apply.{uR, uS, 0} R z
    have hInclusion : independentBGLCellInclusionLift.{uR, uS} R z =
        (independentBGLCellTargetUp.{uR, uS} R) (independentBGLCellInclusion R x) :=
      (independentBGLCellInclusionLift_apply.{uR, uS} R z).trans
        ((congrArg (fun a : ordinaryBGL R =>
            (ULift.up (independentBGLCellInclusion R a) :
              independentBGLCellTargetLift.{uR, uS} R)) hz).trans
          (independentBGLCellTargetUp_apply.{uR, uS} R (independentBGLCellInclusion R x)).symm)
    have hInput := hNative.trans (congrArg M.equiv.invFun hInclusion)
    exact congrArg (fun a : M.space => D (E.map a)) hInput
  · apply ContinuousMap.ext
    intro x
    let z : independentBGLSourceLift.{uR, uS} R := U x
    let w : independentBGLSourceLift.{uS, uR} S := ordinaryBGLScalarCarrierMap.{uR, uS, 0} f z
    have hz : z.down = x := rfl
    have hDown : D (independentBGLCellInclusionLift.{uS, uR} S w) =
        (independentBGLCellInclusionLift.{uS, uR} S w).down :=
      independentBGLCellTargetDown_apply.{uS, uR} S _
    have hInclusion : (independentBGLCellInclusionLift.{uS, uR} S w).down =
        independentBGLCellInclusion S w.down :=
      congrArg (fun a : independentBGLCellTargetLift.{uS, uR} S => a.down)
        (independentBGLCellInclusionLift_apply.{uS, uR} S w)
    have hScalar : w.down = ordinaryBGLScalarMap f x :=
      (congrArg (fun a : independentBGLSourceLift.{uS, uR} S => a.down)
        (ordinaryBGLScalarCarrierMap_apply.{uR, uS, 0} f z)).trans
          (congrArg (ordinaryBGLScalarMap f) hz)
    exact hDown.trans (hInclusion.trans (congrArg (independentBGLCellInclusion S) hScalar))

/-- The whole original BGL source triangle fixes its original vertex at every time. -/
public theorem independentBGLScalarPlusMap_triangle (f : R →+* S) :
    Nonempty (ContinuousMap.HomotopyRel
      ((independentBGLScalarPlusMap f).comp (independentBGLCellInclusion R).hom)
      ((independentBGLCellInclusion S).hom.comp (ordinaryBGLScalarMap f))
      {ordinaryBGLBasepoint R}) :=
  ⟨scalarPlusMap_sourceTriangle f⟩

private def liftOriginalCellCandidate
    (G : C(independentBGLCellTarget R, independentBGLCellTarget S)) :
    (independentBGLCellNativePointModelOfRing.{uR, uS, 0} R).space.toTop ⟶
      independentBGLCellTargetLift.{uS, uR} S :=
  let M := independentBGLCellNativePointModelOfRing.{uR, uS, 0} R
  TopCat.ofHom ((independentBGLCellTargetUp.{uS, uR} S).comp
    (G.comp ((independentBGLCellTargetDown.{uR, uS} R).comp M.equiv.toFun)))

private def liftOriginalCellCandidate_triangle (f : R →+* S)
    (G : C(independentBGLCellTarget R, independentBGLCellTarget S))
    (HG : ContinuousMap.HomotopyRel (G.comp (independentBGLCellInclusion R).hom)
      ((independentBGLCellInclusion S).hom.comp (ordinaryBGLScalarMap f))
      {ordinaryBGLBasepoint R}) :
    ContinuousMap.HomotopyRel
      (independentBGLCellNativeInclusion.{uR, uS, 0} R ≫ liftOriginalCellCandidate G).hom
      (ordinaryBGLScalarCarrierMap.{uR, uS, 0} f ≫
        independentBGLCellInclusionLift.{uS, uR} S).hom
      {independentBGLSourcePointLift.{uR, uS} R} := by
  let M := independentBGLCellNativePointModelOfRing.{uR, uS, 0} R
  let U := independentBGLCellTargetUp.{uS, uR} S
  let D := independentBGLCellTargetDown.{uR, uS} R
  let p : C(independentBGLSourceLift.{uR, uS} R, ordinaryBGL R) :=
    ⟨ULift.down, continuous_uliftDown⟩
  let Hmodel := (M.rightFamily.precomposePointRelative
    (independentBGLCellInclusionLift.{uR, uS} R).hom
    (independentBGLSourcePointLift.{uR, uS} R)
    (independentBGLCellInclusionLift_point.{uR, uS} R)).compContinuousMap (U.comp (G.comp D))
  let A := U.comp (G.comp ((independentBGLCellInclusion R).hom.comp p))
  let B := U.comp ((independentBGLCellInclusion S).hom.comp ((ordinaryBGLScalarMap f).comp p))
  let Hstart : ContinuousMap.HomotopyRel
      (independentBGLCellNativeInclusion.{uR, uS, 0} R ≫ liftOriginalCellCandidate G).hom A
      {independentBGLSourcePointLift.{uR, uS} R} := Hmodel.cast
    (by
      apply ContinuousMap.ext
      intro x
      exact congrArg (fun a : M.space => U (G (D (M.equiv.toFun a))))
        (independentBGLCellNativeInclusion_apply.{uR, uS, 0} R x).symm)
    (by
      apply ContinuousMap.ext
      intro x
      have hDown : D (independentBGLCellInclusionLift.{uR, uS} R x) =
          (independentBGLCellInclusionLift.{uR, uS} R x).down :=
        independentBGLCellTargetDown_apply.{uR, uS} R _
      have hInclusion : (independentBGLCellInclusionLift.{uR, uS} R x).down =
          independentBGLCellInclusion R x.down :=
        congrArg (fun a : independentBGLCellTargetLift.{uR, uS} R => a.down)
          (independentBGLCellInclusionLift_apply.{uR, uS} R x)
      exact congrArg (fun a : independentBGLCellTarget R => U (G a)) (hDown.trans hInclusion))
  let Hraw0 := (HG.precomposePointRelative p
    (independentBGLSourcePointLift.{uR, uS} R) rfl).compContinuousMap U
  let Hraw : ContinuousMap.HomotopyRel A B {independentBGLSourcePointLift.{uR, uS} R} :=
    Hraw0.cast (by apply ContinuousMap.ext; intro x; rfl) (by apply ContinuousMap.ext; intro x; rfl)
  have hLast : B = (ordinaryBGLScalarCarrierMap.{uR, uS, 0} f ≫
      independentBGLCellInclusionLift.{uS, uR} S).hom := by
    apply ContinuousMap.ext
    intro x
    let w : independentBGLSourceLift.{uS, uR} S := ordinaryBGLScalarCarrierMap.{uR, uS, 0} f x
    have hUp : U (independentBGLCellInclusion S (ordinaryBGLScalarMap f x.down)) =
        (ULift.up (independentBGLCellInclusion S (ordinaryBGLScalarMap f x.down)) :
          independentBGLCellTargetLift.{uS, uR} S) :=
      independentBGLCellTargetUp_apply.{uS, uR} S _
    have hScalar : w.down = ordinaryBGLScalarMap f x.down :=
      congrArg (fun a : independentBGLSourceLift.{uS, uR} S => a.down)
        (ordinaryBGLScalarCarrierMap_apply.{uR, uS, 0} f x)
    have hInclusion : independentBGLCellInclusionLift.{uS, uR} S w =
        (ULift.up (independentBGLCellInclusion S (ordinaryBGLScalarMap f x.down)) :
          independentBGLCellTargetLift.{uS, uR} S) :=
      (independentBGLCellInclusionLift_apply.{uS, uR} S w).trans
        (congrArg (fun a : ordinaryBGL S =>
          (ULift.up (independentBGLCellInclusion S a) :
            independentBGLCellTargetLift.{uS, uR} S)) hScalar)
    exact hUp.trans hInclusion.symm

  exact (Hstart.trans Hraw).cast rfl hLast

private def cancelOriginalCellCandidate
    (G : C(independentBGLCellTarget R, independentBGLCellTarget S)) :
    ContinuousMap.HomotopyRel
      ((independentBGLCellTargetDown.{uS, uR} S).comp
        ((liftOriginalCellCandidate G).hom.comp
          ((independentBGLCellNativePointModelOfRing.{uR, uS, 0} R).equiv.invFun.comp
            (independentBGLCellTargetUp.{uR, uS} R))))
      G {independentBGLCellPoint R} := by
  let M := independentBGLCellNativePointModelOfRing.{uR, uS, 0} R
  let U := independentBGLCellTargetUp.{uR, uS} R
  let D := independentBGLCellTargetDown.{uR, uS} R
  let H := (M.rightFamily.precomposePointRelative U (independentBGLCellPoint R)
    (independentBGLCellTargetUp_point.{uR, uS} R)).compContinuousMap (G.comp D)
  refine H.cast ?_ ?_
  · apply ContinuousMap.ext
    intro x
    change G (D (M.equiv.toFun (M.equiv.invFun (U x)))) =
      independentBGLCellTargetDown.{uS, uR} S
        (independentBGLCellTargetUp.{uS, uR} S
          (G (D (M.equiv.toFun (M.equiv.invFun (U x))))))
    rw [independentBGLCellTargetDown_apply.{uS, uR} S,
      independentBGLCellTargetUp_apply.{uS, uR} S]
  · apply ContinuousMap.ext
    intro x
    change G (D (U x)) = G x
    rw [independentBGLCellTargetDown_apply.{uR, uS} R,
      independentBGLCellTargetUp_apply.{uR, uS} R]

/-- The descended actual map is characterized by its original source triangle,
with both whole point-relative uniqueness families on the original cell target. -/
public theorem independentBGLScalarPlusMap_universal (f : R →+* S) :
    ∀ G : C(independentBGLCellTarget R, independentBGLCellTarget S),
      Nonempty (ContinuousMap.HomotopyRel (G.comp (independentBGLCellInclusion R).hom)
        ((independentBGLCellInclusion S).hom.comp (ordinaryBGLScalarMap f))
        {ordinaryBGLBasepoint R}) →
      Nonempty (ContinuousMap.HomotopyRel (independentBGLScalarPlusMap f) G
        {independentBGLCellPoint R}) ∧
      Nonempty (ContinuousMap.HomotopyRel G (independentBGLScalarPlusMap f)
        {independentBGLCellPoint R}) := by
  intro G hG
  let M := independentBGLCellNativePointModelOfRing.{uR, uS, 0} R
  let E := independentBGLScalarNativeExtensionDataOfHom.{uR, uS, 0, 0} f
  let a := independentBGLCellTargetUp.{uR, uS} R
  let r := M.equiv.invFun.comp a
  let d := independentBGLCellTargetDown.{uS, uR} S
  have hr : r (independentBGLCellPoint R) = M.point :=
    (congrArg M.equiv.invFun (independentBGLCellTargetUp_point.{uR, uS} R)).trans M.backwardPoint
  have hTriangle := liftOriginalCellCandidate_triangle f G hG.some
  obtain ⟨hForward, hBackward⟩ := E.unique (liftOriginalCellCandidate G) ⟨hTriangle⟩
  let K := (hForward.some.precomposePointRelative r
    (independentBGLCellPoint R) hr).compContinuousMap d
  let L := (hBackward.some.precomposePointRelative r
    (independentBGLCellPoint R) hr).compContinuousMap d
  let K' : ContinuousMap.HomotopyRel (independentBGLScalarPlusMap f)
      (d.comp ((liftOriginalCellCandidate G).hom.comp r)) {independentBGLCellPoint R} :=
    K.cast (by apply ContinuousMap.ext; intro x; rfl) (by apply ContinuousMap.ext; intro x; rfl)
  let L' : ContinuousMap.HomotopyRel (d.comp ((liftOriginalCellCandidate G).hom.comp r))
      (independentBGLScalarPlusMap f) {independentBGLCellPoint R} :=
    L.cast (by apply ContinuousMap.ext; intro x; rfl) (by apply ContinuousMap.ext; intro x; rfl)
  let C := cancelOriginalCellCandidate G
  exact ⟨⟨K'.trans C⟩, ⟨C.symm.trans L'⟩⟩


/-- The actual scalar plus map and its actual BGL source map induce the same based π₁ square. -/
public theorem independentBGLScalarPlusMap_fundamentalSquare (f : R →+* S) :
    (FundamentalGroup.mapOfEq (independentBGLScalarPlusMap f)
      (independentBGLScalarPlusMap_point f)).comp
        (FundamentalGroup.mapOfEq (independentBGLCellInclusion R).hom
          (independentBGLCellInclusion_point R)) =
      (FundamentalGroup.mapOfEq (independentBGLCellInclusion S).hom
        (independentBGLCellInclusion_point S)).comp
          (FundamentalGroup.mapOfEq (ordinaryBGLScalarMap f) (ordinaryBGLScalarMap_point f)) := by
  let x := ordinaryBGLBasepoint R
  let y := independentBGLCellPoint S
  let i := (independentBGLCellInclusion R).hom
  let j := (independentBGLCellInclusion S).hom
  let a := independentBGLScalarPlusMap f
  let b := ordinaryBGLScalarMap f
  have ha : (a.comp i) x = y :=
    (congrArg a (independentBGLCellInclusion_point R)).trans (independentBGLScalarPlusMap_point f)
  have hb : (j.comp b) x = y :=
    (congrArg j (ordinaryBGLScalarMap_point f)).trans (independentBGLCellInclusion_point S)
  let H := (independentBGLScalarPlusMap_triangle f).some
  have hTrace : ((H.toHomotopy.evalAt x).cast ha.symm hb.symm) = Path.refl y := by
    apply Path.ext
    funext t
    change H (t, x) = y
    exact (H.eq_fst t (Set.mem_singleton x)).trans ha
  have hMaps : FundamentalGroup.mapOfEq (a.comp i) ha =
      FundamentalGroup.mapOfEq (j.comp b) hb := by
    apply MonoidHom.ext
    intro p
    have hn := FundamentalGroup.mapOfEq_homotopy_naturality H.toHomotopy x ha hb p
    rw [hTrace, FundamentalGroup.fundamentalGroupMulEquivOfPath_refl] at hn
    exact hn
  have hLeft := FundamentalGroup.mapOfEq_comp i a
    (independentBGLCellInclusion_point R) (independentBGLScalarPlusMap_point f) ha
  have hRight := FundamentalGroup.mapOfEq_comp b j
    (ordinaryBGLScalarMap_point f) (independentBGLCellInclusion_point S) hb
  exact hLeft.symm.trans (hMaps.trans hRight)

end AlgebraicKTheory.StableGL

end
