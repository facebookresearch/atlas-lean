/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.Comparison.QuillenIndependentPlus
public import MathlibExt.KTheory.Exact.Quillen.UniverseLift
public import MathlibExt.KTheory.Exact.Quillen.UniverseLiftCGWH
public import MathlibExt.KTheory.Exact.Extension.OriginalQK0UniverseLiftCompatibility
public import MathlibExt.KTheory.Ring.StableGeneralLinear.IndependentPlusUniverseLift
public import MathlibExt.Topology.Homotopy.PointRelativeComposition

/-!
# Actual transported Q-plus maps and both global relative inverse families

The ring-only concrete comparison is constructed internally. Its actual maps
are composed with the actual category/native Q maps and the canonical carrier
maps of the same independent cell target. The fixed RingK0 factor is unchanged.

These are concrete construction APIs, including the lifted-category K0
square. The final public statement uses the genuine native
probe bundle on the actual Quillen realization before taking raw loops.
-/

noncomputable section

open CategoryTheory Topology TopologicalSpace
open scoped ContinuousMap

universe uR uM uObj uHom uNative uProbe

namespace AlgebraicKTheory.QuillenPlus.UniverseAssembly

variable (R : Type uR) [Ring R]

/-- The fixed unlifted K0 factor retains its original discrete topology. -/
private local instance fixedRingK0Topology : TopologicalSpace (RingK0 R) :=
  (RingK0.discreteSpace R).str

private abbrev coreCategory := FGProjectiveCat.{max uR uM} R
private abbrev coreSource := BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max uR uM} R)
private abbrev corePoint := BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR uM} R)
private abbrev coreNative := RingK0.projectiveOriginalSpace.{uR, uM, uProbe} R
private abbrev coreNativePoint := RingK0.projectiveOriginalPoint.{uR, uM, uProbe} R
private abbrev coreZero := RingK0.projectiveZeroSpace.{uR, uM, uProbe} R
private abbrev coreZeroPoint := RingK0.projectiveZeroPoint.{uR, uM, uProbe} R
private abbrev corePlus := StableGL.independentBGLCellTarget R
private abbrev corePlusPoint := StableGL.independentBGLCellPoint R
private abbrev coreTarget := independentPlusProduct R
private def coreTargetPoint : coreTarget.{uR} R := (0, corePlusPoint.{uR} R)

/-- Actual core outputs, obtained from the ring theorem rather than given by a caller. -/
private structure CoreRingData where
  d : coreSource.{uR, uM} R ≃ₕ coreNative.{uR, uM, uProbe} R
  dForward : d.toFun = projectiveQLoopToNativePair.{uR, uM, uProbe} R
  dPoint : d.toFun (corePoint.{uR, uM} R) = coreNativePoint.{uR, uM, uProbe} R
  dInversePoint : d.invFun (coreNativePoint.{uR, uM, uProbe} R) = corePoint.{uR, uM} R
  dLeft : ContinuousMap.HomotopyRel (d.invFun.comp d.toFun)
    (ContinuousMap.id (coreSource.{uR, uM} R)) {corePoint.{uR, uM} R}
  dRight : ContinuousMap.HomotopyRel (d.toFun.comp d.invFun)
    (ContinuousMap.id (coreNative.{uR, uM, uProbe} R)) {coreNativePoint.{uR, uM, uProbe} R}
  a : coreZero.{uR, uM, uProbe} R ≃ₕ corePlus.{uR} R
  aPoint : a.toFun (coreZeroPoint.{uR, uM, uProbe} R) = corePlusPoint.{uR} R
  aInversePoint : a.invFun (corePlusPoint.{uR} R) = coreZeroPoint.{uR, uM, uProbe} R
  aLeft : ContinuousMap.HomotopyRel (a.invFun.comp a.toFun)
    (ContinuousMap.id (coreZero.{uR, uM, uProbe} R)) {coreZeroPoint.{uR, uM, uProbe} R}
  aRight : ContinuousMap.HomotopyRel (a.toFun.comp a.invFun)
    (ContinuousMap.id (corePlus.{uR} R)) {corePlusPoint.{uR} R}
  e : coreSource.{uR, uM} R ≃ₕ coreTarget.{uR} R
  eForward : e.toFun = ((ContinuousMap.id (RingK0 R)).prodMap a.toFun).comp
    ((RingK0.projectiveProductForward.{uR, uM, uProbe} R).comp
      (projectiveQLoopToNativePair.{uR, uM, uProbe} R))
  eInverse : e.invFun = d.invFun.comp ((RingK0.projectiveProductInverse.{uR, uM, uProbe} R).comp
    ((ContinuousMap.id (RingK0 R)).prodMap a.invFun))
  ePoint : e.toFun (corePoint.{uR, uM} R) = coreTargetPoint.{uR} R
  eInversePoint : e.invFun (coreTargetPoint.{uR} R) = corePoint.{uR, uM} R
  eLeft : ContinuousMap.HomotopyRel (e.invFun.comp e.toFun)
    (ContinuousMap.id (coreSource.{uR, uM} R)) {corePoint.{uR, uM} R}
  eRight : ContinuousMap.HomotopyRel (e.toFun.comp e.invFun)
    (ContinuousMap.id (coreTarget.{uR} R)) {coreTargetPoint.{uR} R}
  canonicalK0 : ∀ x : coreSource.{uR, uM} R, (e.toFun x).1 =
    RingK0.projectiveUniverseEquiv.{uR, uM} R
      (OriginalQK0Comparison.canonicalLoopComponentsK0 (C := FGProjectiveCat.{max uR uM} R)
        (ZerothHomotopy.mk x))

private theorem coreRingData_nonempty : Nonempty (CoreRingData.{uR, uM, uProbe} R) := by
  obtain ⟨d, hdF, hdq, hdn, ⟨LD⟩, ⟨RD⟩,
    a, haz, hab, ⟨LA⟩, ⟨RA⟩,
    e, hF, hI, heq, het, ⟨L⟩, ⟨S⟩, hK⟩ :=
      quillenIndependentPlusEquivalence_canonicalK0_exists.{uR, uM, uProbe} R
  exact ⟨⟨d, hdF, hdq, hdn, LD, RD, a, haz, hab, LA, RA,
    e, hF, hI, heq, het, L, S, hK⟩⟩

private def coreRingData : CoreRingData.{uR, uM, uProbe} R :=
  Classical.choice (coreRingData_nonempty.{uR, uM, uProbe} R)

/-- Raw loops of the actual independently lifted projective category's Q construction. -/
public abbrev sourceSpace : TopCat.{max uNative
    (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom))} :=
  TopCat.of (QuillenUniverseLift.nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R)

/-- The literal constant loop at the actual lifted Q-zero vertex. -/
public abbrev sourcePoint : sourceSpace.{uR, uM, uObj, uHom, uNative} R :=
  QuillenUniverseLift.nativeConstantLoop.{uR, uM, uObj, uHom, uNative} R

/-- The same independently constructed original cell plus in the actual native carrier. -/
public abbrev plusSpace : TopCat.{max uNative
    (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom))} :=
  StableGL.independentBGLCellTargetLift.{uR, max uNative
    (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom))} R

/-- The lifted original cell point. -/
public abbrev plusPoint : plusSpace.{uR, uM, uObj, uHom, uNative} R :=
  StableGL.independentBGLCellPointLift.{uR, max uNative
    (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom))} R

/-- All fixed K0 classes times the actual lifted independent plus target. -/
public abbrev targetSpace : TopCat.{max uNative
    (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom))} :=
  letI : TopologicalSpace (RingK0 R) := (RingK0.discreteSpace R).str
  TopCat.of (RingK0 R × plusSpace.{uR, uM, uObj, uHom, uNative} R)

/-- The target uses its bundled topology for the product with the fixed K0 factor. -/
public local instance targetSpaceTopology : TopologicalSpace
    (targetSpace.{uR, uM, uObj, uHom, uNative} R) :=
  (targetSpace.{uR, uM, uObj, uHom, uNative} R).str

/-- The original zero label and lifted original cell point. -/
public def targetPoint : targetSpace.{uR, uM, uObj, uHom, uNative} R :=
  (0, plusPoint.{uR, uM, uObj, uHom, uNative} R)

private def namedPlusLeft :
    ContinuousMap.HomotopyRel
      ((StableGL.independentBGLCellTargetDown.{uR, max uNative
        (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom))} R).comp
        (StableGL.independentBGLCellTargetUp.{uR, max uNative
          (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom))} R))
      (ContinuousMap.id (corePlus.{uR} R)) {corePlusPoint.{uR} R} :=
  (ContinuousMap.HomotopyRel.refl (ContinuousMap.id (corePlus.{uR} R)) {corePlusPoint.{uR} R}).cast
    (StableGL.independentBGLCellTargetDown_comp_up.{uR, max uNative
      (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom))} R).symm rfl

private def namedPlusRight :
    ContinuousMap.HomotopyRel
      ((StableGL.independentBGLCellTargetUp.{uR, max uNative
        (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom))} R).comp
        (StableGL.independentBGLCellTargetDown.{uR, max uNative
          (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom))} R))
      (ContinuousMap.id (plusSpace.{uR, uM, uObj, uHom, uNative} R))
      {plusPoint.{uR, uM, uObj, uHom, uNative} R} :=
  (ContinuousMap.HomotopyRel.refl
    (ContinuousMap.id (plusSpace.{uR, uM, uObj, uHom, uNative} R)) {plusPoint.{uR, uM, uObj, uHom, uNative} R}).cast
    (StableGL.independentBGLCellTargetUp_comp_down.{uR, max uNative
      (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom))} R).symm rfl

/-- The same canonical carrier maps, with inverse families from their strict compositions. -/
private def namedPlusEquivalence : corePlus.{uR} R ≃ₕ
    plusSpace.{uR, uM, uObj, uHom, uNative} R where
  toFun := StableGL.independentBGLCellTargetUp.{uR, max uNative
    (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom))} R
  invFun := StableGL.independentBGLCellTargetDown.{uR, max uNative
    (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom))} R
  left_inv := ⟨(namedPlusLeft.{uR, uM, uObj, uHom, uNative} R).toHomotopy⟩
  right_inv := ⟨(namedPlusRight.{uR, uM, uObj, uHom, uNative} R).toHomotopy⟩

private def targetCarrierEquivalence : coreTarget.{uR} R ≃ₕ
    targetSpace.{uR, uM, uObj, uHom, uNative} R :=
  (ContinuousMap.HomotopyEquiv.refl (RingK0 R)).prodCongr
    (namedPlusEquivalence.{uR, uM, uObj, uHom, uNative} R)

/-- The accepted literal Q maps and both whole relative families give this internal factor. -/
private def namedQEquivalence : sourceSpace.{uR, uM, uObj, uHom, uNative} R ≃ₕ
    coreSource.{uR, uM} R where
  toFun := QuillenUniverseLift.Qdown.{uR, uM, uObj, uHom, uNative} R
  invFun := QuillenUniverseLift.Qup.{uR, uM, uObj, uHom, uNative} R
  left_inv := ⟨(QuillenUniverseLift.QleftHomotopyRel.{uR, uM, uObj, uHom, uNative} R).toHomotopy⟩
  right_inv := ⟨(QuillenUniverseLift.QrightHomotopyRel.{uR, uM, uObj, uHom, uNative} R).toHomotopy⟩

private def transportedEquivalence : sourceSpace.{uR, uM, uObj, uHom, uNative} R ≃ₕ
    targetSpace.{uR, uM, uObj, uHom, uNative} R :=
  ((namedQEquivalence.{uR, uM, uObj, uHom, uNative} R).trans
    (coreRingData.{uR, uM, uProbe} R).e).trans
      (targetCarrierEquivalence.{uR, uM, uObj, uHom, uNative} R)

/-- The actual global forward composition; the fixed K0 coordinate is unchanged. -/
public def transportedForward :
    C(sourceSpace.{uR, uM, uObj, uHom, uNative} R,
      targetSpace.{uR, uM, uObj, uHom, uNative} R) := by
  let S := sourceSpace.{uR, uM, uObj, uHom, uNative} R
  let A := coreSource.{uR, uM} R
  let C := coreTarget.{uR} R
  let B0 := corePlus.{uR} R
  let B := plusSpace.{uR, uM, uObj, uHom, uNative} R
  let T := targetSpace.{uR, uM, uObj, uHom, uNative} R
  let d : TopologicalSpace (RingK0 R) := (RingK0.discreteSpace R).str
  let up := StableGL.independentBGLCellTargetUp.{uR,
    max uNative (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom))} R
  let p : @ContinuousMap C T C.str T.str :=
    @ContinuousMap.prodMap (RingK0 R) (RingK0 R) B0 B d d B0.str B.str
      (@ContinuousMap.id (RingK0 R) d) up
  exact @ContinuousMap.comp S C T S.str C.str T.str p
    (@ContinuousMap.comp S A C S.str A.str C.str
      (coreRingData.{uR, uM, uProbe} R).e.toFun
      (QuillenUniverseLift.Qdown.{uR, uM, uObj, uHom, uNative} R))

/-- The actual global inverse composition through the original core inverse. -/
public def transportedInverse :
    C(targetSpace.{uR, uM, uObj, uHom, uNative} R,
      sourceSpace.{uR, uM, uObj, uHom, uNative} R) := by
  let S := sourceSpace.{uR, uM, uObj, uHom, uNative} R
  let A := coreSource.{uR, uM} R
  let C := coreTarget.{uR} R
  let B0 := corePlus.{uR} R
  let B := plusSpace.{uR, uM, uObj, uHom, uNative} R
  let T := targetSpace.{uR, uM, uObj, uHom, uNative} R
  let d : TopologicalSpace (RingK0 R) := (RingK0.discreteSpace R).str
  let down := StableGL.independentBGLCellTargetDown.{uR,
    max uNative (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom))} R
  let p : @ContinuousMap T C T.str C.str :=
    @ContinuousMap.prodMap (RingK0 R) (RingK0 R) B B0 d d B.str B0.str
      (@ContinuousMap.id (RingK0 R) d) down
  exact @ContinuousMap.comp T A S T.str A.str S.str
    (QuillenUniverseLift.Qup.{uR, uM, uObj, uHom, uNative} R)
    (@ContinuousMap.comp T C A T.str C.str A.str
      (coreRingData.{uR, uM, uProbe} R).e.invFun p)

private theorem transportedEquivalence_toFun :
    (transportedEquivalence.{uR, uM, uObj, uHom, uNative, uProbe} R).toFun =
      transportedForward.{uR, uM, uObj, uHom, uNative, uProbe} R := by
  apply ContinuousMap.ext
  intro x
  rfl

private theorem transportedEquivalence_invFun :
    (transportedEquivalence.{uR, uM, uObj, uHom, uNative, uProbe} R).invFun =
      transportedInverse.{uR, uM, uObj, uHom, uNative, uProbe} R := by
  apply ContinuousMap.ext
  intro x
  rfl

/-- The forward preserves the actual original constant-loop point strictly. -/
public theorem transportedForward_point :
    transportedForward.{uR, uM, uObj, uHom, uNative, uProbe} R
        (sourcePoint.{uR, uM, uObj, uHom, uNative} R) =
      targetPoint.{uR, uM, uObj, uHom, uNative} R := by
  change ((ContinuousMap.id (RingK0 R)).prodMap
    (StableGL.independentBGLCellTargetUp.{uR, max uNative
      (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom))} R))
    ((coreRingData.{uR, uM, uProbe} R).e.toFun
      (QuillenUniverseLift.Qdown.{uR, uM, uObj, uHom, uNative} R
        (sourcePoint.{uR, uM, uObj, uHom, uNative} R))) =
      (0, plusPoint.{uR, uM, uObj, uHom, uNative} R)
  rw [QuillenUniverseLift.Qdown_constant.{uR, uM, uObj, uHom, uNative} R, (coreRingData.{uR, uM, uProbe} R).ePoint]
  exact Prod.ext rfl (StableGL.independentBGLCellTargetUp_point.{uR,
    max uNative (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom))} R)

/-- The inverse preserves the original zero-labelled cell point strictly. -/
private theorem transportedInversePointComputed :
    transportedInverse.{uR, uM, uObj, uHom, uNative, uProbe} R
        (targetPoint.{uR, uM, uObj, uHom, uNative} R) =
      sourcePoint.{uR, uM, uObj, uHom, uNative} R := by
  change QuillenUniverseLift.Qup.{uR, uM, uObj, uHom, uNative} R
    ((coreRingData.{uR, uM, uProbe} R).e.invFun
      (0, StableGL.independentBGLCellTargetDown.{uR,
        max uNative (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom))} R
        (plusPoint.{uR, uM, uObj, uHom, uNative} R))) = _
  rw [StableGL.independentBGLCellTargetDown_point.{uR,
    max uNative (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom))} R]
  have hp : ((0 : RingK0 R), StableGL.independentBGLCellPoint R) =
      coreTargetPoint.{uR} R := rfl
  have hCore : (coreRingData.{uR, uM, uProbe} R).e.invFun
      ((0 : RingK0 R), StableGL.independentBGLCellPoint R) =
      corePoint.{uR, uM} R :=
    (congrArg (coreRingData.{uR, uM, uProbe} R).e.invFun hp).trans
      (coreRingData.{uR, uM, uProbe} R).eInversePoint
  exact (congrArg (QuillenUniverseLift.Qup.{uR, uM, uObj, uHom, uNative} R)
    hCore).trans (QuillenUniverseLift.Qup_constant.{uR, uM, uObj, uHom, uNative} R)

public theorem transportedInverse_point :
    transportedInverse.{uR, uM, uObj, uHom, uNative, uProbe} R
        (targetPoint.{uR, uM, uObj, uHom, uNative} R) =
      sourcePoint.{uR, uM, uObj, uHom, uNative} R := by
  exact transportedInversePointComputed.{uR, uM, uObj, uHom, uNative, uProbe} R

private def targetCarrierLeft :
    ContinuousMap.HomotopyRel
      ((targetCarrierEquivalence.{uR, uM, uObj, uHom, uNative} R).invFun.comp
        (targetCarrierEquivalence.{uR, uM, uObj, uHom, uNative} R).toFun)
      (ContinuousMap.id (coreTarget.{uR} R)) {coreTargetPoint.{uR} R} := by
  let K := ContinuousMap.HomotopyEquiv.refl (RingK0 R)
  let B := (namedPlusEquivalence.{uR, uM, uObj, uHom, uNative} R)
  let LK : ContinuousMap.HomotopyRel (K.invFun.comp K.toFun)
      (ContinuousMap.id (RingK0 R)) {(0 : RingK0 R)} :=
    (ContinuousMap.HomotopyRel.refl (ContinuousMap.id (RingK0 R)) {0}).cast
      (by apply ContinuousMap.ext; intro x; rfl) rfl
  let LB : ContinuousMap.HomotopyRel (B.invFun.comp B.toFun)
      (ContinuousMap.id (corePlus.{uR} R)) {corePlusPoint.{uR} R} :=
    namedPlusLeft.{uR, uM, uObj, uHom, uNative} R
  exact K.prodCongrLeftHomotopyRel B 0 (corePlusPoint.{uR} R) LK LB

private def targetCarrierRight :
    ContinuousMap.HomotopyRel
      ((targetCarrierEquivalence.{uR, uM, uObj, uHom, uNative} R).toFun.comp
        (targetCarrierEquivalence.{uR, uM, uObj, uHom, uNative} R).invFun)
      (ContinuousMap.id (targetSpace.{uR, uM, uObj, uHom, uNative} R))
      {targetPoint.{uR, uM, uObj, uHom, uNative} R} := by
  let K := ContinuousMap.HomotopyEquiv.refl (RingK0 R)
  let B := (namedPlusEquivalence.{uR, uM, uObj, uHom, uNative} R)
  let RK : ContinuousMap.HomotopyRel (K.toFun.comp K.invFun)
      (ContinuousMap.id (RingK0 R)) {(0 : RingK0 R)} :=
    (ContinuousMap.HomotopyRel.refl (ContinuousMap.id (RingK0 R)) {0}).cast
      (by apply ContinuousMap.ext; intro x; rfl) rfl
  let RB : ContinuousMap.HomotopyRel (B.toFun.comp B.invFun)
      (ContinuousMap.id (plusSpace.{uR, uM, uObj, uHom, uNative} R)) {plusPoint.{uR, uM, uObj, uHom, uNative} R} :=
    namedPlusRight.{uR, uM, uObj, uHom, uNative} R
  exact K.prodCongrRightHomotopyRel B 0 (plusPoint.{uR, uM, uObj, uHom, uNative} R) RK RB

/-- Both actual maps compose to the identity through a whole-source point-relative family. -/
public def transportedLeftHomotopyRel :
    ContinuousMap.HomotopyRel
      ((transportedInverse.{uR, uM, uObj, uHom, uNative, uProbe} R).comp
        (transportedForward.{uR, uM, uObj, uHom, uNative, uProbe} R))
      (ContinuousMap.id (sourceSpace.{uR, uM, uObj, uHom, uNative} R))
      {sourcePoint.{uR, uM, uObj, uHom, uNative} R} := by
  let Q := namedQEquivalence.{uR, uM, uObj, uHom, uNative} R
  let E := (coreRingData.{uR, uM, uProbe} R).e
  let T := targetCarrierEquivalence.{uR, uM, uObj, uHom, uNative} R
  let LQ0 := Q.transLeftHomotopyRel E (sourcePoint.{uR, uM, uObj, uHom, uNative} R) (corePoint.{uR, uM} R)
    (QuillenUniverseLift.Qdown_constant.{uR, uM, uObj, uHom, uNative} R)
    (QuillenUniverseLift.QleftHomotopyRel.{uR, uM, uObj, uHom, uNative} R)
    (coreRingData.{uR, uM, uProbe} R).eLeft
  have hQ0 : (Q.trans E).toFun (sourcePoint.{uR, uM, uObj, uHom, uNative} R) = coreTargetPoint.{uR} R :=
    (congrArg E.toFun (QuillenUniverseLift.Qdown_constant.{uR, uM, uObj, uHom, uNative} R)).trans
      (coreRingData.{uR, uM, uProbe} R).ePoint
  let L := (Q.trans E).transLeftHomotopyRel T (sourcePoint.{uR, uM, uObj, uHom, uNative} R) (coreTargetPoint.{uR} R)
    hQ0 LQ0 (targetCarrierLeft.{uR, uM, uObj, uHom, uNative} R)
  exact L.cast
    (congrArg₂ (fun (g : C(targetSpace.{uR, uM, uObj, uHom, uNative} R, sourceSpace.{uR, uM, uObj, uHom, uNative} R))
      (f : C(sourceSpace.{uR, uM, uObj, uHom, uNative} R, targetSpace.{uR, uM, uObj, uHom, uNative} R)) =>
      g.comp f) (transportedEquivalence_invFun.{uR, uM, uObj, uHom, uNative, uProbe} R)
      (transportedEquivalence_toFun.{uR, uM, uObj, uHom, uNative, uProbe} R)) rfl

/-- Both actual maps compose to the identity through a whole-target point-relative family. -/
public def transportedRightHomotopyRel :
    ContinuousMap.HomotopyRel
      ((transportedForward.{uR, uM, uObj, uHom, uNative, uProbe} R).comp
        (transportedInverse.{uR, uM, uObj, uHom, uNative, uProbe} R))
      (ContinuousMap.id (targetSpace.{uR, uM, uObj, uHom, uNative} R))
      {targetPoint.{uR, uM, uObj, uHom, uNative} R} := by
  let Q := namedQEquivalence.{uR, uM, uObj, uHom, uNative} R
  let E := (coreRingData.{uR, uM, uProbe} R).e
  let T := targetCarrierEquivalence.{uR, uM, uObj, uHom, uNative} R
  let RQ0 := Q.transRightHomotopyRel E (corePoint.{uR, uM} R) (coreTargetPoint.{uR} R)
    (coreRingData.{uR, uM, uProbe} R).eInversePoint
    (QuillenUniverseLift.QrightHomotopyRel.{uR, uM, uObj, uHom, uNative} R)
    (coreRingData.{uR, uM, uProbe} R).eRight
  have hTI : T.invFun (targetPoint.{uR, uM, uObj, uHom, uNative} R) = coreTargetPoint.{uR} R :=
    Prod.ext rfl (StableGL.independentBGLCellTargetDown_point.{uR,
      max uNative (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom))} R)
  let S := (Q.trans E).transRightHomotopyRel T (coreTargetPoint.{uR} R) (targetPoint.{uR, uM, uObj, uHom, uNative} R)
    hTI RQ0 (targetCarrierRight.{uR, uM, uObj, uHom, uNative} R)
  exact S.cast
    (congrArg₂ (fun (f : C(sourceSpace.{uR, uM, uObj, uHom, uNative} R, targetSpace.{uR, uM, uObj, uHom, uNative} R))
      (g : C(targetSpace.{uR, uM, uObj, uHom, uNative} R, sourceSpace.{uR, uM, uObj, uHom, uNative} R)) =>
      f.comp g) (transportedEquivalence_toFun.{uR, uM, uObj, uHom, uNative, uProbe} R)
      (transportedEquivalence_invFun.{uR, uM, uObj, uHom, uNative, uProbe} R)) rfl

/-- The constructed first coordinate has the original canonical module-category value. -/
public theorem transportedForward_first_eq_coreK0
    (x : sourceSpace.{uR, uM, uObj, uHom, uNative} R) :
    (transportedForward.{uR, uM, uObj, uHom, uNative, uProbe} R x).1 =
      RingK0.projectiveUniverseEquiv.{uR, uM} R
        (OriginalQK0Comparison.canonicalLoopComponentsK0 (C := FGProjectiveCat.{max uR uM} R)
          (ZerothHomotopy.mk (QuillenUniverseLift.Qdown.{uR, uM, uObj, uHom, uNative} R x))) := by
  exact (coreRingData.{uR, uM, uProbe} R).canonicalK0
    (QuillenUniverseLift.Qdown.{uR, uM, uObj, uHom, uNative} R x)

/-- Every source loop retains the independent original lifted-category Q/S label. -/
public theorem transportedForward_first_eq_canonicalK0
    (x : sourceSpace.{uR, uM, uObj, uHom, uNative} R) :
    (transportedForward.{uR, uM, uObj, uHom, uNative, uProbe} R x).1 =
      OriginalQK0UniverseLiftCompatibility.nativeLoopFixedK0.{uR, uM, uObj, uHom, uNative} R x := by
  exact ((transportedForward_first_eq_coreK0.{uR, uM, uObj, uHom, uNative, uProbe} R x).trans
    (OriginalQK0UniverseLiftCompatibility.Qdown_canonicalEvaluator.{uR, uM, uObj, uHom, uNative} R x)).trans
      (OriginalQK0UniverseLiftCompatibility.nativeLoopFixedK0_formula.{uR, uM, uObj, uHom, uNative} R x).symm

/-- Every fixed original K0 label occurs in the first coordinate of the actual map. -/
public theorem transportedForward_every_class (k : RingK0 R) :
    ∃ x : sourceSpace.{uR, uM, uObj, uHom, uNative} R,
      (transportedForward.{uR, uM, uObj, uHom, uNative, uProbe} R x).1 = k := by
  obtain ⟨x, hx⟩ :=
    OriginalQK0UniverseLiftCompatibility.nativeLoopFixedK0_surjective.{uR, uM, uObj, uHom, uNative} R k
  exact ⟨x, (transportedForward_first_eq_canonicalK0.{uR, uM, uObj, uHom, uNative, uProbe} R x).trans hx⟩

/-- The concrete internally constructed equivalence has exactly the actual transported maps. -/
public def transportedHomotopyEquiv :
    sourceSpace.{uR, uM, uObj, uHom, uNative} R ≃ₕ
      targetSpace.{uR, uM, uObj, uHom, uNative} R where
  toFun := transportedForward.{uR, uM, uObj, uHom, uNative, uProbe} R
  invFun := transportedInverse.{uR, uM, uObj, uHom, uNative, uProbe} R
  left_inv := ⟨(transportedLeftHomotopyRel.{uR, uM, uObj, uHom, uNative, uProbe} R).toHomotopy⟩
  right_inv := ⟨(transportedRightHomotopyRel.{uR, uM, uObj, uHom, uNative, uProbe} R).toHomotopy⟩

private theorem transportedHomotopyEquivForwardComputed :
    (transportedHomotopyEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R).toFun =
      transportedForward.{uR, uM, uObj, uHom, uNative, uProbe} R := by
  rfl

private theorem transportedHomotopyEquivInverseComputed :
    (transportedHomotopyEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R).invFun =
      transportedInverse.{uR, uM, uObj, uHom, uNative, uProbe} R := by
  rfl

/-- Every source value uses the same explicit Q/core/plus forward composition. -/
public theorem transportedHomotopyEquiv_toFun :
    (transportedHomotopyEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R).toFun =
      transportedForward.{uR, uM, uObj, uHom, uNative, uProbe} R := by
  exact transportedHomotopyEquivForwardComputed.{uR, uM, uObj, uHom, uNative, uProbe} R

/-- Every target value uses the same explicit plus/core/Q inverse composition. -/
public theorem transportedHomotopyEquiv_invFun :
    (transportedHomotopyEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R).invFun =
      transportedInverse.{uR, uM, uObj, uHom, uNative, uProbe} R := by
  exact transportedHomotopyEquivInverseComputed.{uR, uM, uObj, uHom, uNative, uProbe} R

/-- The actual Quillen realization has an independently sized compact-probe bundle. -/
public abbrev sourceRealizationBundle :
    CGWH.{uProbe, max uNative
      (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom))} :=
  QuillenUniverseLift.nativeQuillenRealizationBundle.{uR, uM, uObj, uHom, uNative, uProbe} R

/-- The genuine bundle uses the original carrier-lifted Q-zero vertex. -/
public abbrev sourceRealizationBundlePoint :
    sourceRealizationBundle.{uR, uM, uObj, uHom, uNative, uProbe} R :=
  QuillenUniverseLift.nativeQuillenRealizationBundlePoint.{uR, uM, uObj, uHom, uNative, uProbe} R

/-- Raw loops are taken on the actual CGWH bundle's underlying Quillen realization. -/
public abbrev sourceSpaceWithProbe : TopCat.{max uNative
    (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom))} :=
  TopCat.of (LoopSpace
    (sourceRealizationBundle.{uR, uM, uObj, uHom, uNative, uProbe} R).toTop
    (sourceRealizationBundlePoint.{uR, uM, uObj, uHom, uNative, uProbe} R))

/-- The actual native constant loop is retained with the genuine probe bundle. -/
public abbrev sourcePointWithProbe :
    sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R :=
  Path.refl (sourceRealizationBundlePoint.{uR, uM, uObj, uHom, uNative, uProbe} R)

/-- Bundling genuine probe data changes no raw-loop carrier or topology. -/
public theorem sourceSpaceWithProbe_eq :
    sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R =
      sourceSpace.{uR, uM, uObj, uHom, uNative} R := rfl

/-- Bundling genuine probe data changes no original constant loop. -/
public theorem sourcePointWithProbe_eq :
    sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R =
      sourcePoint.{uR, uM, uObj, uHom, uNative} R :=
  QuillenUniverseLift.nativeQuillenRealizationBundle_constantLoop_eq.{uR, uM, uObj, uHom, uNative, uProbe} R

end AlgebraicKTheory.QuillenPlus.UniverseAssembly

namespace AlgebraicKTheory.QuillenPlus

open UniverseAssembly

attribute [local instance]
  AlgebraicKTheory.OriginalQK0UniverseLiftCompatibility.categoryUniverseSymmFunctorAdditive
  AlgebraicKTheory.OriginalQK0UniverseLiftCompatibility.categoryUniverseSymmInverseAdditive
  AlgebraicKTheory.OriginalQK0UniverseLiftCompatibility.categoryUniverseSymmFunctorIsExact
  AlgebraicKTheory.OriginalQK0UniverseLiftCompatibility.categoryUniverseSymmInverseIsExact

/-- The full original Q=plus comparison with six genuine independent universe roles.
The source is the raw loop space of the actual Quillen construction of the
independently lifted projective category, at its literal lifted zero vertex.
Its native realization carries actual compact-probe data at the independently
chosen probe level. The target retains every unlifted original RingK0 label and
the actual carrier lift of the same independently constructed two/three-cell
plus. Both global maps are the named actual compositions, both inverse families
are singleton-relative at the original points, and the first coordinate is the
independent original Q/S evaluator of the lifted category at every source loop.
Only the ring and universe choices are outer data. -/
public theorem quillenIndependentPlusEquivalence_allUniverses_canonicalK0_exists
    (R : Type uR) [Ring R] :
    letI : TopologicalSpace (RingK0 R) := (RingK0.discreteSpace R).str
    let X := sourceRealizationBundle.{uR, uM, uObj, uHom, uNative, uProbe} R
    let x0 := sourceRealizationBundlePoint.{uR, uM, uObj, uHom, uNative, uProbe} R
    let Q := TopCat.of (LoopSpace X.toTop x0)
    let q : Q := Path.refl x0
    let B := plusSpace.{uR, uM, uObj, uHom, uNative} R
    let b := plusPoint.{uR, uM, uObj, uHom, uNative} R
    let T := TopCat.of (RingK0 R × B)
    let t : T := (0, b)
    UCompactlyGeneratedSpace.{uProbe} X ∧ UWeakHausdorffSpace.{uProbe} X ∧
      ∃ e : Q ≃ₕ T,
        e.toFun = transportedForward.{uR, uM, uObj, uHom, uNative, uProbe} R ∧
        e.invFun = transportedInverse.{uR, uM, uObj, uHom, uNative, uProbe} R ∧
        e.toFun q = t ∧ e.invFun t = q ∧
        Nonempty (ContinuousMap.HomotopyRel (e.invFun.comp e.toFun) (ContinuousMap.id Q) {q}) ∧
        Nonempty (ContinuousMap.HomotopyRel (e.toFun.comp e.invFun) (ContinuousMap.id T) {t}) ∧
        (∀ x : Q, (e.toFun x).1 =
          OriginalQK0UniverseLiftCompatibility.nativeLoopFixedK0.{uR, uM, uObj, uHom, uNative} R x) ∧
        (∀ x : Q, (e.toFun x).1 =
          RingK0.projectiveUniverseEquiv.{uR, uM} R
            (K0.equivOfEquivalence
              (FGProjectiveCat.CategoryUniverseLift.equivalence.{uR, uM, uObj, uHom} R).symm
              (OriginalQK0Comparison.canonicalLoopComponentsK0
                (C := FGProjectiveCat.CategoryUniverseLift.category.{uR, uM, uObj, uHom} R)
                (ZerothHomotopy.mk
                  (QuillenUniverseLift.rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R x))))) ∧
        (∀ k : RingK0 R, ∃ x : Q, (e.toFun x).1 = k) := by
  letI : TopologicalSpace (targetSpace.{uR, uM, uObj, uHom, uNative} R) :=
    UniverseAssembly.targetSpaceTopology.{uR, uM, uObj, uHom, uNative} R
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · exact QuillenUniverseLift.nativeQuillenRealization_uCompactlyGeneratedSpace.{uR, uM, uObj, uHom, uNative, uProbe} R
  · let _ : T2Space (QuillenUniverseLift.nativeRealization.{uR, uM, uObj, uHom, uNative} R) :=
      QuillenUniverseLift.nativeQuillenRealization_t2Space.{uR, uM, uObj, uHom, uNative} R
    exact uWeakHausdorffSpaceOfT2
      (QuillenUniverseLift.nativeRealization.{uR, uM, uObj, uHom, uNative} R)
  · have hq := sourcePointWithProbe_eq.{uR, uM, uObj, uHom, uNative, uProbe} R
    have hForward : transportedForward.{uR, uM, uObj, uHom, uNative, uProbe} R
        (sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R) = targetPoint.{uR, uM, uObj, uHom, uNative} R :=
      (congrArg (transportedForward.{uR, uM, uObj, uHom, uNative, uProbe} R) hq).trans
        (transportedForward_point.{uR, uM, uObj, uHom, uNative, uProbe} R)
    have hInverse : transportedInverse.{uR, uM, uObj, uHom, uNative, uProbe} R
        (targetPoint.{uR, uM, uObj, uHom, uNative} R) = sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R :=
      (transportedInverse_point.{uR, uM, uObj, uHom, uNative, uProbe} R).trans hq.symm
    let L : ContinuousMap.HomotopyRel
        ((transportedInverse.{uR, uM, uObj, uHom, uNative, uProbe} R).comp
          (transportedForward.{uR, uM, uObj, uHom, uNative, uProbe} R))
        (ContinuousMap.id (sourceSpaceWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R))
        {sourcePointWithProbe.{uR, uM, uObj, uHom, uNative, uProbe} R} :=
      Eq.mp (congrArg (fun point : sourceSpace.{uR, uM, uObj, uHom, uNative} R =>
        ContinuousMap.HomotopyRel
          ((transportedInverse.{uR, uM, uObj, uHom, uNative, uProbe} R).comp
            (transportedForward.{uR, uM, uObj, uHom, uNative, uProbe} R))
          (ContinuousMap.id (sourceSpace.{uR, uM, uObj, uHom, uNative} R)) {point}) hq.symm)
        (transportedLeftHomotopyRel.{uR, uM, uObj, uHom, uNative, uProbe} R)
    refine ⟨transportedHomotopyEquiv.{uR, uM, uObj, uHom, uNative, uProbe} R,
      transportedHomotopyEquiv_toFun.{uR, uM, uObj, uHom, uNative, uProbe} R,
      transportedHomotopyEquiv_invFun.{uR, uM, uObj, uHom, uNative, uProbe} R, hForward, hInverse,
      ⟨L⟩, ⟨transportedRightHomotopyRel.{uR, uM, uObj, uHom, uNative, uProbe} R⟩, ?_, ?_, ?_⟩
    · intro x
      exact transportedForward_first_eq_canonicalK0.{uR, uM, uObj, uHom, uNative, uProbe} R x
    · intro x
      exact (transportedForward_first_eq_canonicalK0.{uR, uM, uObj, uHom, uNative, uProbe} R x).trans
        (OriginalQK0UniverseLiftCompatibility.nativeLoopFixedK0_formula R x)
    · intro k
      exact transportedForward_every_class.{uR, uM, uObj, uHom, uNative, uProbe} R k

end AlgebraicKTheory.QuillenPlus

end
