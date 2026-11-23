/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.KTheory.Ring.StableGeneralLinear.NativeProjectiveZeroScalarNormalizedSourceComparison
public import MathlibExt.KTheory.Ring.StableGeneralLinear.BGLScalarPlusMap
public import MathlibExt.Topology.Homotopy.PointRelativeComposition

/-!
# Original independent plus scalar map and both normalized chart directions

The same six independent roles and both original normalization records are used.
The actual intrinsic source comparison derives the original BGL triangle for
its normalized conjugate. Both original plus universal comparison families are
selected together. All four original left/right families derive the normalized
map comparisons and both chart squares, with their reverse families.
-/

noncomputable section

open CategoryTheory
open scoped ContinuousMap

namespace AlgebraicKTheory.StableGL

private abbrev scalarOriginalNormalization.{uRing, uModule, uNative}
    (A : Type uRing) [Ring A] :
    NativeProjectiveZeroPlusNormalization.{uRing, uModule, uNative} A :=
  nativeProjectiveZeroPlusNormalizationOfRing.{uRing, uModule, uNative} A

/-- The actual normalized conjugate, retaining the two original plus targets. -/
public def nativeProjectiveZeroScalarOriginalConjugatePlusMap.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) : C(independentBGLCellTarget R, independentBGLCellTarget S) :=
  (scalarOriginalNormalization.{uS, uMS, uNS} S).equiv.toFun.comp
    ((nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f).comp
      (scalarOriginalNormalization.{uR, uMR, uNR} R).equiv.invFun)

/-- The conjugate retains the same two original marked cell points. -/
public theorem nativeProjectiveZeroScalarOriginalConjugatePlusMap_point.{
    uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) :
    nativeProjectiveZeroScalarOriginalConjugatePlusMap.{uR, uS, uMR, uMS, uNR, uNS} f
        (independentBGLCellPoint R) = independentBGLCellPoint S := by
  let A := scalarOriginalNormalization.{uR, uMR, uNR} R
  let B := scalarOriginalNormalization.{uS, uMS, uNS} S
  let psi := nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f
  exact (congrArg (fun x => B.equiv.toFun (psi x)) A.backwardPoint).trans
    ((congrArg B.equiv.toFun
      (nativeProjectiveZeroScalarMap_point.{uR, uS, uMR, uMS, uNR, uNS} f)).trans B.forwardPoint)

/-- The accepted source square and the same original source triangles derive
    the whole BGL triangle for this conjugate, relative to the original root. -/
public def nativeProjectiveZeroScalarOriginalConjugateSourceTriangle.{
    uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) :
    ContinuousMap.HomotopyRel
      ((nativeProjectiveZeroScalarOriginalConjugatePlusMap.{uR, uS, uMR, uMS, uNR, uNS} f).comp
        (independentBGLCellInclusion R).hom)
      ((independentBGLCellInclusion S).hom.comp (ordinaryBGLScalarMap f))
      {ordinaryBGLBasepoint R} := by
  let A := scalarOriginalNormalization.{uR, uMR, uNR} R
  let B := scalarOriginalNormalization.{uS, uMS, uNS} S
  let psi := nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f
  let G := nativeProjectiveZeroScalarOriginalConjugatePlusMap.{uR, uS, uMR, uMS, uNR, uNS} f
  let H := (nativeProjectiveZeroScalarNormalizedSourceComparison.{
    uR, uS, uMR, uMS, uNR, uNS} f).compContinuousMap B.equiv.toFun
  have hFirst : B.equiv.toFun.comp (psi.comp A.sourceMap) =
      G.comp (independentBGLCellInclusion R).hom := by
    apply ContinuousMap.ext
    intro x
    exact congrArg (fun z => B.equiv.toFun (psi z))
      (congrArg (fun q : C(ordinaryBGL R,
        RingK0.projectiveZeroSpace.{uR, uMR, uNR} R) => q x) A.inverseSourceTriangle).symm
  have hMiddle : B.equiv.toFun.comp (B.sourceMap.comp (ordinaryBGLScalarMap f)) =
      (B.equiv.toFun.comp B.sourceMap).comp (ordinaryBGLScalarMap f) := by
    apply ContinuousMap.ext
    intro x
    rfl
  let K := B.sourceTriangle.precomposePointRelative (ordinaryBGLScalarMap f)
    (ordinaryBGLBasepoint R) (ordinaryBGLScalarMap_point f)
  exact (H.cast hFirst hMiddle).trans K

private def scalarOriginalPlusComparisonPair.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) :
    ContinuousMap.HomotopyRel (independentBGLScalarPlusMap f)
        (nativeProjectiveZeroScalarOriginalConjugatePlusMap.{uR, uS, uMR, uMS, uNR, uNS} f)
        {independentBGLCellPoint R} ×
      ContinuousMap.HomotopyRel
        (nativeProjectiveZeroScalarOriginalConjugatePlusMap.{uR, uS, uMR, uMS, uNR, uNS} f)
        (independentBGLScalarPlusMap f) {independentBGLCellPoint R} :=
  let G := nativeProjectiveZeroScalarOriginalConjugatePlusMap.{uR, uS, uMR, uMS, uNR, uNS} f
  let U := independentBGLScalarPlusMap_universal.{uR, uS} f G
    ⟨nativeProjectiveZeroScalarOriginalConjugateSourceTriangle.{
      uR, uS, uMR, uMS, uNR, uNS} f⟩
  (U.1.some, U.2.some)

/-- The first whole ORIGINAL universal family: original plus map to conjugate. -/
public def nativeProjectiveZeroScalarOriginalPlusToConjugate.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) :
    ContinuousMap.HomotopyRel (independentBGLScalarPlusMap f)
      (nativeProjectiveZeroScalarOriginalConjugatePlusMap.{uR, uS, uMR, uMS, uNR, uNS} f)
      {independentBGLCellPoint R} :=
  (scalarOriginalPlusComparisonPair.{uR, uS, uMR, uMS, uNR, uNS} f).1

/-- The second whole ORIGINAL universal family: conjugate to original plus map. -/
public def nativeProjectiveZeroScalarOriginalConjugateToPlus.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) :
    ContinuousMap.HomotopyRel
      (nativeProjectiveZeroScalarOriginalConjugatePlusMap.{uR, uS, uMR, uMS, uNR, uNS} f)
      (independentBGLScalarPlusMap f) {independentBGLCellPoint R} :=
  (scalarOriginalPlusComparisonPair.{uR, uS, uMR, uMS, uNR, uNS} f).2

/-- The original plus map transported by the two original normalization charts. -/
public def nativeProjectiveZeroScalarOriginalNormalizedMap.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) :
    C(RingK0.projectiveZeroSpace.{uR, uMR, uNR} R,
      RingK0.projectiveZeroSpace.{uS, uMS, uNS} S) :=
  (scalarOriginalNormalization.{uS, uMS, uNS} S).equiv.invFun.comp
    ((independentBGLScalarPlusMap f).comp
      (scalarOriginalNormalization.{uR, uMR, uNR} R).equiv.toFun)

/-- The transported original plus map retains the original native zero points. -/
public theorem nativeProjectiveZeroScalarOriginalNormalizedMap_point.{
    uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) :
    nativeProjectiveZeroScalarOriginalNormalizedMap.{uR, uS, uMR, uMS, uNR, uNS} f
        (RingK0.projectiveZeroPoint.{uR, uMR, uNR} R) =
      RingK0.projectiveZeroPoint.{uS, uMS, uNS} S := by
  let A := scalarOriginalNormalization.{uR, uMR, uNR} R
  let B := scalarOriginalNormalization.{uS, uMS, uNS} S
  exact (congrArg (fun x => B.equiv.invFun (independentBGLScalarPlusMap f x))
    A.forwardPoint).trans
      ((congrArg B.equiv.invFun (independentBGLScalarPlusMap_point f)).trans B.backwardPoint)

private def scalarOriginalNormalizedForwardComputed.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) :
    ContinuousMap.HomotopyRel
      (nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f)
      (nativeProjectiveZeroScalarOriginalNormalizedMap.{uR, uS, uMR, uMS, uNR, uNS} f)
      {RingK0.projectiveZeroPoint.{uR, uMR, uNR} R} := by
  let A := scalarOriginalNormalization.{uR, uMR, uNR} R
  let B := scalarOriginalNormalization.{uS, uMS, uNS} S
  let psi := nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f
  let G := nativeProjectiveZeroScalarOriginalConjugatePlusMap.{uR, uS, uMR, uMS, uNR, uNS} f
  let T := nativeProjectiveZeroScalarOriginalNormalizedMap.{uR, uS, uMR, uMS, uNR, uNS} f
  let x := RingK0.projectiveZeroPoint.{uR, uMR, uNR} R
  let k := (B.equiv.invFun.comp B.equiv.toFun).comp psi
  let middle := (B.equiv.invFun.comp G).comp A.equiv.toFun
  let H0 := B.leftFamily.symm.precomposePointRelative psi x
    (nativeProjectiveZeroScalarMap_point.{uR, uS, uMR, uMS, uNR, uNS} f)
  let H : ContinuousMap.HomotopyRel psi k {x} := H0.cast
    (by apply ContinuousMap.ext; intro z; rfl) (by apply ContinuousMap.ext; intro z; rfl)
  let K0 := A.leftFamily.symm.compContinuousMap k
  let K : ContinuousMap.HomotopyRel k middle {x} := K0.cast
    (by apply ContinuousMap.ext; intro z; rfl) (by apply ContinuousMap.ext; intro z; rfl)
  let L0 := ((nativeProjectiveZeroScalarOriginalConjugateToPlus.{
    uR, uS, uMR, uMS, uNR, uNS} f).precomposePointRelative A.equiv.toFun x
      A.forwardPoint).compContinuousMap B.equiv.invFun
  let L : ContinuousMap.HomotopyRel middle T {x} := L0.cast
    (by apply ContinuousMap.ext; intro z; rfl) (by apply ContinuousMap.ext; intro z; rfl)
  exact (H.trans K).trans L

private def scalarOriginalNormalizedBackwardComputed.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) :
    ContinuousMap.HomotopyRel
      (nativeProjectiveZeroScalarOriginalNormalizedMap.{uR, uS, uMR, uMS, uNR, uNS} f)
      (nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f)
      {RingK0.projectiveZeroPoint.{uR, uMR, uNR} R} := by
  let A := scalarOriginalNormalization.{uR, uMR, uNR} R
  let B := scalarOriginalNormalization.{uS, uMS, uNS} S
  let psi := nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f
  let G := nativeProjectiveZeroScalarOriginalConjugatePlusMap.{uR, uS, uMR, uMS, uNR, uNS} f
  let T := nativeProjectiveZeroScalarOriginalNormalizedMap.{uR, uS, uMR, uMS, uNR, uNS} f
  let x := RingK0.projectiveZeroPoint.{uR, uMR, uNR} R
  let k := (B.equiv.invFun.comp B.equiv.toFun).comp psi
  let middle := (B.equiv.invFun.comp G).comp A.equiv.toFun
  let L0 := ((nativeProjectiveZeroScalarOriginalPlusToConjugate.{
    uR, uS, uMR, uMS, uNR, uNS} f).precomposePointRelative A.equiv.toFun x
      A.forwardPoint).compContinuousMap B.equiv.invFun
  let L : ContinuousMap.HomotopyRel T middle {x} := L0.cast
    (by apply ContinuousMap.ext; intro z; rfl) (by apply ContinuousMap.ext; intro z; rfl)
  let K0 := A.leftFamily.compContinuousMap k
  let K : ContinuousMap.HomotopyRel middle k {x} := K0.cast
    (by apply ContinuousMap.ext; intro z; rfl) (by apply ContinuousMap.ext; intro z; rfl)
  let H0 := B.leftFamily.precomposePointRelative psi x
    (nativeProjectiveZeroScalarMap_point.{uR, uS, uMR, uMS, uNR, uNS} f)
  let H : ContinuousMap.HomotopyRel k psi {x} := H0.cast
    (by apply ContinuousMap.ext; intro z; rfl) (by apply ContinuousMap.ext; intro z; rfl)
  exact (L.trans K).trans H

/-- Intrinsic scalar to normalized original plus scalar, using both original left families. -/
public def nativeProjectiveZeroScalarOriginalNormalizedComparison.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) :
    ContinuousMap.HomotopyRel
      (nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f)
      (nativeProjectiveZeroScalarOriginalNormalizedMap.{uR, uS, uMR, uMS, uNR, uNS} f)
      {RingK0.projectiveZeroPoint.{uR, uMR, uNR} R} :=
  scalarOriginalNormalizedForwardComputed.{uR, uS, uMR, uMS, uNR, uNS} f

/-- Normalized original plus scalar to intrinsic scalar, using the other universal family. -/
public def nativeProjectiveZeroScalarOriginalNormalizedComparisonInverse.{
    uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) :
    ContinuousMap.HomotopyRel
      (nativeProjectiveZeroScalarOriginalNormalizedMap.{uR, uS, uMR, uMS, uNR, uNS} f)
      (nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f)
      {RingK0.projectiveZeroPoint.{uR, uMR, uNR} R} :=
  scalarOriginalNormalizedBackwardComputed.{uR, uS, uMR, uMS, uNR, uNS} f

/-- The original forward chart square, with its entire original-root relative family. -/
public def nativeProjectiveZeroScalarOriginalForwardSquare.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) :
    ContinuousMap.HomotopyRel
      ((independentBGLScalarPlusMap f).comp
        (nativeProjectiveZeroPlusNormalizationOfRing.{uR, uMR, uNR} R).equiv.toFun)
      ((nativeProjectiveZeroPlusNormalizationOfRing.{uS, uMS, uNS} S).equiv.toFun.comp
        (nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f))
      {RingK0.projectiveZeroPoint.{uR, uMR, uNR} R} := by
  let A := scalarOriginalNormalization.{uR, uMR, uNR} R
  let B := scalarOriginalNormalization.{uS, uMS, uNS} S
  let T := nativeProjectiveZeroScalarOriginalNormalizedMap.{uR, uS, uMR, uMS, uNR, uNS} f
  let x := RingK0.projectiveZeroPoint.{uR, uMR, uNR} R
  let q := (independentBGLScalarPlusMap f).comp A.equiv.toFun
  have hq : q x = independentBGLCellPoint S :=
    (congrArg (independentBGLScalarPlusMap f) A.forwardPoint).trans
      (independentBGLScalarPlusMap_point f)
  let H0 := B.rightFamily.symm.precomposePointRelative q x hq
  let H : ContinuousMap.HomotopyRel q (B.equiv.toFun.comp T) {x} := H0.cast
    (by apply ContinuousMap.ext; intro z; rfl) (by apply ContinuousMap.ext; intro z; rfl)
  let K := (nativeProjectiveZeroScalarOriginalNormalizedComparisonInverse.{
    uR, uS, uMR, uMS, uNR, uNS} f).compContinuousMap B.equiv.toFun
  exact H.trans K

/-- The full reverse of the forward chart square, using the other universal family. -/
public def nativeProjectiveZeroScalarOriginalForwardSquareInverse.{
    uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) :
    ContinuousMap.HomotopyRel
      ((nativeProjectiveZeroPlusNormalizationOfRing.{uS, uMS, uNS} S).equiv.toFun.comp
        (nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f))
      ((independentBGLScalarPlusMap f).comp
        (nativeProjectiveZeroPlusNormalizationOfRing.{uR, uMR, uNR} R).equiv.toFun)
      {RingK0.projectiveZeroPoint.{uR, uMR, uNR} R} := by
  let A := scalarOriginalNormalization.{uR, uMR, uNR} R
  let B := scalarOriginalNormalization.{uS, uMS, uNS} S
  let T := nativeProjectiveZeroScalarOriginalNormalizedMap.{uR, uS, uMR, uMS, uNR, uNS} f
  let x := RingK0.projectiveZeroPoint.{uR, uMR, uNR} R
  let q := (independentBGLScalarPlusMap f).comp A.equiv.toFun
  have hq : q x = independentBGLCellPoint S :=
    (congrArg (independentBGLScalarPlusMap f) A.forwardPoint).trans
      (independentBGLScalarPlusMap_point f)
  let H := (nativeProjectiveZeroScalarOriginalNormalizedComparison.{
    uR, uS, uMR, uMS, uNR, uNS} f).compContinuousMap B.equiv.toFun
  let K0 := B.rightFamily.precomposePointRelative q x hq
  let K : ContinuousMap.HomotopyRel (B.equiv.toFun.comp T) q {x} := K0.cast
    (by apply ContinuousMap.ext; intro z; rfl) (by apply ContinuousMap.ext; intro z; rfl)
  exact H.trans K

/-- The original inverse chart square retains the original marked plus point. -/
public def nativeProjectiveZeroScalarOriginalInverseSquare.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) :
    ContinuousMap.HomotopyRel
      ((nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f).comp
        (nativeProjectiveZeroPlusNormalizationOfRing.{uR, uMR, uNR} R).equiv.invFun)
      ((nativeProjectiveZeroPlusNormalizationOfRing.{uS, uMS, uNS} S).equiv.invFun.comp
        (independentBGLScalarPlusMap f)) {independentBGLCellPoint R} := by
  let A := scalarOriginalNormalization.{uR, uMR, uNR} R
  let B := scalarOriginalNormalization.{uS, uMS, uNS} S
  let T := nativeProjectiveZeroScalarOriginalNormalizedMap.{uR, uS, uMR, uMS, uNR, uNS} f
  let p := independentBGLCellPoint R
  let k := B.equiv.invFun.comp (independentBGLScalarPlusMap f)
  let H := (nativeProjectiveZeroScalarOriginalNormalizedComparison.{
    uR, uS, uMR, uMS, uNR, uNS} f).precomposePointRelative A.equiv.invFun p A.backwardPoint
  let K0 := A.rightFamily.compContinuousMap k
  let K : ContinuousMap.HomotopyRel (T.comp A.equiv.invFun) k {p} := K0.cast
    (by apply ContinuousMap.ext; intro z; rfl) (by apply ContinuousMap.ext; intro z; rfl)
  exact H.trans K

/-- The complete reverse inverse-chart family uses the other universal direction. -/
public def nativeProjectiveZeroScalarOriginalInverseSquareInverse.{
    uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) :
    ContinuousMap.HomotopyRel
      ((nativeProjectiveZeroPlusNormalizationOfRing.{uS, uMS, uNS} S).equiv.invFun.comp
        (independentBGLScalarPlusMap f))
      ((nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f).comp
        (nativeProjectiveZeroPlusNormalizationOfRing.{uR, uMR, uNR} R).equiv.invFun)
      {independentBGLCellPoint R} := by
  let A := scalarOriginalNormalization.{uR, uMR, uNR} R
  let B := scalarOriginalNormalization.{uS, uMS, uNS} S
  let T := nativeProjectiveZeroScalarOriginalNormalizedMap.{uR, uS, uMR, uMS, uNR, uNS} f
  let p := independentBGLCellPoint R
  let k := B.equiv.invFun.comp (independentBGLScalarPlusMap f)
  let H0 := A.rightFamily.symm.compContinuousMap k
  let H : ContinuousMap.HomotopyRel k (T.comp A.equiv.invFun) {p} := H0.cast
    (by apply ContinuousMap.ext; intro z; rfl) (by apply ContinuousMap.ext; intro z; rfl)
  let K := (nativeProjectiveZeroScalarOriginalNormalizedComparisonInverse.{
    uR, uS, uMR, uMS, uNR, uNS} f).precomposePointRelative A.equiv.invFun p A.backwardPoint
  exact H.trans K

/-- ALL ten original complete normalization-family values are retained. -/
public theorem nativeProjectiveZeroScalarOriginalNormalizationFamilyValues.{
    uR, uS, uMR, uMS, uNR, uNS} (R : Type uR) (S : Type uS) [Ring R] [Ring S] :
    let A := nativeProjectiveZeroPlusNormalizationOfRing.{uR, uMR, uNR} R
    let B := nativeProjectiveZeroPlusNormalizationOfRing.{uS, uMS, uNS} S
    (A.modelLeft.toContinuousMap = A.data.modelLeft ∧
      A.modelRight.toContinuousMap = A.data.modelRight ∧
      A.leftFamily.toContinuousMap = A.data.leftFamily ∧
      A.rightFamily.toContinuousMap = A.data.rightFamily ∧
      A.sourceTriangle.toContinuousMap = A.data.sourceTriangle) ∧
    (B.modelLeft.toContinuousMap = B.data.modelLeft ∧
      B.modelRight.toContinuousMap = B.data.modelRight ∧
      B.leftFamily.toContinuousMap = B.data.leftFamily ∧
      B.rightFamily.toContinuousMap = B.data.rightFamily ∧
      B.sourceTriangle.toContinuousMap = B.data.sourceTriangle) := by
  let A := nativeProjectiveZeroPlusNormalizationOfRing.{uR, uMR, uNR} R
  let B := nativeProjectiveZeroPlusNormalizationOfRing.{uS, uMS, uNS} S
  exact ⟨A.fullFamilyValues, B.fullFamilyValues⟩

/-- The complete SAME continuous family value of
    nativeProjectiveZeroScalarOriginalConjugateSourceTriangle. -/
public def nativeProjectiveZeroScalarOriginalConjugateSourceTriangleFamily.{uR, uS, uMR, uMS, uNR,
  uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) : C(unitInterval × (ordinaryBGL R), independentBGLCellTarget S) :=
  (nativeProjectiveZeroScalarOriginalConjugateSourceTriangle.{uR, uS, uMR, uMS, uNR, uNS}
    f).toContinuousMap

/-- The entire exported family is the selected relative homotopy's full value. -/
public theorem nativeProjectiveZeroScalarOriginalConjugateSourceTriangle_toContinuousMap.{uR, uS,
  uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) : (nativeProjectiveZeroScalarOriginalConjugateSourceTriangle.{uR, uS, uMR, uMS,
      uNR, uNS} f).toContinuousMap =
      nativeProjectiveZeroScalarOriginalConjugateSourceTriangleFamily.{uR, uS, uMR, uMS, uNR, uNS}
        f := by
  rfl

/-- Every interval time retains the exact original target root. -/
public theorem nativeProjectiveZeroScalarOriginalConjugateSourceTriangle_root_value.{uR, uS, uMR,
  uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) (t : unitInterval) :
    nativeProjectiveZeroScalarOriginalConjugateSourceTriangleFamily.{uR, uS, uMR, uMS, uNR, uNS} f
      (t, ordinaryBGLBasepoint R) = independentBGLCellPoint S := by
  exact ((nativeProjectiveZeroScalarOriginalConjugateSourceTriangle.{uR, uS, uMR, uMS, uNR, uNS}
    f).eq_fst t
    (by rfl)).trans
      ((congrArg (nativeProjectiveZeroScalarOriginalConjugatePlusMap.{uR, uS, uMR, uMS, uNR, uNS} f)
        (independentBGLCellInclusion_point R)).trans
        (nativeProjectiveZeroScalarOriginalConjugatePlusMap_point.{uR, uS, uMR, uMS, uNR, uNS} f))

/-- The complete SAME continuous family value of
    nativeProjectiveZeroScalarOriginalPlusToConjugate. -/
public def nativeProjectiveZeroScalarOriginalPlusToConjugateFamily.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) : C(unitInterval × (independentBGLCellTarget R), independentBGLCellTarget S) :=
  (nativeProjectiveZeroScalarOriginalPlusToConjugate.{uR, uS, uMR, uMS, uNR, uNS} f).toContinuousMap

/-- The entire exported family is the selected relative homotopy's full value. -/
public theorem nativeProjectiveZeroScalarOriginalPlusToConjugate_toContinuousMap.{uR, uS, uMR,
  uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) : (nativeProjectiveZeroScalarOriginalPlusToConjugate.{uR, uS, uMR, uMS, uNR,
      uNS} f).toContinuousMap =
      nativeProjectiveZeroScalarOriginalPlusToConjugateFamily.{uR, uS, uMR, uMS, uNR, uNS} f := by
  rfl

/-- Every interval time retains the exact original target root. -/
public theorem nativeProjectiveZeroScalarOriginalPlusToConjugate_root_value.{uR, uS, uMR, uMS,
  uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) (t : unitInterval) :
    nativeProjectiveZeroScalarOriginalPlusToConjugateFamily.{uR, uS, uMR, uMS, uNR, uNS} f (t,
      independentBGLCellPoint R) = independentBGLCellPoint S := by
  exact ((nativeProjectiveZeroScalarOriginalPlusToConjugate.{uR, uS, uMR, uMS, uNR, uNS} f).eq_fst t
    (by rfl)).trans (independentBGLScalarPlusMap_point f)

/-- The complete SAME continuous family value of
    nativeProjectiveZeroScalarOriginalConjugateToPlus. -/
public def nativeProjectiveZeroScalarOriginalConjugateToPlusFamily.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) : C(unitInterval × (independentBGLCellTarget R), independentBGLCellTarget S) :=
  (nativeProjectiveZeroScalarOriginalConjugateToPlus.{uR, uS, uMR, uMS, uNR, uNS} f).toContinuousMap

/-- The entire exported family is the selected relative homotopy's full value. -/
public theorem nativeProjectiveZeroScalarOriginalConjugateToPlus_toContinuousMap.{uR, uS, uMR,
  uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) : (nativeProjectiveZeroScalarOriginalConjugateToPlus.{uR, uS, uMR, uMS, uNR,
      uNS} f).toContinuousMap =
      nativeProjectiveZeroScalarOriginalConjugateToPlusFamily.{uR, uS, uMR, uMS, uNR, uNS} f := by
  rfl

/-- Every interval time retains the exact original target root. -/
public theorem nativeProjectiveZeroScalarOriginalConjugateToPlus_root_value.{uR, uS, uMR, uMS,
  uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) (t : unitInterval) :
    nativeProjectiveZeroScalarOriginalConjugateToPlusFamily.{uR, uS, uMR, uMS, uNR, uNS} f (t,
      independentBGLCellPoint R) = independentBGLCellPoint S := by
  exact ((nativeProjectiveZeroScalarOriginalConjugateToPlus.{uR, uS, uMR, uMS, uNR, uNS} f).eq_fst t
    (by rfl)).trans (nativeProjectiveZeroScalarOriginalConjugatePlusMap_point.{uR, uS, uMR, uMS,
      uNR, uNS} f)

/-- The complete SAME continuous family value of
    nativeProjectiveZeroScalarOriginalNormalizedComparison. -/
public def nativeProjectiveZeroScalarOriginalNormalizedComparisonFamily.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) : C(unitInterval × (RingK0.projectiveZeroSpace.{uR, uMR, uNR} R),
      RingK0.projectiveZeroSpace.{uS, uMS, uNS} S) :=
  (nativeProjectiveZeroScalarOriginalNormalizedComparison.{uR, uS, uMR, uMS, uNR, uNS}
    f).toContinuousMap

/-- The entire exported family is the selected relative homotopy's full value. -/
public theorem nativeProjectiveZeroScalarOriginalNormalizedComparison_toContinuousMap.{uR, uS,
  uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) : (nativeProjectiveZeroScalarOriginalNormalizedComparison.{uR, uS, uMR, uMS,
      uNR, uNS} f).toContinuousMap =
      nativeProjectiveZeroScalarOriginalNormalizedComparisonFamily.{uR, uS, uMR, uMS, uNR, uNS} f
        := by
  rfl

/-- Every interval time retains the exact original target root. -/
public theorem nativeProjectiveZeroScalarOriginalNormalizedComparison_root_value.{uR, uS, uMR,
  uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) (t : unitInterval) :
    nativeProjectiveZeroScalarOriginalNormalizedComparisonFamily.{uR, uS, uMR, uMS, uNR, uNS} f
      (t, RingK0.projectiveZeroPoint.{uR, uMR, uNR} R) = RingK0.projectiveZeroPoint.{uS, uMS, uNS}
      S := by
  exact ((nativeProjectiveZeroScalarOriginalNormalizedComparison.{uR, uS, uMR, uMS, uNR, uNS}
    f).eq_fst t
    (by rfl)).trans (nativeProjectiveZeroScalarMap_point.{uR, uS, uMR, uMS, uNR, uNS} f)

/-- The complete SAME continuous family value of
    nativeProjectiveZeroScalarOriginalNormalizedComparisonInverse. -/
public def nativeProjectiveZeroScalarOriginalNormalizedComparisonInverseFamily.{uR, uS, uMR, uMS,
  uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) : C(unitInterval × (RingK0.projectiveZeroSpace.{uR, uMR, uNR} R),
      RingK0.projectiveZeroSpace.{uS, uMS, uNS} S) :=
  (nativeProjectiveZeroScalarOriginalNormalizedComparisonInverse.{uR, uS, uMR, uMS, uNR, uNS}
    f).toContinuousMap

/-- The entire exported family is the selected relative homotopy's full value. -/
public theorem nativeProjectiveZeroScalarOriginalNormalizedComparisonInverse_toContinuousMap.{uR,
  uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) : (nativeProjectiveZeroScalarOriginalNormalizedComparisonInverse.{uR, uS, uMR,
      uMS, uNR, uNS} f).toContinuousMap =
      nativeProjectiveZeroScalarOriginalNormalizedComparisonInverseFamily.{uR, uS, uMR, uMS, uNR,
        uNS} f := by
  rfl

/-- Every interval time retains the exact original target root. -/
public theorem nativeProjectiveZeroScalarOriginalNormalizedComparisonInverse_root_value.{uR, uS,
  uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) (t : unitInterval) :
    nativeProjectiveZeroScalarOriginalNormalizedComparisonInverseFamily.{uR, uS, uMR, uMS, uNR,
      uNS} f (t, RingK0.projectiveZeroPoint.{uR, uMR, uNR} R) = RingK0.projectiveZeroPoint.{uS,
      uMS, uNS} S := by
  exact ((nativeProjectiveZeroScalarOriginalNormalizedComparisonInverse.{uR, uS, uMR, uMS, uNR,
    uNS} f).eq_fst t
    (by rfl)).trans (nativeProjectiveZeroScalarOriginalNormalizedMap_point.{uR, uS, uMR, uMS, uNR,
      uNS} f)

/-- The complete SAME continuous family value of nativeProjectiveZeroScalarOriginalForwardSquare. -/
public def nativeProjectiveZeroScalarOriginalForwardSquareFamily.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) : C(unitInterval × (RingK0.projectiveZeroSpace.{uR, uMR, uNR} R),
      independentBGLCellTarget S) :=
  (nativeProjectiveZeroScalarOriginalForwardSquare.{uR, uS, uMR, uMS, uNR, uNS} f).toContinuousMap

/-- The entire exported family is the selected relative homotopy's full value. -/
public theorem nativeProjectiveZeroScalarOriginalForwardSquare_toContinuousMap.{uR, uS, uMR, uMS,
  uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) : (nativeProjectiveZeroScalarOriginalForwardSquare.{uR, uS, uMR, uMS, uNR, uNS}
      f).toContinuousMap =
      nativeProjectiveZeroScalarOriginalForwardSquareFamily.{uR, uS, uMR, uMS, uNR, uNS} f := by
  rfl

/-- Every interval time retains the exact original target root. -/
public theorem nativeProjectiveZeroScalarOriginalForwardSquare_root_value.{uR, uS, uMR, uMS, uNR,
  uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) (t : unitInterval) :
    nativeProjectiveZeroScalarOriginalForwardSquareFamily.{uR, uS, uMR, uMS, uNR, uNS} f (t,
      RingK0.projectiveZeroPoint.{uR, uMR, uNR} R) = independentBGLCellPoint S := by
  let A := scalarOriginalNormalization.{uR, uMR, uNR} R
  exact ((nativeProjectiveZeroScalarOriginalForwardSquare.{uR, uS, uMR, uMS, uNR, uNS} f).eq_fst t
    (by rfl)).trans
      ((congrArg (independentBGLScalarPlusMap f) A.forwardPoint).trans
        (independentBGLScalarPlusMap_point f))

/-- The complete SAME continuous family value of
    nativeProjectiveZeroScalarOriginalForwardSquareInverse. -/
public def nativeProjectiveZeroScalarOriginalForwardSquareInverseFamily.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) : C(unitInterval × (RingK0.projectiveZeroSpace.{uR, uMR, uNR} R),
      independentBGLCellTarget S) :=
  (nativeProjectiveZeroScalarOriginalForwardSquareInverse.{uR, uS, uMR, uMS, uNR, uNS}
    f).toContinuousMap

/-- The entire exported family is the selected relative homotopy's full value. -/
public theorem nativeProjectiveZeroScalarOriginalForwardSquareInverse_toContinuousMap.{uR, uS,
  uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) : (nativeProjectiveZeroScalarOriginalForwardSquareInverse.{uR, uS, uMR, uMS,
      uNR, uNS} f).toContinuousMap =
      nativeProjectiveZeroScalarOriginalForwardSquareInverseFamily.{uR, uS, uMR, uMS, uNR, uNS} f
        := by
  rfl

/-- Every interval time retains the exact original target root. -/
public theorem nativeProjectiveZeroScalarOriginalForwardSquareInverse_root_value.{uR, uS, uMR,
  uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) (t : unitInterval) :
    nativeProjectiveZeroScalarOriginalForwardSquareInverseFamily.{uR, uS, uMR, uMS, uNR, uNS} f
      (t, RingK0.projectiveZeroPoint.{uR, uMR, uNR} R) = independentBGLCellPoint S := by
  let B := scalarOriginalNormalization.{uS, uMS, uNS} S
  exact ((nativeProjectiveZeroScalarOriginalForwardSquareInverse.{uR, uS, uMR, uMS, uNR, uNS}
    f).eq_fst t
    (by rfl)).trans
      ((congrArg B.equiv.toFun (nativeProjectiveZeroScalarMap_point.{uR, uS, uMR, uMS, uNR, uNS}
        f)).trans
        B.forwardPoint)

/-- The complete SAME continuous family value of nativeProjectiveZeroScalarOriginalInverseSquare. -/
public def nativeProjectiveZeroScalarOriginalInverseSquareFamily.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) : C(unitInterval × (independentBGLCellTarget R), RingK0.projectiveZeroSpace.{uS,
      uMS, uNS} S) :=
  (nativeProjectiveZeroScalarOriginalInverseSquare.{uR, uS, uMR, uMS, uNR, uNS} f).toContinuousMap

/-- The entire exported family is the selected relative homotopy's full value. -/
public theorem nativeProjectiveZeroScalarOriginalInverseSquare_toContinuousMap.{uR, uS, uMR, uMS,
  uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) : (nativeProjectiveZeroScalarOriginalInverseSquare.{uR, uS, uMR, uMS, uNR, uNS}
      f).toContinuousMap =
      nativeProjectiveZeroScalarOriginalInverseSquareFamily.{uR, uS, uMR, uMS, uNR, uNS} f := by
  rfl

/-- Every interval time retains the exact original target root. -/
public theorem nativeProjectiveZeroScalarOriginalInverseSquare_root_value.{uR, uS, uMR, uMS, uNR,
  uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) (t : unitInterval) :
    nativeProjectiveZeroScalarOriginalInverseSquareFamily.{uR, uS, uMR, uMS, uNR, uNS} f (t,
      independentBGLCellPoint R) = RingK0.projectiveZeroPoint.{uS, uMS, uNS} S := by
  let A := scalarOriginalNormalization.{uR, uMR, uNR} R
  let psi := nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f
  exact ((nativeProjectiveZeroScalarOriginalInverseSquare.{uR, uS, uMR, uMS, uNR, uNS} f).eq_fst t
    (by rfl)).trans
      ((congrArg psi A.backwardPoint).trans (nativeProjectiveZeroScalarMap_point.{uR, uS, uMR,
        uMS, uNR, uNS} f))

/-- The complete SAME continuous family value of
    nativeProjectiveZeroScalarOriginalInverseSquareInverse. -/
public def nativeProjectiveZeroScalarOriginalInverseSquareInverseFamily.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) : C(unitInterval × (independentBGLCellTarget R), RingK0.projectiveZeroSpace.{uS,
      uMS, uNS} S) :=
  (nativeProjectiveZeroScalarOriginalInverseSquareInverse.{uR, uS, uMR, uMS, uNR, uNS}
    f).toContinuousMap

/-- The entire exported family is the selected relative homotopy's full value. -/
public theorem nativeProjectiveZeroScalarOriginalInverseSquareInverse_toContinuousMap.{uR, uS,
  uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) : (nativeProjectiveZeroScalarOriginalInverseSquareInverse.{uR, uS, uMR, uMS,
      uNR, uNS} f).toContinuousMap =
      nativeProjectiveZeroScalarOriginalInverseSquareInverseFamily.{uR, uS, uMR, uMS, uNR, uNS} f
        := by
  rfl

/-- Every interval time retains the exact original target root. -/
public theorem nativeProjectiveZeroScalarOriginalInverseSquareInverse_root_value.{uR, uS, uMR,
  uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) (t : unitInterval) :
    nativeProjectiveZeroScalarOriginalInverseSquareInverseFamily.{uR, uS, uMR, uMS, uNR, uNS} f
      (t, independentBGLCellPoint R) = RingK0.projectiveZeroPoint.{uS, uMS, uNS} S := by
  let B := scalarOriginalNormalization.{uS, uMS, uNS} S
  exact ((nativeProjectiveZeroScalarOriginalInverseSquareInverse.{uR, uS, uMR, uMS, uNR, uNS}
    f).eq_fst t
    (by rfl)).trans
      ((congrArg B.equiv.invFun (independentBGLScalarPlusMap_point f)).trans B.backwardPoint)

end AlgebraicKTheory.StableGL

end
