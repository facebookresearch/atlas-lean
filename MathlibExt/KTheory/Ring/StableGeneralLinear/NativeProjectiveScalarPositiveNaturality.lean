/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.KTheory.Ring.StableGeneralLinear.NativeProjectiveZeroScalarOriginalPlusNaturality
public import MathlibExt.Topology.Homotopy.BasedHomotopyGroupEquivalence
public import MathlibExt.Topology.Homotopy.WeaklyPointedPositiveHomotopyGroupMap

/-!
# Every positive group of the exact original native/independent-plus normalization

The original normalization forward/backward maps and BOTH complete inverse
families induce group isomorphisms in every positive degree. The SAME original
independent P_f and intrinsic native scalar map satisfy both chart squares,
using their actual whole point-relative families. All ten original family
values and six independent roles remain. This is the native/plus branch;
attaching the canonical original Q map still requires its actual source and
original own-loop-unit comparison.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicKTheory.StableGL

private abbrev originalPositiveNormalization.{uRing, uModule, uNative}
    (R : Type uRing) [Ring R] :=
  nativeProjectiveZeroPlusNormalizationOfRing.{uRing, uModule, uNative} R

/-- The original normalized maps and BOTH full inverse families give every positive isomorphism. -/
public def originalNativePlusPositiveMulEquiv.{uRing, uModule, uNative}
    (R : Type uRing) [Ring R] (n : ℕ) :
    HomotopyGroup.Pi (n + 1) (RingK0.projectiveZeroSpace.{uRing, uModule, uNative} R)
        (RingK0.projectiveZeroPoint.{uRing, uModule, uNative} R) ≃*
      HomotopyGroup.Pi (n + 1) (independentBGLCellTarget R) (independentBGLCellPoint R) := by
  let N := originalPositiveNormalization.{uRing, uModule, uNative} R
  exact HomotopyGroup.mulEquivOfBasedInverse n N.equiv.toFun N.equiv.invFun
    N.forwardPoint N.backwardPoint N.leftFamily N.rightFamily

private theorem originalNativePlusPositiveApplyComputed.{uRing, uModule, uNative}
    (R : Type uRing) [Ring R] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (RingK0.projectiveZeroSpace.{uRing, uModule, uNative} R)
      (RingK0.projectiveZeroPoint.{uRing, uModule, uNative} R)) :
    originalNativePlusPositiveMulEquiv.{uRing, uModule, uNative} R n a =
      HomotopyGroup.mapHomOfEq
        (nativeProjectiveZeroPlusNormalizationOfRing.{uRing, uModule, uNative} R).equiv.toFun
        (nativeProjectiveZeroPlusNormalizationOfRing.{uRing, uModule, uNative} R).forwardPoint
        n a := by
  let N := originalPositiveNormalization.{uRing, uModule, uNative} R
  exact HomotopyGroup.mulEquivOfBasedInverse_apply n N.equiv.toFun N.equiv.invFun
    N.forwardPoint N.backwardPoint N.leftFamily N.rightFamily a

/-- Every forward class uses the exact original normalization map and point equation. -/
public theorem originalNativePlusPositiveMulEquiv_apply.{uRing, uModule, uNative}
    (R : Type uRing) [Ring R] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (RingK0.projectiveZeroSpace.{uRing, uModule, uNative} R)
      (RingK0.projectiveZeroPoint.{uRing, uModule, uNative} R)) :
    originalNativePlusPositiveMulEquiv.{uRing, uModule, uNative} R n a =
      HomotopyGroup.mapHomOfEq
        (nativeProjectiveZeroPlusNormalizationOfRing.{uRing, uModule, uNative} R).equiv.toFun
        (nativeProjectiveZeroPlusNormalizationOfRing.{uRing, uModule, uNative} R).forwardPoint
        n a :=
  originalNativePlusPositiveApplyComputed R n a

private theorem originalNativePlusPositiveSymmApplyComputed.{uRing, uModule, uNative}
    (R : Type uRing) [Ring R] (n : ℕ)
    (b : HomotopyGroup.Pi (n + 1) (independentBGLCellTarget R) (independentBGLCellPoint R)) :
    (originalNativePlusPositiveMulEquiv.{uRing, uModule, uNative} R n).symm b =
      HomotopyGroup.mapHomOfEq
        (nativeProjectiveZeroPlusNormalizationOfRing.{uRing, uModule, uNative} R).equiv.invFun
        (nativeProjectiveZeroPlusNormalizationOfRing.{uRing, uModule, uNative} R).backwardPoint
        n b := by
  let N := originalPositiveNormalization.{uRing, uModule, uNative} R
  exact HomotopyGroup.mulEquivOfBasedInverse_symm_apply n N.equiv.toFun N.equiv.invFun
    N.forwardPoint N.backwardPoint N.leftFamily N.rightFamily b

/-- Every inverse class uses the SAME original backward map and its original point law. -/
public theorem originalNativePlusPositiveMulEquiv_symm_apply.{uRing, uModule, uNative}
    (R : Type uRing) [Ring R] (n : ℕ)
    (b : HomotopyGroup.Pi (n + 1) (independentBGLCellTarget R) (independentBGLCellPoint R)) :
    (originalNativePlusPositiveMulEquiv.{uRing, uModule, uNative} R n).symm b =
      HomotopyGroup.mapHomOfEq
        (nativeProjectiveZeroPlusNormalizationOfRing.{uRing, uModule, uNative} R).equiv.invFun
        (nativeProjectiveZeroPlusNormalizationOfRing.{uRing, uModule, uNative} R).backwardPoint
        n b :=
  originalNativePlusPositiveSymmApplyComputed R n b

/-- Both original normalization directions are inverse on all positive classes. -/
public theorem originalNativePlusPositiveMulEquiv_inverse_laws.{uRing, uModule, uNative}
    (R : Type uRing) [Ring R] (n : ℕ) :
    (∀ a, (originalNativePlusPositiveMulEquiv.{uRing, uModule, uNative} R n).symm
      (originalNativePlusPositiveMulEquiv.{uRing, uModule, uNative} R n a) = a) ∧
    (∀ b, originalNativePlusPositiveMulEquiv.{uRing, uModule, uNative} R n
      ((originalNativePlusPositiveMulEquiv.{uRing, uModule, uNative} R n).symm b) = b) :=
  ⟨(originalNativePlusPositiveMulEquiv.{uRing, uModule, uNative} R n).symm_apply_apply,
    (originalNativePlusPositiveMulEquiv.{uRing, uModule, uNative} R n).apply_symm_apply⟩

private def originalStrictPositiveMap.{uX, uY}
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : C(X, Y)) (h : f x = y) (n : ℕ) :
    HomotopyGroup.Pi (n + 1) X x →* HomotopyGroup.Pi (n + 1) Y y :=
  ContinuousMap.WeaklyPointed.positiveHomotopyGroupMap n
    (⟨f, (Path.refl (f x)).cast rfl h.symm⟩ : ContinuousMap.WeaklyPointed x y)

private theorem originalStrictPositiveMapValue.{uX, uY}
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : C(X, Y)) (h : f x = y) (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) X x) :
    originalStrictPositiveMap f h n a = HomotopyGroup.mapHomOfEq f h n a :=
  ContinuousMap.WeaklyPointed.positiveHomotopyGroupMap_of_eq n f h a

/-- The actual original intrinsic scalar map induces its positive group map at the SAME point. -/
public def originalNativePositiveScalarMap.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (n : ℕ) :
    HomotopyGroup.Pi (n + 1) (RingK0.projectiveZeroSpace.{uR, uMR, uNR} R)
        (RingK0.projectiveZeroPoint.{uR, uMR, uNR} R) →*
      HomotopyGroup.Pi (n + 1) (RingK0.projectiveZeroSpace.{uS, uMS, uNS} S)
        (RingK0.projectiveZeroPoint.{uS, uMS, uNS} S) :=
  originalStrictPositiveMap (nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f)
    (nativeProjectiveZeroScalarMap_point.{uR, uS, uMR, uMS, uNR, uNS} f) n

private theorem originalNativePositiveScalarApplyComputed.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (RingK0.projectiveZeroSpace.{uR, uMR, uNR} R)
      (RingK0.projectiveZeroPoint.{uR, uMR, uNR} R)) :
    originalNativePositiveScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f n a =
      HomotopyGroup.mapHomOfEq (nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f)
        (nativeProjectiveZeroScalarMap_point.{uR, uS, uMR, uMS, uNR, uNS} f) n a :=
  originalStrictPositiveMapValue _ _ n a

/-- Every positive scalar value is induced by the SAME original intrinsic map. -/
public theorem originalNativePositiveScalarMap_apply.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (RingK0.projectiveZeroSpace.{uR, uMR, uNR} R)
      (RingK0.projectiveZeroPoint.{uR, uMR, uNR} R)) :
    originalNativePositiveScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f n a =
      HomotopyGroup.mapHomOfEq (nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f)
        (nativeProjectiveZeroScalarMap_point.{uR, uS, uMR, uMS, uNR, uNS} f) n a :=
  originalNativePositiveScalarApplyComputed f n a

/-- The positive plus scalar map is induced by EXACT original independent P_f and its root. -/
public def originalIndependentPlusPositiveScalarMap.{uR, uS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (n : ℕ) :
    HomotopyGroup.Pi (n + 1) (independentBGLCellTarget R) (independentBGLCellPoint R) →*
      HomotopyGroup.Pi (n + 1) (independentBGLCellTarget S) (independentBGLCellPoint S) :=
  originalStrictPositiveMap (independentBGLScalarPlusMap f) (independentBGLScalarPlusMap_point f) n

private theorem originalIndependentPlusPositiveScalarApplyComputed.{uR, uS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (n : ℕ)
    (b : HomotopyGroup.Pi (n + 1) (independentBGLCellTarget R) (independentBGLCellPoint R)) :
    originalIndependentPlusPositiveScalarMap f n b =
      HomotopyGroup.mapHomOfEq (independentBGLScalarPlusMap f)
        (independentBGLScalarPlusMap_point f) n b :=
  originalStrictPositiveMapValue _ _ n b

/-- Every positive plus scalar value uses the original independently constructed map. -/
public theorem originalIndependentPlusPositiveScalarMap_apply.{uR, uS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (n : ℕ)
    (b : HomotopyGroup.Pi (n + 1) (independentBGLCellTarget R) (independentBGLCellPoint R)) :
    originalIndependentPlusPositiveScalarMap f n b =
      HomotopyGroup.mapHomOfEq (independentBGLScalarPlusMap f)
        (independentBGLScalarPlusMap_point f) n b :=
  originalIndependentPlusPositiveScalarApplyComputed f n b

/-- The ACTUAL original forward chart family gives f-naturality in EVERY positive degree. -/
public theorem originalNativePlusPositiveNaturality.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (RingK0.projectiveZeroSpace.{uR, uMR, uNR} R)
      (RingK0.projectiveZeroPoint.{uR, uMR, uNR} R)) :
    originalNativePlusPositiveMulEquiv.{uS, uMS, uNS} S n
        (originalNativePositiveScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f n a) =
      originalIndependentPlusPositiveScalarMap f n
        (originalNativePlusPositiveMulEquiv.{uR, uMR, uNR} R n a) := by
  let A := originalPositiveNormalization.{uR, uMR, uNR} R
  let B := originalPositiveNormalization.{uS, uMS, uNS} S
  let P := independentBGLScalarPlusMap f
  let F := nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f
  let x := RingK0.projectiveZeroPoint.{uR, uMR, uNR} R
  let hF := nativeProjectiveZeroScalarMap_point.{uR, uS, uMR, uMS, uNR, uNS} f
  let hP := independentBGLScalarPlusMap_point f
  have hLeft : (P.comp A.equiv.toFun) x = independentBGLCellPoint S :=
    (congrArg P A.forwardPoint).trans hP
  have hRight : (B.equiv.toFun.comp F) x = independentBGLCellPoint S :=
    (congrArg B.equiv.toFun hF).trans B.forwardPoint
  have hRel := HomotopyGroup.mapHomOfEq_homotopyRel n
    (P.comp A.equiv.toFun) (B.equiv.toFun.comp F) hLeft hRight
    (nativeProjectiveZeroScalarOriginalForwardSquare.{uR, uS, uMR, uMS, uNR, uNS} f)
  have hOne := HomotopyGroup.mapHomOfEq_comp F B.equiv.toFun hF B.forwardPoint hRight n a
  have hTwo := HomotopyGroup.mapHomOfEq_comp A.equiv.toFun P A.forwardPoint hP hLeft n a
  rw [originalNativePlusPositiveMulEquiv_apply, originalNativePositiveScalarMap_apply,
    originalIndependentPlusPositiveScalarMap_apply, originalNativePlusPositiveMulEquiv_apply]
  exact hOne.symm.trans ((DFunLike.congr_fun hRel a).symm.trans hTwo)

/-- The original backward chart family gives the inverse f-square in EVERY positive degree. -/
public theorem originalNativePlusPositiveInverseNaturality.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (n : ℕ)
    (b : HomotopyGroup.Pi (n + 1) (independentBGLCellTarget R) (independentBGLCellPoint R)) :
    (originalNativePlusPositiveMulEquiv.{uS, uMS, uNS} S n).symm
        (originalIndependentPlusPositiveScalarMap f n b) =
      originalNativePositiveScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f n
        ((originalNativePlusPositiveMulEquiv.{uR, uMR, uNR} R n).symm b) := by
  let A := originalPositiveNormalization.{uR, uMR, uNR} R
  let B := originalPositiveNormalization.{uS, uMS, uNS} S
  let P := independentBGLScalarPlusMap f
  let F := nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f
  let x := independentBGLCellPoint R
  let hF := nativeProjectiveZeroScalarMap_point.{uR, uS, uMR, uMS, uNR, uNS} f
  let hP := independentBGLScalarPlusMap_point f
  have hLeft : (F.comp A.equiv.invFun) x = RingK0.projectiveZeroPoint.{uS, uMS, uNS} S :=
    (congrArg F A.backwardPoint).trans hF
  have hRight : (B.equiv.invFun.comp P) x = RingK0.projectiveZeroPoint.{uS, uMS, uNS} S :=
    (congrArg B.equiv.invFun hP).trans B.backwardPoint
  have hRel := HomotopyGroup.mapHomOfEq_homotopyRel n
    (F.comp A.equiv.invFun) (B.equiv.invFun.comp P) hLeft hRight
    (nativeProjectiveZeroScalarOriginalInverseSquare.{uR, uS, uMR, uMS, uNR, uNS} f)
  have hOne := HomotopyGroup.mapHomOfEq_comp P B.equiv.invFun hP B.backwardPoint hRight n b
  have hTwo := HomotopyGroup.mapHomOfEq_comp A.equiv.invFun F A.backwardPoint hF hLeft n b
  rw [originalNativePlusPositiveMulEquiv_symm_apply, originalIndependentPlusPositiveScalarMap_apply,
    originalNativePositiveScalarMap_apply, originalNativePlusPositiveMulEquiv_symm_apply]
  exact hOne.symm.trans ((DFunLike.congr_fun hRel b).symm.trans hTwo)

/-- The original units of both positive scalar group maps are preserved. -/
public theorem originalPositiveScalarMaps_units.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (n : ℕ) :
    originalNativePositiveScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f n 1 = 1 ∧
      originalIndependentPlusPositiveScalarMap f n 1 = 1 :=
  ⟨(originalNativePositiveScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f n).map_one,
    (originalIndependentPlusPositiveScalarMap f n).map_one⟩

/-- All positive indices retain BOTH original group squares and all TEN original family values. -/
public theorem originalNativePlusPositiveNaturality_allIndices.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (∀ n a, originalNativePlusPositiveMulEquiv.{uS, uMS, uNS} S n
        (originalNativePositiveScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f n a) =
      originalIndependentPlusPositiveScalarMap f n
        (originalNativePlusPositiveMulEquiv.{uR, uMR, uNR} R n a)) ∧
    (∀ n b, (originalNativePlusPositiveMulEquiv.{uS, uMS, uNS} S n).symm
        (originalIndependentPlusPositiveScalarMap f n b) =
      originalNativePositiveScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f n
        ((originalNativePlusPositiveMulEquiv.{uR, uMR, uNR} R n).symm b)) ∧
    (let A := nativeProjectiveZeroPlusNormalizationOfRing.{uR, uMR, uNR} R
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
       B.sourceTriangle.toContinuousMap = B.data.sourceTriangle)) :=
  ⟨(fun n a => originalNativePlusPositiveNaturality.{uR, uS, uMR, uMS, uNR, uNS} f n a),
    (fun n b => originalNativePlusPositiveInverseNaturality.{uR, uS, uMR, uMS, uNR, uNS} f n b),
    nativeProjectiveZeroScalarOriginalNormalizationFamilyValues.{uR, uS, uMR, uMS, uNR, uNS} R S⟩

end AlgebraicKTheory.StableGL

end
