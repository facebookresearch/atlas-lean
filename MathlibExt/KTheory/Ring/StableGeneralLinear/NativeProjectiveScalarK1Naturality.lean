/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.KTheory.Ring.StableGeneralLinear.NativeProjectiveZeroScalarOriginalPlusNaturality
public import MathlibExt.KTheory.Ring.K1.Basic
public import MathlibExt.KTheory.Ring.K1.PlusConstructionComparison
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.PathTransportNaturality
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.PiOneMapComposition

/-!
# Classical K1 on the original independent plus and native normalization

The literal original plus inclusion supplies its actual surjective pi1 map.
The original quotient dictionary identifies its marked fundamental group
with actual classical K1. Original stable loops and the original
scalar square give naturality on every pi1 element. Both original native
normalization inverse families and their roots give the native dictionary
and its scalar square. No target or comparison outcome is supplied.
-/

noncomputable section

open CategoryTheory
open scoped ContinuousMap

namespace AlgebraicKTheory.StableGL

private theorem originalIndependentPlusPiOneSurjective.{uRing}
    (R : Type uRing) [Ring R] :
    Function.Surjective (FundamentalGroup.mapOfEq (independentBGLCellInclusion R).hom
      (independentBGLCellInclusion_point R)) := by
  let X := ordinaryBGL R
  let _ : PathConnectedSpace X := ordinaryBGLPathConnected R
  let _ : ConnectedSpace X := inferInstance
  let _ : T2Space X := SSet.realization_t2Space (classifyingNerve R)
  let _ : Topology.CWComplex (Set.univ : Set X) :=
    SSet.instCWComplexToTop (classifyingNerve R)
  let _ : (BGLPlusSubgroup R).Normal := BGLPlusSubgroup.instNormal R
  let _ : Group.IsPerfect (BGLPlusSubgroup R) := BGLPlusSubgroup.instIsPerfect R
  have h := AlgebraicTopology.LoopCellIndependentPlus.original_connected_CW_plus_construction_full
    X (ordinaryBGLBasepoint R) (BGLPlusSubgroup R)
  exact h.2.2.2.2.1

private def originalIndependentPlusK1DictionaryComputed.{uRing}
    (R : Type uRing) [Ring R] :
    Additive (FundamentalGroup (independentBGLCellTarget R) (independentBGLCellPoint R)) ≃+
      K1 R :=
  plusTargetFundamentalAddEquivK1 (independentBGLCellInclusion R) (independentBGLCellPoint R)
    (independentBGLCellInclusion_point R) (independentBGLCellInclusion_isPlus R)
    (originalIndependentPlusPiOneSurjective R)

/-- The actual marked fundamental group of the SAME original cell target
    is the original classical K1, using the existing quotient dictionary. -/
public def originalIndependentPlusK1Equiv.{uRing} (R : Type uRing) [Ring R] :
    Additive (FundamentalGroup (independentBGLCellTarget R) (independentBGLCellPoint R)) ≃+
      K1 R :=
  originalIndependentPlusK1DictionaryComputed R

/-- The full first inverse law retains every original target pi1 class. -/
public theorem originalIndependentPlusK1Equiv_left_inv.{uRing}
    (R : Type uRing) [Ring R]
    (p : Additive (FundamentalGroup (independentBGLCellTarget R) (independentBGLCellPoint R))) :
    (originalIndependentPlusK1Equiv R).symm (originalIndependentPlusK1Equiv R p) = p :=
  (originalIndependentPlusK1Equiv R).symm_apply_apply p

/-- The full other inverse law retains every original classical K1 class. -/
public theorem originalIndependentPlusK1Equiv_right_inv.{uRing}
    (R : Type uRing) [Ring R] (x : K1 R) :
    originalIndependentPlusK1Equiv R ((originalIndependentPlusK1Equiv R).symm x) = x :=
  (originalIndependentPlusK1Equiv R).apply_symm_apply x

/-- Both dictionary directions retain the original group identity roots. -/
public theorem originalIndependentPlusK1Equiv_roots.{uRing}
    (R : Type uRing) [Ring R] :
    originalIndependentPlusK1Equiv R 0 = 0 ∧
      (originalIndependentPlusK1Equiv R).symm 0 = 0 :=
  ⟨map_zero _, map_zero _⟩

/-- EVERY original normalized stable loop maps to its actual K1.proj value;
    the original op(g inverse) edge convention is unchanged. -/
public theorem originalIndependentPlusK1Equiv_loop.{uRing}
    (R : Type uRing) [Ring R] (g : StableGL R) :
    originalIndependentPlusK1Equiv R
        (Additive.ofMul (FundamentalGroup.mapOfEq (independentBGLCellInclusion R).hom
          (independentBGLCellInclusion_point R)
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (ordinaryBGLLoop g))))) =
      K1.proj g :=
  plusTargetFundamentalAddEquivK1_loop (independentBGLCellInclusion R)
    (independentBGLCellPoint R) (independentBGLCellInclusion_point R)
    (independentBGLCellInclusion_isPlus R) (originalIndependentPlusPiOneSurjective R) g

/-- The actual inverse dictionary returns EVERY original projected stable
    class through its SAME original inclusion loop. -/
public theorem originalIndependentPlusK1Equiv_symm_proj.{uRing}
    (R : Type uRing) [Ring R] (g : StableGL R) :
    (originalIndependentPlusK1Equiv R).symm (K1.proj g) =
      Additive.ofMul (FundamentalGroup.mapOfEq (independentBGLCellInclusion R).hom
        (independentBGLCellInclusion_point R)
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (ordinaryBGLLoop g)))) := by
  apply (originalIndependentPlusK1Equiv R).injective
  exact ((originalIndependentPlusK1Equiv R).apply_symm_apply (K1.proj g)).trans
    (originalIndependentPlusK1Equiv_loop R g).symm

private theorem originalBGLScalarNormalizedLoopValue.{uR, uS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (g : StableGL R) :
    FundamentalGroup.mapOfEq (ordinaryBGLScalarMap f) (ordinaryBGLScalarMap_point f)
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (ordinaryBGLLoop g))) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (ordinaryBGLLoop (StableGL.scalarMap f g))) := by
  apply (ordinaryBGLFundamentalMulEquiv S).injective
  exact (ordinaryBGLScalarMap_fundamental f
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (ordinaryBGLLoop g)))).trans
      ((congrArg (StableGL.scalarMap f) (ordinaryBGLFundamentalMulEquiv_loop g)).trans
        (ordinaryBGLFundamentalMulEquiv_loop (StableGL.scalarMap f g)).symm)

/-- The EXACT original independent plus map carries every normalized stable
    loop to the classical class of its actual coefficient image. -/
public theorem originalIndependentPlusK1ScalarLoop.{uR, uS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (g : StableGL R) :
    originalIndependentPlusK1Equiv S
        (Additive.ofMul (FundamentalGroup.mapOfEq (independentBGLScalarPlusMap f)
          (independentBGLScalarPlusMap_point f)
          (FundamentalGroup.mapOfEq (independentBGLCellInclusion R).hom
            (independentBGLCellInclusion_point R)
            (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (ordinaryBGLLoop g)))))) =
      K1.proj (StableGL.scalarMap f g) := by
  let q := FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (ordinaryBGLLoop g))
  have hSquare := congrArg
    (fun k : FundamentalGroup (ordinaryBGL R) (ordinaryBGLBasepoint R) →*
      FundamentalGroup (independentBGLCellTarget S) (independentBGLCellPoint S) => k q)
    (independentBGLScalarPlusMap_fundamentalSquare f)
  have hScalar := originalBGLScalarNormalizedLoopValue f g
  exact (congrArg (fun p => originalIndependentPlusK1Equiv S (Additive.ofMul p)) hSquare).trans
    ((congrArg (fun p => originalIndependentPlusK1Equiv S
      (Additive.ofMul (FundamentalGroup.mapOfEq (independentBGLCellInclusion S).hom
        (independentBGLCellInclusion_point S) p))) hScalar).trans
      (originalIndependentPlusK1Equiv_loop S (StableGL.scalarMap f g)))

/-- EVERY pi1 element of the same original independent plus target has its
    scalar image under the actual canonical classical K1 map. -/
public theorem originalIndependentPlusK1Naturality.{uR, uS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S)
    (p : FundamentalGroup (independentBGLCellTarget R) (independentBGLCellPoint R)) :
    originalIndependentPlusK1Equiv S
        (Additive.ofMul (FundamentalGroup.mapOfEq (independentBGLScalarPlusMap f)
          (independentBGLScalarPlusMap_point f) p)) =
      K1.mapRingHom.{uR, uS} f (originalIndependentPlusK1Equiv R (Additive.ofMul p)) := by
  obtain ⟨q, hq⟩ := originalIndependentPlusPiOneSurjective R p
  let g := ordinaryBGLFundamentalMulEquiv R q
  have hLoop : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (ordinaryBGLLoop g)) = q :=
    (ordinaryBGLFundamentalMulEquiv R).injective (ordinaryBGLFundamentalMulEquiv_loop g)
  have hp : FundamentalGroup.mapOfEq (independentBGLCellInclusion R).hom
      (independentBGLCellInclusion_point R)
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (ordinaryBGLLoop g))) = p :=
    (congrArg (FundamentalGroup.mapOfEq (independentBGLCellInclusion R).hom
      (independentBGLCellInclusion_point R)) hLoop).trans hq
  exact (congrArg (fun z => originalIndependentPlusK1Equiv S
    (Additive.ofMul (FundamentalGroup.mapOfEq (independentBGLScalarPlusMap f)
      (independentBGLScalarPlusMap_point f) z))) hp.symm).trans
        ((originalIndependentPlusK1ScalarLoop f g).trans
          ((K1.mapRingHom_proj.{uR, uS} f g).symm.trans
            ((congrArg (K1.mapRingHom.{uR, uS} f)
              (originalIndependentPlusK1Equiv_loop R g).symm).trans
                (congrArg (fun z => K1.mapRingHom.{uR, uS} f
                  (originalIndependentPlusK1Equiv R (Additive.ofMul z))) hp))))

private theorem originalPointRelativeFundamentalMapEquality.{uX, uY}
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f g : C(X, Y)) (hf : f x = y) (hg : g x = y)
    (H : ContinuousMap.HomotopyRel f g {x}) :
    FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg := by
  apply MonoidHom.ext
  intro p
  have hTrace : ((H.toHomotopy.evalAt x).cast hf.symm hg.symm) = Path.refl y := by
    apply Path.ext
    funext t
    exact (H.eq_fst t (by rfl)).trans hf
  have h := FundamentalGroup.mapOfEq_homotopy_naturality H.toHomotopy x hf hg p
  rw [hTrace, FundamentalGroup.fundamentalGroupMulEquivOfPath_refl] at h
  exact h

/-- The whole ORIGINAL native left inverse family is retained without
    reselecting its continuous value or marked native zero root. -/
public def originalNativeK1NormalizationLeftFamily.{uRing, uModule, uNative}
    (R : Type uRing) [Ring R] :
    ContinuousMap.HomotopyRel
      ((nativeProjectiveZeroPlusNormalizationOfRing.{uRing, uModule, uNative} R).equiv.invFun.comp
        (nativeProjectiveZeroPlusNormalizationOfRing.{uRing, uModule, uNative} R).equiv.toFun)
      (ContinuousMap.id (RingK0.projectiveZeroSpace.{uRing, uModule, uNative} R))
      {RingK0.projectiveZeroPoint.{uRing, uModule, uNative} R} :=
  (nativeProjectiveZeroPlusNormalizationOfRing.{uRing, uModule, uNative} R).leftFamily

/-- The whole ORIGINAL plus right inverse family retains its original
    continuous value and the exact original marked cell point. -/
public def originalNativeK1NormalizationRightFamily.{uRing, uModule, uNative}
    (R : Type uRing) [Ring R] :
    ContinuousMap.HomotopyRel
      ((nativeProjectiveZeroPlusNormalizationOfRing.{uRing, uModule, uNative} R).equiv.toFun.comp
        (nativeProjectiveZeroPlusNormalizationOfRing.{uRing, uModule, uNative} R).equiv.invFun)
      (ContinuousMap.id (independentBGLCellTarget R)) {independentBGLCellPoint R} :=
  (nativeProjectiveZeroPlusNormalizationOfRing.{uRing, uModule, uNative} R).rightFamily

/-- BOTH complete inverse families have the literal original stored values. -/
public theorem originalNativeK1NormalizationFamilyValues.{uRing, uModule, uNative}
    (R : Type uRing) [Ring R] :
    (originalNativeK1NormalizationLeftFamily.{uRing, uModule, uNative} R).toContinuousMap =
        (nativeProjectiveZeroPlusNormalizationOfRing.{uRing, uModule, uNative} R).data.leftFamily ∧
      (originalNativeK1NormalizationRightFamily.{uRing, uModule, uNative} R).toContinuousMap =
        (nativeProjectiveZeroPlusNormalizationOfRing.{uRing, uModule, uNative} R).data.rightFamily
          :=
  ⟨(nativeProjectiveZeroPlusNormalizationOfRing.{uRing, uModule, uNative} R).fullFamilyValues.2.2.1,
    (nativeProjectiveZeroPlusNormalizationOfRing.{uRing, uModule, uNative}
      R).fullFamilyValues.2.2.2.1⟩

/-- At EVERY time, both original inverse families retain their original roots. -/
public theorem originalNativeK1NormalizationFamilyRoots.{uRing, uModule, uNative}
    (R : Type uRing) [Ring R] (t : unitInterval) :
    originalNativeK1NormalizationLeftFamily.{uRing, uModule, uNative} R
        (t, RingK0.projectiveZeroPoint.{uRing, uModule, uNative} R) =
        RingK0.projectiveZeroPoint.{uRing, uModule, uNative} R ∧
      originalNativeK1NormalizationRightFamily.{uRing, uModule, uNative} R
        (t, independentBGLCellPoint R) = independentBGLCellPoint R :=
  ⟨(originalNativeK1NormalizationLeftFamily.{uRing, uModule, uNative} R).eq_snd t (by rfl),
    (originalNativeK1NormalizationRightFamily.{uRing, uModule, uNative} R).eq_snd t (by rfl)⟩

private def originalNativeToPlusFundamentalMap.{uRing, uModule, uNative}
    (R : Type uRing) [Ring R] :
    FundamentalGroup (RingK0.projectiveZeroSpace.{uRing, uModule, uNative} R)
        (RingK0.projectiveZeroPoint.{uRing, uModule, uNative} R) →*
      FundamentalGroup (independentBGLCellTarget R) (independentBGLCellPoint R) :=
  FundamentalGroup.mapOfEq
    (nativeProjectiveZeroPlusNormalizationOfRing.{uRing, uModule, uNative} R).equiv.toFun
    (nativeProjectiveZeroPlusNormalizationOfRing.{uRing, uModule, uNative} R).forwardPoint

private def originalPlusToNativeFundamentalMap.{uRing, uModule, uNative}
    (R : Type uRing) [Ring R] :
    FundamentalGroup (independentBGLCellTarget R) (independentBGLCellPoint R) →*
      FundamentalGroup (RingK0.projectiveZeroSpace.{uRing, uModule, uNative} R)
        (RingK0.projectiveZeroPoint.{uRing, uModule, uNative} R) :=
  FundamentalGroup.mapOfEq
    (nativeProjectiveZeroPlusNormalizationOfRing.{uRing, uModule, uNative} R).equiv.invFun
    (nativeProjectiveZeroPlusNormalizationOfRing.{uRing, uModule, uNative} R).backwardPoint

private theorem originalNativePlusFundamentalLeftInverse.{uRing, uModule, uNative}
    (R : Type uRing) [Ring R] :
    (originalPlusToNativeFundamentalMap.{uRing, uModule, uNative} R).comp
        (originalNativeToPlusFundamentalMap.{uRing, uModule, uNative} R) = MonoidHom.id _ := by
  let N := nativeProjectiveZeroPlusNormalizationOfRing.{uRing, uModule, uNative} R
  let X := RingK0.projectiveZeroSpace.{uRing, uModule, uNative} R
  let x := RingK0.projectiveZeroPoint.{uRing, uModule, uNative} R
  have hPoint : (N.equiv.invFun.comp N.equiv.toFun) x = x :=
    (congrArg N.equiv.invFun N.forwardPoint).trans N.backwardPoint
  have hComp := FundamentalGroup.mapOfEq_comp N.equiv.toFun N.equiv.invFun
    N.forwardPoint N.backwardPoint hPoint
  have hRel := originalPointRelativeFundamentalMapEquality
    (N.equiv.invFun.comp N.equiv.toFun) (ContinuousMap.id X) hPoint rfl
    (originalNativeK1NormalizationLeftFamily.{uRing, uModule, uNative} R)
  exact hComp.symm.trans (hRel.trans (FundamentalGroup.mapOfEq_id x rfl))

private theorem originalNativePlusFundamentalRightInverse.{uRing, uModule, uNative}
    (R : Type uRing) [Ring R] :
    (originalNativeToPlusFundamentalMap.{uRing, uModule, uNative} R).comp
        (originalPlusToNativeFundamentalMap.{uRing, uModule, uNative} R) = MonoidHom.id _ := by
  let N := nativeProjectiveZeroPlusNormalizationOfRing.{uRing, uModule, uNative} R
  let X := independentBGLCellTarget R
  let x := independentBGLCellPoint R
  have hPoint : (N.equiv.toFun.comp N.equiv.invFun) x = x :=
    (congrArg N.equiv.toFun N.backwardPoint).trans N.forwardPoint
  have hComp := FundamentalGroup.mapOfEq_comp N.equiv.invFun N.equiv.toFun
    N.backwardPoint N.forwardPoint hPoint
  have hRel := originalPointRelativeFundamentalMapEquality
    (N.equiv.toFun.comp N.equiv.invFun) (ContinuousMap.id X) hPoint rfl
    (originalNativeK1NormalizationRightFamily.{uRing, uModule, uNative} R)
  exact hComp.symm.trans (hRel.trans (FundamentalGroup.mapOfEq_id x rfl))

/-- The original based normalization maps induce the actual pi1 equivalence;
    both inverse laws come from their original complete relative families. -/
public def originalNativePlusFundamentalMulEquiv.{uRing, uModule, uNative}
    (R : Type uRing) [Ring R] :
    FundamentalGroup (RingK0.projectiveZeroSpace.{uRing, uModule, uNative} R)
        (RingK0.projectiveZeroPoint.{uRing, uModule, uNative} R) ≃*
      FundamentalGroup (independentBGLCellTarget R) (independentBGLCellPoint R) where
  toFun := originalNativeToPlusFundamentalMap.{uRing, uModule, uNative} R
  invFun := originalPlusToNativeFundamentalMap.{uRing, uModule, uNative} R
  left_inv p := congrArg
    (fun k => k p) (originalNativePlusFundamentalLeftInverse.{uRing, uModule, uNative} R)
  right_inv p := congrArg
    (fun k => k p) (originalNativePlusFundamentalRightInverse.{uRing, uModule, uNative} R)
  map_mul' := (originalNativeToPlusFundamentalMap.{uRing, uModule, uNative} R).map_mul

/-- The actual original native zero-space pi1 dictionary is classical K1. -/
public def originalNativeK1Equiv.{uRing, uModule, uNative} (R : Type uRing) [Ring R] :
    Additive (FundamentalGroup (RingK0.projectiveZeroSpace.{uRing, uModule, uNative} R)
      (RingK0.projectiveZeroPoint.{uRing, uModule, uNative} R)) ≃+ K1 R :=
  (originalNativePlusFundamentalMulEquiv.{uRing, uModule, uNative} R).toAdditive.trans
    (originalIndependentPlusK1Equiv R)

/-- Both native K1 dictionary inverse laws hold on every original class. -/
public theorem originalNativeK1Equiv_inverse_laws.{uRing, uModule, uNative}
    (R : Type uRing) [Ring R] :
    (∀ p, (originalNativeK1Equiv.{uRing, uModule, uNative} R).symm
      (originalNativeK1Equiv.{uRing, uModule, uNative} R p) = p) ∧
    (∀ k, originalNativeK1Equiv.{uRing, uModule, uNative} R
      ((originalNativeK1Equiv.{uRing, uModule, uNative} R).symm k) = k) :=
  ⟨(originalNativeK1Equiv.{uRing, uModule, uNative} R).symm_apply_apply,
    (originalNativeK1Equiv.{uRing, uModule, uNative} R).apply_symm_apply⟩

/-- Both native dictionary directions preserve the specified identity roots. -/
public theorem originalNativeK1Equiv_roots.{uRing, uModule, uNative}
    (R : Type uRing) [Ring R] :
    originalNativeK1Equiv.{uRing, uModule, uNative} R 0 = 0 ∧
      (originalNativeK1Equiv.{uRing, uModule, uNative} R).symm 0 = 0 :=
  ⟨map_zero _, map_zero _⟩

/-- The SAME intrinsic scalar map acts by the actual canonical classical K1 map
    on EVERY native pi1 element, retaining all SIX original universe roles. -/
public theorem originalNativeK1Naturality.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S)
    (p : FundamentalGroup (RingK0.projectiveZeroSpace.{uR, uMR, uNR} R)
      (RingK0.projectiveZeroPoint.{uR, uMR, uNR} R)) :
    originalNativeK1Equiv.{uS, uMS, uNS} S
        (Additive.ofMul (FundamentalGroup.mapOfEq
          (nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f)
          (nativeProjectiveZeroScalarMap_point.{uR, uS, uMR, uMS, uNR, uNS} f) p)) =
      K1.mapRingHom.{uR, uS} f
        (originalNativeK1Equiv.{uR, uMR, uNR} R (Additive.ofMul p)) := by
  let A := nativeProjectiveZeroPlusNormalizationOfRing.{uR, uMR, uNR} R
  let B := nativeProjectiveZeroPlusNormalizationOfRing.{uS, uMS, uNS} S
  let psi := nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f
  let Pmap := independentBGLScalarPlusMap f
  let x := RingK0.projectiveZeroPoint.{uR, uMR, uNR} R
  have hLeft : (Pmap.comp A.equiv.toFun) x = independentBGLCellPoint S :=
    (congrArg Pmap A.forwardPoint).trans (independentBGLScalarPlusMap_point f)
  have hRight : (B.equiv.toFun.comp psi) x = independentBGLCellPoint S :=
    (congrArg B.equiv.toFun
      (nativeProjectiveZeroScalarMap_point.{uR, uS, uMR, uMS, uNR, uNS} f)).trans B.forwardPoint
  have hRel := originalPointRelativeFundamentalMapEquality
    (Pmap.comp A.equiv.toFun) (B.equiv.toFun.comp psi) hLeft hRight
    (nativeProjectiveZeroScalarOriginalForwardSquare.{uR, uS, uMR, uMS, uNR, uNS} f)
  have hCompLeft := FundamentalGroup.mapOfEq_comp A.equiv.toFun Pmap
    A.forwardPoint (independentBGLScalarPlusMap_point f) hLeft
  have hCompRight := FundamentalGroup.mapOfEq_comp psi B.equiv.toFun
    (nativeProjectiveZeroScalarMap_point.{uR, uS, uMR, uMS, uNR, uNS} f) B.forwardPoint hRight
  have hTriangle := hCompLeft.symm.trans (hRel.trans hCompRight)
  have hAt := congrArg
    (fun k : FundamentalGroup (RingK0.projectiveZeroSpace.{uR, uMR, uNR} R) x →*
      FundamentalGroup (independentBGLCellTarget S) (independentBGLCellPoint S) => k p) hTriangle
  change originalIndependentPlusK1Equiv S
    (Additive.ofMul ((originalNativeToPlusFundamentalMap.{uS, uMS, uNS} S)
      (FundamentalGroup.mapOfEq psi
        (nativeProjectiveZeroScalarMap_point.{uR, uS, uMR, uMS, uNR, uNS} f) p))) =
    K1.mapRingHom.{uR, uS} f
      (originalIndependentPlusK1Equiv R
        (Additive.ofMul (originalNativeToPlusFundamentalMap.{uR, uMR, uNR} R p)))
  exact (congrArg (fun q => originalIndependentPlusK1Equiv S (Additive.ofMul q)) hAt).symm.trans
    (originalIndependentPlusK1Naturality f
      (originalNativeToPlusFundamentalMap.{uR, uMR, uNR} R p))

end AlgebraicKTheory.StableGL

end
