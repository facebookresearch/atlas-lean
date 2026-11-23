/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.Comparison.OriginalNormalizedQSourceComparison
public import MathlibExt.Topology.Homotopy.PositivePathComponentInclusion
public import MathlibExt.Topology.Homotopy.BasedHomotopyGroupEquivalence

/-!
# Genuine canonical normalized positive Q/plus comparison

Original zero-component, native-realization, Core and Q comparison maps give
positive group isomorphisms. The original normalization then gives a genuine
plus/Q comparison. Both directions and original inverse families are retained;
the scalar/root/own-unit comparison is a separate required next proof.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open CategoryTheory.CoreLocalizationComparison
open CategoryTheory.SInverseS.ComponentTranslation
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ContinuousMap
    Topology

attribute [local instance] MonoidalActionCategory.diagonalAction

namespace AlgebraicKTheory.QuillenPlus

private def originalPointedHomeoPositiveEquiv.{uX, uY}
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) (x : X) (y : Y) (hy : h x = y) (n : ℕ) :
    HomotopyGroup.Pi (n + 1) X x ≃* HomotopyGroup.Pi (n + 1) Y y := by
  let f : C(X, Y) := ⟨h, h.continuous_toFun⟩
  let g : C(Y, X) := ⟨h.symm, h.continuous_invFun⟩
  have hg : g y = x := (congrArg h.symm hy).symm.trans (h.symm_apply_apply x)
  have hL : g.comp f = ContinuousMap.id X := by
    apply ContinuousMap.ext
    intro a
    exact h.symm_apply_apply a
  have hR : f.comp g = ContinuousMap.id Y := by
    apply ContinuousMap.ext
    intro b
    exact h.apply_symm_apply b
  let L := (ContinuousMap.HomotopyRel.refl (ContinuousMap.id X) {x}).cast hL.symm rfl
  let R := (ContinuousMap.HomotopyRel.refl (ContinuousMap.id Y) {y}).cast hR.symm rfl
  exact HomotopyGroup.mulEquivOfBasedInverse n f g hy hg L R

private theorem originalPointedHomeoPositiveEquivValue.{uX, uY}
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) (x : X) (y : Y) (hy : h x = y) (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) X x) :
    originalPointedHomeoPositiveEquiv h x y hy n a =
      HomotopyGroup.mapHomOfEq (⟨h, h.continuous_toFun⟩ : C(X, Y)) hy n a := by
  unfold originalPointedHomeoPositiveEquiv
  exact HomotopyGroup.mulEquivOfBasedInverse_apply _ _ _ _ _ _ _ a

private theorem originalPointedHomeoPositiveEquivSymmValue.{uX, uY}
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) (x : X) (y : Y) (hy : h x = y) (n : ℕ)
    (b : HomotopyGroup.Pi (n + 1) Y y) :
    (originalPointedHomeoPositiveEquiv h x y hy n).symm b =
      HomotopyGroup.mapHomOfEq (⟨h.symm, h.continuous_invFun⟩ : C(Y, X))
        ((congrArg h.symm hy).symm.trans (h.symm_apply_apply x)) n b := by
  unfold originalPointedHomeoPositiveEquiv
  exact HomotopyGroup.mulEquivOfBasedInverse_symm_apply _ _ _ _ _ _ _ b

private theorem originalPositiveMapCongr.{uX, uY}
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (n : ℕ) (f g : C(X, Y)) (hf : f x = y) (hg : g x = y)
    (h : f = g) (a : HomotopyGroup.Pi (n + 1) X x) :
    HomotopyGroup.mapHomOfEq f hf n a = HomotopyGroup.mapHomOfEq g hg n a := by
  cases h
  rfl

private theorem originalCoreFunctorLeftIdentity.{uR, uM} (R : Type uR) [Ring R] :
    (coreAdditivePairEquivalence (C := FGProjectiveCat.{max uR uM} R)).functor ⋙
      (coreAdditivePairEquivalence (C := FGProjectiveCat.{max uR uM} R)).inverse =
        𝟭 (SInverse (Core (FGProjectiveCat.{max uR uM} R))
          (Core (FGProjectiveCat.{max uR uM} R))) := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
  intro a b f
  change HEq ((fromPairFunctor (C := FGProjectiveCat.{max uR uM} R)).map
    ((toPairFunctor (C := FGProjectiveCat.{max uR uM} R)).map f)) f
  exact heq_of_eq (from_to_map f)

private theorem originalCoreFunctorRightIdentity.{uR, uM} (R : Type uR) [Ring R] :
    (coreAdditivePairEquivalence (C := FGProjectiveCat.{max uR uM} R)).inverse ⋙
      (coreAdditivePairEquivalence (C := FGProjectiveCat.{max uR uM} R)).functor =
        𝟭 (SInverseS.Pair (FGProjectiveCat.{max uR uM} R)) := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
  intro a b f
  change HEq ((toPairFunctor (C := FGProjectiveCat.{max uR uM} R)).map
    ((fromPairFunctor (C := FGProjectiveCat.{max uR uM} R)).map f)) f
  exact heq_of_eq (to_from_map f)

private def originalCorePairRealizationHomeo.{uR, uM} (R : Type uR) [Ring R] :
    BasedSplitExactQLoop.completedCoreSpace (C := FGProjectiveCat.{max uR uM} R) ≃ₜ
      originalSpace (C := FGProjectiveCat.{max uR uM} R) := by
  let C := FGProjectiveCat.{max uR uM} R
  let E := coreAdditivePairEquivalence (C := C)
  let F := SSet.toTop.map (nerveMap E.functor)
  let G := SSet.toTop.map (nerveMap E.inverse)
  have hNerveL : nerveMap E.functor ≫ nerveMap E.inverse = 𝟙 (nerve (SInverse (Core C) (Core C))) :=
    (nerveMap_comp E.functor E.inverse).trans
      ((congrArg nerveMap (originalCoreFunctorLeftIdentity.{uR, uM} R)).trans nerveMap_id)
  have hNerveR : nerveMap E.inverse ≫ nerveMap E.functor = 𝟙 (nerve (SInverseS.Pair C)) :=
    (nerveMap_comp E.inverse E.functor).trans
      ((congrArg nerveMap (originalCoreFunctorRightIdentity.{uR, uM} R)).trans nerveMap_id)
  have hTopL : F ≫ G = 𝟙 (BasedSplitExactQLoop.completedCoreSpace (C := C)) :=
    (SSet.toTop.map_comp _ _).symm.trans
      ((congrArg SSet.toTop.map hNerveL).trans (SSet.toTop.map_id _))
  have hTopR : G ≫ F = 𝟙 (originalSpace (C := C)) :=
    (SSet.toTop.map_comp _ _).symm.trans
      ((congrArg SSet.toTop.map hNerveR).trans (SSet.toTop.map_id _))
  exact
    { toFun := F
      invFun := G
      left_inv := fun x => (TopCat.comp_app F G x).symm.trans
        (ConcreteCategory.congr_hom hTopL x)
      right_inv := fun y => (TopCat.comp_app G F y).symm.trans
        (ConcreteCategory.congr_hom hTopR y)
      continuous_toFun := F.hom.continuous
      continuous_invFun := G.hom.continuous }

private theorem originalCorePairRealizationPoint.{uR, uM} (R : Type uR) [Ring R] :
    originalCorePairRealizationHomeo.{uR, uM} R
      (BasedSplitExactQLoop.completedCorePoint (C := FGProjectiveCat.{max uR uM} R)) =
      originalSpacePoint (C := FGProjectiveCat.{max uR uM} R) := by
  let C := FGProjectiveCat.{max uR uM} R
  let E := coreAdditivePairEquivalence (C := C)
  let x := (SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C))
  have hObj : E.functor.obj x = (⟨0, 0⟩ : SInverseS.Pair C) := by
    rw [coreAdditivePairEquivalence_functor_obj]
    rfl
  have hVertex := (SSet.realizedVertex_naturality (nerveMap E.functor)
    (ComposableArrows.mk₀ x)).symm
  exact hVertex.trans ((congrArg (SSet.realizedVertex (X := nerve (SInverseS.Pair C)))
    (nerveMap_app_mk₀ E.functor x)).trans
      ((congrArg (fun y : SInverseS.Pair C => SSet.realizedVertex
        (X := nerve (SInverseS.Pair C)) (ComposableArrows.mk₀ y)) hObj).trans
        (originalSpacePoint_eq_realizedVertex (C := C)).symm))

private def originalCorePairPositiveEquiv.{uR, uM} (R : Type uR) [Ring R] (n : ℕ) :
    HomotopyGroup.Pi (n + 1) (BasedSplitExactQLoop.completedCoreSpace
      (C := FGProjectiveCat.{max uR uM} R))
      (BasedSplitExactQLoop.completedCorePoint (C := FGProjectiveCat.{max uR uM} R)) ≃*
    HomotopyGroup.Pi (n + 1) (originalSpace (C := FGProjectiveCat.{max uR uM} R))
      (originalSpacePoint (C := FGProjectiveCat.{max uR uM} R)) :=
  originalPointedHomeoPositiveEquiv (originalCorePairRealizationHomeo.{uR, uM} R)
    _ _ (originalCorePairRealizationPoint.{uR, uM} R) n

private def originalCoreQPositiveEquiv.{uR, uM} (R : Type uR) [Ring R] (n : ℕ) :
    HomotopyGroup.Pi (n + 1) (BasedSplitExactQLoop.completedCoreSpace
      (C := FGProjectiveCat.{max uR uM} R))
      (BasedSplitExactQLoop.completedCorePoint (C := FGProjectiveCat.{max uR uM} R)) ≃*
    HomotopyGroup.Pi (n + 1) (BasedSplitExactQLoop.originalQLoops
      (C := FGProjectiveCat.{max uR uM} R))
      (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR uM} R)) := by
  let C := FGProjectiveCat.{max uR uM} R
  let D := BasedSplitExactQLoop.comparison (C := C)
    (originalCanonicalProjectiveSplitRows.{uR, uM} R)
  exact HomotopyGroup.mulEquivOfBasedInverse n (BasedSplitExactQLoop.comparisonMap (C := C)).hom
    D.loopInverse (BasedSplitExactQLoop.comparisonMap_point (C := C)) D.loopInverse_point
      D.loopSourceHomotopy D.loopTargetHomotopy

private def originalNativeZeroPairPositiveEquiv.{uR, uM, uNative}
    (R : Type uR) [Ring R] (n : ℕ) :
    HomotopyGroup.Pi (n + 1) (RingK0.projectiveZeroSpace.{uR, uM, uNative} R)
      (RingK0.projectiveZeroPoint.{uR, uM, uNative} R) ≃*
    HomotopyGroup.Pi (n + 1)
      (nativeOriginalSpace.{max uR uM + 1, max uR uM, uNative}
        (C := FGProjectiveCat.{max uR uM} R))
      (nativeOriginalPoint.{max uR uM + 1, max uR uM, uNative}
        (C := FGProjectiveCat.{max uR uM} R)) := by
  let C := FGProjectiveCat.{max uR uM} R
  let h := nativeZeroPathComponentHomeomorph.{max uR uM + 1, max uR uM, uNative} (C := C)
  let z := RingK0.projectiveZeroPoint.{uR, uM, uNative} R
  let x := nativeOriginalPoint.{max uR uM + 1, max uR uM, uNative} (C := C)
  let y : pathComponent x := ⟨x, mem_pathComponent_self x⟩
  have hy : h z = y :=
    (congrArg h (RingK0.projectiveZeroPoint_eq_native.{uR, uM, uNative} R)).trans
      (nativeZeroPathComponentHomeomorph_point.{max uR uM + 1, max uR uM, uNative} (C := C))
  exact (originalPointedHomeoPositiveEquiv h z y hy n).trans
    (HomotopyGroup.positivePathComponentInclusionMulEquiv n x)

private def originalNativePairOrdinaryPositiveEquiv.{uR, uM, uNative}
    (R : Type uR) [Ring R] (n : ℕ) :
    HomotopyGroup.Pi (n + 1)
      (nativeOriginalSpace.{max uR uM + 1, max uR uM, uNative}
        (C := FGProjectiveCat.{max uR uM} R))
      (nativeOriginalPoint.{max uR uM + 1, max uR uM, uNative}
        (C := FGProjectiveCat.{max uR uM} R)) ≃*
    HomotopyGroup.Pi (n + 1) (originalSpace (C := FGProjectiveCat.{max uR uM} R))
      (originalSpacePoint (C := FGProjectiveCat.{max uR uM} R)) := by
  let C := FGProjectiveCat.{max uR uM} R
  let I := nativeOriginalRealizationIso.{max uR uM + 1, max uR uM, uNative} (C := C)
  let h := TopCat.homeoOfIso I
  exact originalPointedHomeoPositiveEquiv h _ _
    (nativeOriginalRealizationIso_point.{max uR uM + 1, max uR uM, uNative} (C := C)) n

private theorem originalNativeZeroPairPositiveEquivValue.{uR, uM, uNative}
    (R : Type uR) [Ring R] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (RingK0.projectiveZeroSpace.{uR, uM, uNative} R)
      (RingK0.projectiveZeroPoint.{uR, uM, uNative} R)) :
    originalNativeZeroPairPositiveEquiv.{uR, uM, uNative} R n a =
      HomotopyGroup.mapHomOfEq
        (nativeZeroInclusion.{max uR uM + 1, max uR uM, uNative}
          (C := FGProjectiveCat.{max uR uM} R))
        ((congrArg
          (nativeZeroInclusion.{max uR uM + 1, max uR uM, uNative}
            (C := FGProjectiveCat.{max uR uM} R))
          (RingK0.projectiveZeroPoint_eq_native.{uR, uM, uNative} R)).trans
          (nativeZeroInclusion_point.{max uR uM + 1, max uR uM, uNative}
            (C := FGProjectiveCat.{max uR uM} R))) n a := by
  let C := FGProjectiveCat.{max uR uM} R
  let h := nativeZeroPathComponentHomeomorph.{max uR uM + 1, max uR uM, uNative} (C := C)
  let z := RingK0.projectiveZeroPoint.{uR, uM, uNative} R
  let q := nativeOriginalPoint.{max uR uM + 1, max uR uM, uNative} (C := C)
  let y : pathComponent q := ⟨q, mem_pathComponent_self q⟩
  let f : C(RingK0.projectiveZeroSpace.{uR, uM, uNative} R, pathComponent q) :=
    ⟨h, h.continuous_toFun⟩
  let j : C(pathComponent q, nativeOriginalSpace.{max uR uM + 1, max uR uM, uNative}
      (C := C)) := ⟨Subtype.val, continuous_subtype_val⟩
  let J := nativeZeroInclusion.{max uR uM + 1, max uR uM, uNative} (C := C)
  have hf : f z = y :=
    (congrArg h (RingK0.projectiveZeroPoint_eq_native.{uR, uM, uNative} R)).trans
      (nativeZeroPathComponentHomeomorph_point.{max uR uM + 1, max uR uM, uNative} (C := C))
  have hJ : J z = q :=
    (congrArg J (RingK0.projectiveZeroPoint_eq_native.{uR, uM, uNative} R)).trans
      (nativeZeroInclusion_point.{max uR uM + 1, max uR uM, uNative} (C := C))
  have hComp : (j.comp f) z = q := congrArg j hf
  have hMaps : j.comp f = J := by
    apply ContinuousMap.ext
    intro t
    exact nativeZeroPathComponentHomeomorph_apply.{max uR uM + 1, max uR uM, uNative} (C := C) t
  have h0 := originalPointedHomeoPositiveEquivValue h z y hf n a
  have h1 := HomotopyGroup.mapHomOfEq_comp f j hf rfl hComp n a
  have h2 := originalPositiveMapCongr n (j.comp f) J hComp hJ hMaps a
  unfold originalNativeZeroPairPositiveEquiv
  rw [MulEquiv.trans_apply, HomotopyGroup.positivePathComponentInclusionMulEquiv_apply]
  rw [h0]
  have hIncl : HomotopyGroup.map j (HomotopyGroup.mapHomOfEq f hf n a) =
      HomotopyGroup.mapHomOfEq j rfl n (HomotopyGroup.mapHomOfEq f hf n a) := by
    exact (HomotopyGroup.mapHomOfEq_apply j (rfl : j y = q) n
      (HomotopyGroup.mapHomOfEq f hf n a)).symm
  exact hIncl.trans (h1.symm.trans h2)

private theorem originalNativePairOrdinaryPositiveEquivValue.{uR, uM, uNative}
    (R : Type uR) [Ring R] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1)
      (nativeOriginalSpace.{max uR uM + 1, max uR uM, uNative}
        (C := FGProjectiveCat.{max uR uM} R))
      (nativeOriginalPoint.{max uR uM + 1, max uR uM, uNative}
        (C := FGProjectiveCat.{max uR uM} R))) :
    originalNativePairOrdinaryPositiveEquiv.{uR, uM, uNative} R n a =
      HomotopyGroup.mapHomOfEq
        (nativeOriginalRealizationIso.{max uR uM + 1, max uR uM, uNative}
          (C := FGProjectiveCat.{max uR uM} R)).hom.hom
        (nativeOriginalRealizationIso_point.{max uR uM + 1, max uR uM, uNative}
          (C := FGProjectiveCat.{max uR uM} R)) n a := by
  unfold originalNativePairOrdinaryPositiveEquiv
  exact originalPointedHomeoPositiveEquivValue _ _ _ _ n a

private theorem originalCoreInverseRealizationPoint.{uR, uM} (R : Type uR) [Ring R] :
    (SSet.toTop.map (nerveMap
      (coreAdditivePairEquivalence (C := FGProjectiveCat.{max uR uM} R)).inverse))
      (originalSpacePoint (C := FGProjectiveCat.{max uR uM} R)) =
      BasedSplitExactQLoop.completedCorePoint (C := FGProjectiveCat.{max uR uM} R) := by
  let h := originalCorePairRealizationHomeo.{uR, uM} R
  have hPoint := originalCorePairRealizationPoint.{uR, uM} R
  exact (congrArg h.symm hPoint).symm.trans (h.symm_apply_apply _)

private theorem originalCorePairPositiveEquivSymmValue.{uR, uM}
    (R : Type uR) [Ring R] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (originalSpace (C := FGProjectiveCat.{max uR uM} R))
      (originalSpacePoint (C := FGProjectiveCat.{max uR uM} R))) :
    (originalCorePairPositiveEquiv.{uR, uM} R n).symm a =
      HomotopyGroup.mapHomOfEq (SSet.toTop.map (nerveMap
        (coreAdditivePairEquivalence (C := FGProjectiveCat.{max uR uM} R)).inverse)).hom
        (originalCoreInverseRealizationPoint.{uR, uM} R) n a := by
  unfold originalCorePairPositiveEquiv
  exact originalPointedHomeoPositiveEquivSymmValue _ _ _ _ n a

private theorem originalCoreQPositiveEquivValue.{uR, uM} (R : Type uR) [Ring R] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (BasedSplitExactQLoop.completedCoreSpace
      (C := FGProjectiveCat.{max uR uM} R))
      (BasedSplitExactQLoop.completedCorePoint (C := FGProjectiveCat.{max uR uM} R))) :
    originalCoreQPositiveEquiv.{uR, uM} R n a = HomotopyGroup.mapHomOfEq
      (BasedSplitExactQLoop.comparisonMap (C := FGProjectiveCat.{max uR uM} R)).hom
      (BasedSplitExactQLoop.comparisonMap_point (C := FGProjectiveCat.{max uR uM} R)) n a := by
  unfold originalCoreQPositiveEquiv
  exact HomotopyGroup.mulEquivOfBasedInverse_apply _ _ _ _ _ _ _ a

/-- The original component/Core/Q recipes give a genuine positive native-zero/Q isomorphism. -/
public def originalNativeZeroQPositiveMulEquiv.{uR, uM, uNative}
    (R : Type uR) [Ring R] (n : ℕ) :
    HomotopyGroup.Pi (n + 1) (RingK0.projectiveZeroSpace.{uR, uM, uNative} R)
      (RingK0.projectiveZeroPoint.{uR, uM, uNative} R) ≃*
    HomotopyGroup.Pi (n + 1) (BasedSplitExactQLoop.originalQLoops
      (C := FGProjectiveCat.{max uR uM} R))
      (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR uM} R)) :=
  (originalNativeZeroPairPositiveEquiv.{uR, uM, uNative} R n).trans
    ((originalNativePairOrdinaryPositiveEquiv.{uR, uM, uNative} R n).trans
      ((originalCorePairPositiveEquiv.{uR, uM} R n).symm.trans
        (originalCoreQPositiveEquiv.{uR, uM} R n)))

/-- EXACT226 normalization and canonical Q maps give every positive plus/Q isomorphism. -/
public def originalNormalizedPlusQPositiveMulEquiv.{uR, uM, uNative}
    (R : Type uR) [Ring R] (n : ℕ) :
    HomotopyGroup.Pi (n + 1) (StableGL.independentBGLCellTarget R)
      (StableGL.independentBGLCellPoint R) ≃*
    HomotopyGroup.Pi (n + 1) (BasedSplitExactQLoop.originalQLoops
      (C := FGProjectiveCat.{max uR uM} R))
      (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR uM} R)) :=
  (StableGL.originalNativePlusPositiveMulEquiv.{uR, uM, uNative} R n).symm.trans
    (originalNativeZeroQPositiveMulEquiv.{uR, uM, uNative} R n)

private theorem originalNativeZeroQPositiveApplyComputed.{uR, uM, uNative}
    (R : Type uR) [Ring R] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (RingK0.projectiveZeroSpace.{uR, uM, uNative} R)
      (RingK0.projectiveZeroPoint.{uR, uM, uNative} R)) :
    originalNativeZeroQPositiveMulEquiv.{uR, uM, uNative} R n a =
      HomotopyGroup.mapHomOfEq (originalNativeZeroToQLoops.{uR, uM, uNative} R)
        (originalNativeZeroToQLoops_point.{uR, uM, uNative} R) n a := by
  let C := FGProjectiveCat.{max uR uM} R
  let z := RingK0.projectiveZeroPoint.{uR, uM, uNative} R
  let p := nativeOriginalPoint.{max uR uM + 1, max uR uM, uNative} (C := C)
  let q := originalSpacePoint (C := C)
  let u := BasedSplitExactQLoop.completedCorePoint (C := C)
  let v := BasedSplitExactQLoop.constantQLoop (C := C)
  let J := nativeZeroInclusion.{max uR uM + 1, max uR uM, uNative} (C := C)
  let I := (nativeOriginalRealizationIso.{max uR uM + 1, max uR uM, uNative} (C := C)).hom.hom
  let G := (SSet.toTop.map (nerveMap (coreAdditivePairEquivalence (C := C)).inverse)).hom
  let K := (BasedSplitExactQLoop.comparisonMap (C := C)).hom
  have hJ : J z = p :=
    (congrArg J (RingK0.projectiveZeroPoint_eq_native.{uR, uM, uNative} R)).trans
      (nativeZeroInclusion_point.{max uR uM + 1, max uR uM, uNative} (C := C))
  have hI : I p = q :=
    nativeOriginalRealizationIso_point.{max uR uM + 1, max uR uM, uNative} (C := C)
  have hG : G q = u := originalCoreInverseRealizationPoint.{uR, uM} R
  have hK : K u = v := BasedSplitExactQLoop.comparisonMap_point (C := C)
  have hIJ : (I.comp J) z = q := (congrArg I hJ).trans hI
  have hGIJ : (G.comp (I.comp J)) z = u := (congrArg G hIJ).trans hG
  have hFinal : (K.comp (G.comp (I.comp J))) z = v := (congrArg K hGIJ).trans hK
  have h1 := HomotopyGroup.mapHomOfEq_comp J I hJ hI hIJ n a
  have h2 := HomotopyGroup.mapHomOfEq_comp (I.comp J) G hIJ hG hGIJ n a
  have h3 := HomotopyGroup.mapHomOfEq_comp (G.comp (I.comp J)) K hGIJ hK hFinal n a
  have hMaps : K.comp (G.comp (I.comp J)) = originalNativeZeroToQLoops.{uR, uM, uNative} R :=
    (originalNativeZeroToQLoops_value.{uR, uM, uNative} R).symm
  have h4 := originalPositiveMapCongr n (K.comp (G.comp (I.comp J)))
    (originalNativeZeroToQLoops.{uR, uM, uNative} R) hFinal
    (originalNativeZeroToQLoops_point.{uR, uM, uNative} R) hMaps a
  unfold originalNativeZeroQPositiveMulEquiv
  simp only [MulEquiv.trans_apply]
  rw [originalNativeZeroPairPositiveEquivValue, originalNativePairOrdinaryPositiveEquivValue,
    originalCorePairPositiveEquivSymmValue, originalCoreQPositiveEquivValue]
  exact (congrArg
    (fun b => HomotopyGroup.mapHomOfEq K hK n (HomotopyGroup.mapHomOfEq G hG n b)) h1.symm).trans
      ((congrArg (HomotopyGroup.mapHomOfEq K hK n) h2.symm).trans (h3.symm.trans h4))

/-- Every positive native/Q value uses EXACT131 original inclusion/Core/κ map. -/
public theorem originalNativeZeroQPositiveMulEquiv_apply.{uR, uM, uNative}
    (R : Type uR) [Ring R] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (RingK0.projectiveZeroSpace.{uR, uM, uNative} R)
      (RingK0.projectiveZeroPoint.{uR, uM, uNative} R)) :
    originalNativeZeroQPositiveMulEquiv.{uR, uM, uNative} R n a =
      HomotopyGroup.mapHomOfEq (originalNativeZeroToQLoops.{uR, uM, uNative} R)
        (originalNativeZeroToQLoops_point.{uR, uM, uNative} R) n a :=
  originalNativeZeroQPositiveApplyComputed R n a

private theorem originalNormalizedPlusQPositiveApplyComputed.{uR, uM, uNative}
    (R : Type uR) [Ring R] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (StableGL.independentBGLCellTarget R)
      (StableGL.independentBGLCellPoint R)) :
    originalNormalizedPlusQPositiveMulEquiv.{uR, uM, uNative} R n a =
      HomotopyGroup.mapHomOfEq (originalNormalizedPlusToQLoops.{uR, uM, uNative} R)
        (originalNormalizedPlusToQLoops_point.{uR, uM, uNative} R) n a := by
  let N := StableGL.nativeProjectiveZeroPlusNormalizationOfRing.{uR, uM, uNative} R
  let Q := originalNativeZeroToQLoops.{uR, uM, uNative} R
  let x := StableGL.independentBGLCellPoint R
  let y := BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR uM} R)
  have hQ := originalNativeZeroToQLoops_point.{uR, uM, uNative} R
  have hComp : (Q.comp N.equiv.invFun) x = y := (congrArg Q N.backwardPoint).trans hQ
  have h1 := HomotopyGroup.mapHomOfEq_comp N.equiv.invFun Q N.backwardPoint hQ hComp n a
  have hMaps : Q.comp N.equiv.invFun = originalNormalizedPlusToQLoops.{uR, uM, uNative} R :=
    (originalNormalizedPlusToQLoops_value.{uR, uM, uNative} R).symm
  have h2 := originalPositiveMapCongr n (Q.comp N.equiv.invFun)
    (originalNormalizedPlusToQLoops.{uR, uM, uNative} R) hComp
    (originalNormalizedPlusToQLoops_point.{uR, uM, uNative} R) hMaps a
  unfold originalNormalizedPlusQPositiveMulEquiv
  rw [MulEquiv.trans_apply, StableGL.originalNativePlusPositiveMulEquiv_symm_apply,
    originalNativeZeroQPositiveMulEquiv_apply]
  exact h1.symm.trans h2

/-- Every positive plus/Q value uses EXACT131 source-bearing map with EXACT226 backward. -/
public theorem originalNormalizedPlusQPositiveMulEquiv_apply.{uR, uM, uNative}
    (R : Type uR) [Ring R] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (StableGL.independentBGLCellTarget R)
      (StableGL.independentBGLCellPoint R)) :
    originalNormalizedPlusQPositiveMulEquiv.{uR, uM, uNative} R n a =
      HomotopyGroup.mapHomOfEq (originalNormalizedPlusToQLoops.{uR, uM, uNative} R)
        (originalNormalizedPlusToQLoops_point.{uR, uM, uNative} R) n a :=
  originalNormalizedPlusQPositiveApplyComputed R n a

/-- The positive class return follows original Q/Core/native maps and132's actual component lift. -/
public def originalQLoopsToNativeZeroPositiveMap.{uR, uM, uNative}
    (R : Type uR) [Ring R] (n : ℕ) :
    HomotopyGroup.Pi (n + 1) (BasedSplitExactQLoop.originalQLoops
      (C := FGProjectiveCat.{max uR uM} R))
      (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR uM} R)) →
    HomotopyGroup.Pi (n + 1) (RingK0.projectiveZeroSpace.{uR, uM, uNative} R)
      (RingK0.projectiveZeroPoint.{uR, uM, uNative} R) := fun a =>
  (originalNativeZeroPairPositiveEquiv.{uR, uM, uNative} R n).symm
    ((originalNativePairOrdinaryPositiveEquiv.{uR, uM, uNative} R n).symm
      (originalCorePairPositiveEquiv.{uR, uM} R n
        ((originalCoreQPositiveEquiv.{uR, uM} R n).symm a)))

private theorem originalNativeZeroQPositiveSymmApplyComputed.{uR, uM, uNative}
    (R : Type uR) [Ring R] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (BasedSplitExactQLoop.originalQLoops
      (C := FGProjectiveCat.{max uR uM} R))
      (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR uM} R))) :
    (originalNativeZeroQPositiveMulEquiv.{uR, uM, uNative} R n).symm a =
      originalQLoopsToNativeZeroPositiveMap.{uR, uM, uNative} R n a := by
  unfold originalNativeZeroQPositiveMulEquiv originalQLoopsToNativeZeroPositiveMap
  rfl

/-- Inverse native/Q classes use the original return maps and actual component lift. -/
public theorem originalNativeZeroQPositiveMulEquiv_symm_apply.{uR, uM, uNative}
    (R : Type uR) [Ring R] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (BasedSplitExactQLoop.originalQLoops
      (C := FGProjectiveCat.{max uR uM} R))
      (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR uM} R))) :
    (originalNativeZeroQPositiveMulEquiv.{uR, uM, uNative} R n).symm a =
      originalQLoopsToNativeZeroPositiveMap.{uR, uM, uNative} R n a :=
  originalNativeZeroQPositiveSymmApplyComputed R n a

private theorem originalNormalizedPlusQPositiveSymmApplyComputed.{uR, uM, uNative}
    (R : Type uR) [Ring R] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (BasedSplitExactQLoop.originalQLoops
      (C := FGProjectiveCat.{max uR uM} R))
      (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR uM} R))) :
    (originalNormalizedPlusQPositiveMulEquiv.{uR, uM, uNative} R n).symm a =
      StableGL.originalNativePlusPositiveMulEquiv.{uR, uM, uNative} R n
        (originalQLoopsToNativeZeroPositiveMap.{uR, uM, uNative} R n a) := by
  unfold originalNormalizedPlusQPositiveMulEquiv
  rw [MulEquiv.symm_trans_apply, originalNativeZeroQPositiveMulEquiv_symm_apply]
  rfl

/-- Every Q/plus inverse class returns through the SAME original maps then EXACT226forward. -/
public theorem originalNormalizedPlusQPositiveMulEquiv_symm_apply.{uR, uM, uNative}
    (R : Type uR) [Ring R] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (BasedSplitExactQLoop.originalQLoops
      (C := FGProjectiveCat.{max uR uM} R))
      (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR uM} R))) :
    (originalNormalizedPlusQPositiveMulEquiv.{uR, uM, uNative} R n).symm a =
      StableGL.originalNativePlusPositiveMulEquiv.{uR, uM, uNative} R n
        (originalQLoopsToNativeZeroPositiveMap.{uR, uM, uNative} R n a) :=
  originalNormalizedPlusQPositiveSymmApplyComputed R n a

/-- Both genuine positive plus/Q maps are inverse on ALL original classes. -/
public theorem originalNormalizedPlusQPositiveMulEquiv_inverse_laws.{uR, uM, uNative}
    (R : Type uR) [Ring R] (n : ℕ) :
    (∀ a, (originalNormalizedPlusQPositiveMulEquiv.{uR, uM, uNative} R n).symm
      (originalNormalizedPlusQPositiveMulEquiv.{uR, uM, uNative} R n a) = a) ∧
    (∀ b, originalNormalizedPlusQPositiveMulEquiv.{uR, uM, uNative} R n
      ((originalNormalizedPlusQPositiveMulEquiv.{uR, uM, uNative} R n).symm b) = b) :=
  ⟨(originalNormalizedPlusQPositiveMulEquiv.{uR, uM, uNative} R n).symm_apply_apply,
    (originalNormalizedPlusQPositiveMulEquiv.{uR, uM, uNative} R n).apply_symm_apply⟩

/-- Every positive comparison retains its own original group unit in both directions. -/
public theorem originalNormalizedPlusQPositiveMulEquiv_units.{uR, uM, uNative}
    (R : Type uR) [Ring R] (n : ℕ) :
    originalNormalizedPlusQPositiveMulEquiv.{uR, uM, uNative} R n 1 = 1 ∧
      (originalNormalizedPlusQPositiveMulEquiv.{uR, uM, uNative} R n).symm 1 = 1 :=
  ⟨(originalNormalizedPlusQPositiveMulEquiv.{uR, uM, uNative} R n).map_one,
    (originalNormalizedPlusQPositiveMulEquiv.{uR, uM, uNative} R n).symm.map_one⟩

/-- All positive original class formulas and both inverse laws retain the BGL source triangle. -/
public theorem originalNormalizedPlusQPositiveComparison_allIndices.{uR, uM, uNative}
    (R : Type uR) [Ring R] :
    (∀ n a, originalNormalizedPlusQPositiveMulEquiv.{uR, uM, uNative} R n a =
      HomotopyGroup.mapHomOfEq (originalNormalizedPlusToQLoops.{uR, uM, uNative} R)
        (originalNormalizedPlusToQLoops_point.{uR, uM, uNative} R) n a) ∧
    (∀ n b, (originalNormalizedPlusQPositiveMulEquiv.{uR, uM, uNative} R n).symm b =
      StableGL.originalNativePlusPositiveMulEquiv.{uR, uM, uNative} R n
        (originalQLoopsToNativeZeroPositiveMap.{uR, uM, uNative} R n b)) ∧
    (∀ n, (∀ a, (originalNormalizedPlusQPositiveMulEquiv.{uR, uM, uNative} R n).symm
      (originalNormalizedPlusQPositiveMulEquiv.{uR, uM, uNative} R n a) = a) ∧
      (∀ b, originalNormalizedPlusQPositiveMulEquiv.{uR, uM, uNative} R n
        ((originalNormalizedPlusQPositiveMulEquiv.{uR, uM, uNative} R n).symm b) = b)) ∧
    (originalNormalizedPlusToQLoops.{uR, uM, uNative} R).comp
      (StableGL.independentBGLCellInclusion R).hom =
        originalNormalizedBGLToQLoopsSource.{uR, uM, uNative} R :=
  ⟨(fun n a => originalNormalizedPlusQPositiveMulEquiv_apply R n a),
    (fun n b => originalNormalizedPlusQPositiveMulEquiv_symm_apply R n b),
    (fun n => originalNormalizedPlusQPositiveMulEquiv_inverse_laws R n),
    originalNormalizedPlusToQLoops_sourceTriangle R⟩

end AlgebraicKTheory.QuillenPlus

end
