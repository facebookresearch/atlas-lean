/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteBGLTelescopeScalarStableRowSourceComparison
public import
  MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteBGLTelescopeBasedProjection

/-!
# Descent through the same original based telescope projection

The original telescope family is precomposed by the literal accepted inverse.
The same original right inverse family surrounds it in both directions.
Its original rank-zero trace descends through the inverse point law and the
actual stationary relative families. No inverse naturality is assumed.
-/

noncomputable section

open CategoryTheory
open scoped ContinuousMap Simplicial

universe uR uS uX uY

namespace AlgebraicKTheory.StableGL

/-- Both complete original projection records, retaining every inverse,
point law, left/right family and forward/backward equivalence value. -/
public def ordinaryBGLScalarOriginalProjectionFamilies
    (R : Type uR) (S : Type uS) [Ring R] [Ring S] :
    FiniteBGLTelescopeBasedProjection R × FiniteBGLTelescopeBasedProjection S :=
  (finiteBGLTelescopeBasedProjection R, finiteBGLTelescopeBasedProjection S)

private theorem scalarBGLOriginalProjectionFamiliesValueComputed
    (R : Type uR) (S : Type uS) [Ring R] [Ring S] :
    ordinaryBGLScalarOriginalProjectionFamilies R S =
      (finiteBGLTelescopeBasedProjection R, finiteBGLTelescopeBasedProjection S) := by
  rfl

/-- The whole pair of original projection records has its literal stored value. -/
public theorem ordinaryBGLScalarOriginalProjectionFamilies_value
    (R : Type uR) (S : Type uS) [Ring R] [Ring S] :
    ordinaryBGLScalarOriginalProjectionFamilies R S =
      (finiteBGLTelescopeBasedProjection R, finiteBGLTelescopeBasedProjection S) :=
  scalarBGLOriginalProjectionFamiliesValueComputed R S

/-- BOTH full relative families and both point laws are those of the SAME
original accepted records, without a replacement inverse or contraction. -/
public theorem ordinaryBGLScalarOriginalProjectionFamilies_full_values
    (R : Type uR) (S : Type uS) [Ring R] [Ring S] :
    (ordinaryBGLScalarOriginalProjectionFamilies R S).1.left.toContinuousMap =
        (finiteBGLTelescopeBasedProjection R).left.toContinuousMap ∧
      (ordinaryBGLScalarOriginalProjectionFamilies R S).1.right.toContinuousMap =
        (finiteBGLTelescopeBasedProjection R).right.toContinuousMap ∧
      (ordinaryBGLScalarOriginalProjectionFamilies R S).2.left.toContinuousMap =
        (finiteBGLTelescopeBasedProjection S).left.toContinuousMap ∧
      (ordinaryBGLScalarOriginalProjectionFamilies R S).2.right.toContinuousMap =
        (finiteBGLTelescopeBasedProjection S).right.toContinuousMap ∧
      (ordinaryBGLScalarOriginalProjectionFamilies R S).1.inverse
          (ordinaryBGLBasepoint R) = ordinaryFiniteBGLTelescopeBasepoint R ∧
      (ordinaryBGLScalarOriginalProjectionFamilies R S).2.inverse
          (ordinaryBGLBasepoint S) = ordinaryFiniteBGLTelescopeBasepoint S :=
  ⟨rfl, rfl, rfl, rfl, (finiteBGLTelescopeBasedProjection R).inverse_point,
    (finiteBGLTelescopeBasedProjection S).inverse_point⟩

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

private abbrev scalarBGLOriginalSourceCoefficientMap (f : R →+* S) :=
  CategoryTheory.realizedNerveFunctorMap
    (SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
      FGProjectiveCat.scalarExtension.{uR, uS, uR} f))

private abbrev scalarBGLOriginalTargetCoefficientMap.{uSourceCarrier, uTargetRing}
    (S : Type uTargetRing) [Ring S] :=
  CategoryTheory.realizedNerveFunctorMap
    (SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
      (FGProjectiveCat.universeEquivalence.{uTargetRing, uSourceCarrier} S).inverse))

private abbrev scalarBGLOriginalSource (f : R →+* S) :=
  (scalarBGLOriginalSourceCoefficientMap f).comp (finiteFreeRowStableZeroComparison R).hom

private abbrev scalarBGLOriginalTarget (f : R →+* S) :=
  (scalarBGLOriginalTargetCoefficientMap.{uR, uS} S).comp
    ((finiteFreeRowStableZeroComparison S).hom.comp (ordinaryBGLScalarMap f))

private abbrev scalarBGLOriginalTelescopeSource (f : R →+* S) :=
  (scalarBGLOriginalSource f).comp (ordinaryFiniteBGLTelescopeToBGL R).hom

private abbrev scalarBGLOriginalTelescopeTarget (f : R →+* S) :=
  (scalarBGLOriginalTarget f).comp (ordinaryFiniteBGLTelescopeToBGL R).hom

private def scalarBGLOriginalPrefixRelative (f : R →+* S) :
    ContinuousMap.HomotopyRel (scalarBGLOriginalSource f)
      ((scalarBGLOriginalTelescopeSource f).comp
        (finiteBGLTelescopeBasedProjection R).inverse.hom) {ordinaryBGLBasepoint R} :=
  ((finiteBGLTelescopeBasedProjection R).right.symm.compContinuousMap
    (scalarBGLOriginalSource f)).cast
      (by apply ContinuousMap.ext; intro x; rfl)
      (by apply ContinuousMap.ext; intro x; rfl)

private def scalarBGLOriginalSuffixRelative (f : R →+* S) :
    ContinuousMap.HomotopyRel
      ((scalarBGLOriginalTelescopeTarget f).comp
        (finiteBGLTelescopeBasedProjection R).inverse.hom)
      (scalarBGLOriginalTarget f) {ordinaryBGLBasepoint R} :=
  ((finiteBGLTelescopeBasedProjection R).right.compContinuousMap
    (scalarBGLOriginalTarget f)).cast
      (by apply ContinuousMap.ext; intro x; rfl)
      (by apply ContinuousMap.ext; intro x; rfl)

private def scalarBGLOriginalMiddle (f : R →+* S) :
    ContinuousMap.Homotopy
      ((scalarBGLOriginalTelescopeSource f).comp
        (finiteBGLTelescopeBasedProjection R).inverse.hom)
      ((scalarBGLOriginalTelescopeTarget f).comp
        (finiteBGLTelescopeBasedProjection R).inverse.hom) :=
  (finiteBGLTelescopeScalarOriginalStableRowHomotopy f).compContinuousMap
    (finiteBGLTelescopeBasedProjection R).inverse.hom

private def scalarBGLOriginalPaste (f : R →+* S) :
    ContinuousMap.Homotopy (scalarBGLOriginalSource f) (scalarBGLOriginalTarget f) :=
  (scalarBGLOriginalPrefixRelative f).toHomotopy.trans
    ((scalarBGLOriginalMiddle f).trans (scalarBGLOriginalSuffixRelative f).toHomotopy)

/-- The original scalar stable-row family on BGL, descended through the
literal accepted inverse and both directions of its SAME original right family. -/
public def ordinaryBGLScalarOriginalStableRowHomotopy (f : R →+* S) :
    ContinuousMap.Homotopy
      ((CategoryTheory.realizedNerveFunctorMap
        (SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
          FGProjectiveCat.scalarExtension.{uR, uS, uR} f))).comp
        (finiteFreeRowStableZeroComparison R).hom)
      ((CategoryTheory.realizedNerveFunctorMap
        (SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
          (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse))).comp
        ((finiteFreeRowStableZeroComparison S).hom.comp (ordinaryBGLScalarMap f))) :=
  scalarBGLOriginalPaste f

/-- The whole SAME original BGL family, without an additional choice. -/
public def ordinaryBGLScalarOriginalStableRowFamily (f : R →+* S) :
    C(unitInterval × ordinaryBGL R,
      SSet.toTop.obj (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uR} S)))) :=
  (ordinaryBGLScalarOriginalStableRowHomotopy f).toContinuousMap

private theorem scalarBGLOriginalPastedFamilyValueComputed (f : R →+* S) :
    (ordinaryBGLScalarOriginalStableRowHomotopy f).toContinuousMap =
      ordinaryBGLScalarOriginalStableRowFamily f := by
  rfl

/-- The homotopy retains the same complete descended continuous family. -/
public theorem ordinaryBGLScalarOriginalStableRowHomotopy_toContinuousMap (f : R →+* S) :
    (ordinaryBGLScalarOriginalStableRowHomotopy f).toContinuousMap =
      ordinaryBGLScalarOriginalStableRowFamily f :=
  scalarBGLOriginalPastedFamilyValueComputed f

private theorem scalarBGLOriginalMiddleSourcePointComputed (f : R →+* S) :
    scalarBGLOriginalTelescopeSource f
        ((finiteBGLTelescopeBasedProjection R).inverse (ordinaryBGLBasepoint R)) =
      ordinaryFiniteBGLTelescopeRowScalarSourceMap f (ordinaryFiniteBGLTelescopeBasepoint R) :=
  (congrArg (scalarBGLOriginalTelescopeSource f)
    (finiteBGLTelescopeBasedProjection R).inverse_point).trans
    (finiteBGLTelescopeScalarOriginalStableRow_source_point f)

private theorem scalarBGLOriginalMiddleTargetPointComputed (f : R →+* S) :
    scalarBGLOriginalTelescopeTarget f
        ((finiteBGLTelescopeBasedProjection R).inverse (ordinaryBGLBasepoint R)) =
      ordinaryFiniteBGLTelescopeRowScalarTargetMap f (ordinaryFiniteBGLTelescopeBasepoint R) :=
  (congrArg (scalarBGLOriginalTelescopeTarget f)
    (finiteBGLTelescopeBasedProjection R).inverse_point).trans
    (finiteBGLTelescopeScalarOriginalStableRow_target_point f)

/-- The BGL source root value is the SAME original scalar-row source root value. -/
public theorem ordinaryBGLScalarOriginalStableRow_source_point (f : R →+* S) :
    ((CategoryTheory.realizedNerveFunctorMap
      (SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
        FGProjectiveCat.scalarExtension.{uR, uS, uR} f))).comp
      (finiteFreeRowStableZeroComparison R).hom) (ordinaryBGLBasepoint R) =
      ordinaryFiniteBGLTelescopeRowScalarSourceMap f (ordinaryFiniteBGLTelescopeBasepoint R) :=
  ((scalarBGLOriginalPrefixRelative f).fst_eq_snd (by rfl)).trans
    (scalarBGLOriginalMiddleSourcePointComputed f)

/-- The BGL target root value is the SAME original scalar-row target root value. -/
public theorem ordinaryBGLScalarOriginalStableRow_target_point (f : R →+* S) :
    ((CategoryTheory.realizedNerveFunctorMap
      (SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
        (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse))).comp
      ((finiteFreeRowStableZeroComparison S).hom.comp (ordinaryBGLScalarMap f)))
        (ordinaryBGLBasepoint R) =
      ordinaryFiniteBGLTelescopeRowScalarTargetMap f (ordinaryFiniteBGLTelescopeBasepoint R) :=
  ((scalarBGLOriginalSuffixRelative f).fst_eq_snd (by rfl)).symm.trans
    (scalarBGLOriginalMiddleTargetPointComputed f)

private theorem scalarBGLOriginalEvalAtTransComputed
    {X : Type uX} [TopologicalSpace X] {Y : Type uY} [TopologicalSpace Y]
    {a b c : C(X, Y)} (H : ContinuousMap.Homotopy a b) (K : ContinuousMap.Homotopy b c)
    (x : X) : (H.trans K).evalAt x = (H.evalAt x).trans (K.evalAt x) := by
  apply Path.ext
  funext t
  rfl

private theorem scalarBGLOriginalRelativeClockComputed (f : R →+* S) :
    (((ordinaryBGLScalarOriginalStableRowHomotopy f).evalAt (ordinaryBGLBasepoint R)).cast
      ((scalarBGLOriginalPrefixRelative f).fst_eq_snd (by rfl)).symm
      ((scalarBGLOriginalSuffixRelative f).fst_eq_snd (by rfl))).Homotopic
        ((scalarBGLOriginalMiddle f).evalAt (ordinaryBGLBasepoint R)) := by
  let x := ordinaryBGLBasepoint R
  let P := (scalarBGLOriginalPrefixRelative f).toHomotopy.evalAt x
  let Q := (scalarBGLOriginalMiddle f).evalAt x
  let W := (scalarBGLOriginalSuffixRelative f).toHomotopy.evalAt x
  let hs := (scalarBGLOriginalPrefixRelative f).fst_eq_snd (by rfl)
  let ht := ((scalarBGLOriginalSuffixRelative f).fst_eq_snd (by rfl)).symm
  have hP : P.cast hs.symm rfl =
      Path.refl (scalarBGLOriginalTelescopeSource f
        ((finiteBGLTelescopeBasedProjection R).inverse x)) := by
    apply Path.ext
    funext t
    change scalarBGLOriginalPrefixRelative f (t, x) = _
    exact (scalarBGLOriginalPrefixRelative f).eq_snd t (by rfl)
  have hW : W.cast rfl ht.symm =
      Path.refl (scalarBGLOriginalTelescopeTarget f
        ((finiteBGLTelescopeBasedProjection R).inverse x)) := by
    apply Path.ext
    funext t
    change scalarBGLOriginalSuffixRelative f (t, x) = _
    exact (scalarBGLOriginalSuffixRelative f).eq_fst t (by rfl)
  have hEval : (ordinaryBGLScalarOriginalStableRowHomotopy f).evalAt x = P.trans (Q.trans W) :=
    (scalarBGLOriginalEvalAtTransComputed (scalarBGLOriginalPrefixRelative f).toHomotopy
      ((scalarBGLOriginalMiddle f).trans (scalarBGLOriginalSuffixRelative f).toHomotopy) x).trans
      (congrArg (fun q => P.trans q)
        (scalarBGLOriginalEvalAtTransComputed (scalarBGLOriginalMiddle f)
          (scalarBGLOriginalSuffixRelative f).toHomotopy x))
  have hClock : ((ordinaryBGLScalarOriginalStableRowHomotopy f).evalAt x).cast hs.symm ht.symm =
      (Path.refl (scalarBGLOriginalTelescopeSource f
          ((finiteBGLTelescopeBasedProjection R).inverse x))).trans
        (Q.trans (Path.refl (scalarBGLOriginalTelescopeTarget f
          ((finiteBGLTelescopeBasedProjection R).inverse x)))) := by
    calc
      _ = (P.trans (Q.trans W)).cast hs.symm ht.symm :=
        congrArg
          (fun p : Path (scalarBGLOriginalSource f x) (scalarBGLOriginalTarget f x) =>
            p.cast hs.symm ht.symm) hEval
      _ = (P.cast hs.symm rfl).trans ((Q.cast rfl rfl).trans (W.cast rfl ht.symm)) :=
        (Path.cast_trans P (Q.trans W) hs.symm rfl ht.symm).trans
          (congrArg (fun q => (P.cast hs.symm rfl).trans q)
            (Path.cast_trans Q W rfl rfl ht.symm))
      _ = _ := by rw [hP, hW, Path.cast_rfl_rfl]
  change (((ordinaryBGLScalarOriginalStableRowHomotopy f).evalAt x).cast
    hs.symm ht.symm).Homotopic Q
  rw [hClock]
  exact (Path.Homotopic.refl_trans (Q.trans
      (Path.refl (scalarBGLOriginalTelescopeTarget f
        ((finiteBGLTelescopeBasedProjection R).inverse x))))).trans
    (Path.Homotopic.trans_refl Q)

private theorem scalarBGLOriginalRootClockComputed (f : R →+* S) :
    (((ordinaryBGLScalarOriginalStableRowHomotopy f).evalAt (ordinaryBGLBasepoint R)).cast
      (ordinaryBGLScalarOriginalStableRow_source_point f).symm
      (ordinaryBGLScalarOriginalStableRow_target_point f).symm).Homotopic
        (((finiteBGLTelescopeScalarOriginalStableRowHomotopy f).evalAt
          (ordinaryFiniteBGLTelescopeBasepoint R)).cast
            (finiteBGLTelescopeScalarOriginalStableRow_source_point f).symm
            (finiteBGLTelescopeScalarOriginalStableRow_target_point f).symm) := by
  let x := ordinaryBGLBasepoint R
  let hs := (scalarBGLOriginalPrefixRelative f).fst_eq_snd (by rfl)
  let ht := ((scalarBGLOriginalSuffixRelative f).fst_eq_snd (by rfl)).symm
  let ms := scalarBGLOriginalMiddleSourcePointComputed f
  let mt := scalarBGLOriginalMiddleTargetPointComputed f
  have hPath := (scalarBGLOriginalRelativeClockComputed f).pathCast ms.symm mt.symm
  have hCast :
      ((((ordinaryBGLScalarOriginalStableRowHomotopy f).evalAt x).cast
        hs.symm ht.symm).cast ms.symm mt.symm) =
      (((ordinaryBGLScalarOriginalStableRowHomotopy f).evalAt x).cast
        (ordinaryBGLScalarOriginalStableRow_source_point f).symm
        (ordinaryBGLScalarOriginalStableRow_target_point f).symm) := by
    apply Path.ext
    funext t
    rfl
  have hMiddle : ((scalarBGLOriginalMiddle f).evalAt x).cast ms.symm mt.symm =
      (((finiteBGLTelescopeScalarOriginalStableRowHomotopy f).evalAt
        (ordinaryFiniteBGLTelescopeBasepoint R)).cast
          (finiteBGLTelescopeScalarOriginalStableRow_source_point f).symm
          (finiteBGLTelescopeScalarOriginalStableRow_target_point f).symm) := by
    apply Path.ext
    funext t
    change finiteBGLTelescopeScalarOriginalStableRowHomotopy f
        (t, (finiteBGLTelescopeBasedProjection R).inverse x) =
      finiteBGLTelescopeScalarOriginalStableRowHomotopy f
        (t, ordinaryFiniteBGLTelescopeBasepoint R)
    exact congrArg (fun q => finiteBGLTelescopeScalarOriginalStableRowHomotopy f (t, q))
      (finiteBGLTelescopeBasedProjection R).inverse_point
  rw [hCast, hMiddle] at hPath
  exact hPath

private theorem scalarBGLOriginalPrefixWhiskeredValueComputed (f : R →+* S)
    (t : unitInterval) (x : ordinaryBGL R) :
    (scalarBGLOriginalPrefixRelative f).toHomotopy (t, x) =
      scalarBGLOriginalSource f
        ((finiteBGLTelescopeBasedProjection R).right.symm (t, x)) := by
  rfl

private theorem scalarBGLOriginalMiddleWhiskeredValueComputed (f : R →+* S)
    (t : unitInterval) (x : ordinaryBGL R) :
    scalarBGLOriginalMiddle f (t, x) =
      finiteBGLTelescopeScalarOriginalStableRowHomotopy f
        (t, (finiteBGLTelescopeBasedProjection R).inverse x) := by
  rfl

private theorem scalarBGLOriginalSuffixWhiskeredValueComputed (f : R →+* S)
    (t : unitInterval) (x : ordinaryBGL R) :
    (scalarBGLOriginalSuffixRelative f).toHomotopy (t, x) =
      scalarBGLOriginalTarget f
        ((finiteBGLTelescopeBasedProjection R).right (t, x)) := by
  rfl

private theorem scalarBGLOriginalWholeClockValueComputed (f : R →+* S)
    (t : unitInterval) (x : ordinaryBGL R) :
    ordinaryBGLScalarOriginalStableRowFamily f (t, x) =
      if ht : (t : ℝ) ≤ 1 / 2 then
        scalarBGLOriginalSource f ((finiteBGLTelescopeBasedProjection R).right.symm
          (⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩, x))
      else
        let s : unitInterval := ⟨2 * (t : ℝ) - 1,
          unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩
        if hs : (s : ℝ) ≤ 1 / 2 then
          finiteBGLTelescopeScalarOriginalStableRowHomotopy f
            (⟨2 * (s : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩,
              (finiteBGLTelescopeBasedProjection R).inverse x)
        else
          scalarBGLOriginalTarget f ((finiteBGLTelescopeBasedProjection R).right
            (⟨2 * (s : ℝ) - 1,
              unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, s.2.2⟩⟩, x)) := by
  change ((scalarBGLOriginalPrefixRelative f).toHomotopy.trans
    ((scalarBGLOriginalMiddle f).trans (scalarBGLOriginalSuffixRelative f).toHomotopy)) (t, x) = _
  simpa only [ContinuousMap.Homotopy.trans_apply,
    scalarBGLOriginalPrefixWhiskeredValueComputed, scalarBGLOriginalMiddleWhiskeredValueComputed,
    scalarBGLOriginalSuffixWhiskeredValueComputed]

/-- Every original point/time keeps the literal accepted inverse, the SAME
right families in both directions, and the original telescope family clocks. -/
public theorem ordinaryBGLScalarOriginalStableRowFamily_value (f : R →+* S)
    (t : unitInterval) (x : ordinaryBGL R) :
    ordinaryBGLScalarOriginalStableRowFamily f (t, x) =
      if ht : (t : ℝ) ≤ 1 / 2 then
        ((CategoryTheory.realizedNerveFunctorMap
          (SInverseS.zeroComponentFunctor
            ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
            FGProjectiveCat.scalarExtension.{uR, uS, uR} f))).comp
          (finiteFreeRowStableZeroComparison R).hom)
            ((finiteBGLTelescopeBasedProjection R).right.symm
              (⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩, x))
      else
        let s : unitInterval := ⟨2 * (t : ℝ) - 1,
          unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩
        if hs : (s : ℝ) ≤ 1 / 2 then
          finiteBGLTelescopeScalarOriginalStableRowHomotopy f
            (⟨2 * (s : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩,
              (finiteBGLTelescopeBasedProjection R).inverse x)
        else
          ((CategoryTheory.realizedNerveFunctorMap
            (SInverseS.zeroComponentFunctor
              ((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
              (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse))).comp
            ((finiteFreeRowStableZeroComparison S).hom.comp (ordinaryBGLScalarMap f)))
              ((finiteBGLTelescopeBasedProjection R).right
                (⟨2 * (s : ℝ) - 1,
                  unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, s.2.2⟩⟩, x)) :=
  scalarBGLOriginalWholeClockValueComputed f t x

private theorem scalarBGLOriginalRootTraceComputed (f : R →+* S) :
    (TopCat.pathEquiv (SSet.realizedEdgePath
      (nerve.edgeMk (finiteBGLTelescopeScalarSourceRootZeroIso f).hom))).Homotopic
      ((((ordinaryBGLScalarOriginalStableRowHomotopy f).evalAt (ordinaryBGLBasepoint R)).cast
        ((ordinaryBGLScalarOriginalStableRow_source_point f).trans
          (ordinaryFiniteBGLTelescopeRowScalarSourceMap_original_vertex f)).symm
        ((ordinaryBGLScalarOriginalStableRow_target_point f).trans
          (ordinaryFiniteBGLTelescopeRowScalarTargetMap_original_vertex f)).symm).trans
        (TopCat.pathEquiv (SSet.realizedEdgePath
          (nerve.edgeMk (finiteBGLTelescopeScalarTargetRootZeroIso f).hom)))) := by
  let x := ordinaryBGLBasepoint R
  let vs := ordinaryFiniteBGLTelescopeRowScalarSourceMap_original_vertex f
  let vt := ordinaryFiniteBGLTelescopeRowScalarTargetMap_original_vertex f
  let q := TopCat.pathEquiv (SSet.realizedEdgePath
    (nerve.edgeMk (finiteBGLTelescopeScalarTargetRootZeroIso f).hom))
  have hPath := (scalarBGLOriginalRootClockComputed f).pathCast vs.symm vt.symm
  have hLeftCast :
      ((((ordinaryBGLScalarOriginalStableRowHomotopy f).evalAt x).cast
        (ordinaryBGLScalarOriginalStableRow_source_point f).symm
        (ordinaryBGLScalarOriginalStableRow_target_point f).symm).cast vs.symm vt.symm) =
      (((ordinaryBGLScalarOriginalStableRowHomotopy f).evalAt x).cast
        ((ordinaryBGLScalarOriginalStableRow_source_point f).trans vs).symm
        ((ordinaryBGLScalarOriginalStableRow_target_point f).trans vt).symm) := by
    apply Path.ext
    funext t
    rfl
  have hRightCast :
      ((((finiteBGLTelescopeScalarOriginalStableRowHomotopy f).evalAt
          (ordinaryFiniteBGLTelescopeBasepoint R)).cast
        (finiteBGLTelescopeScalarOriginalStableRow_source_point f).symm
        (finiteBGLTelescopeScalarOriginalStableRow_target_point f).symm).cast vs.symm vt.symm) =
      (((finiteBGLTelescopeScalarOriginalStableRowHomotopy f).evalAt
          (ordinaryFiniteBGLTelescopeBasepoint R)).cast
        ((finiteBGLTelescopeScalarOriginalStableRow_source_point f).trans vs).symm
        ((finiteBGLTelescopeScalarOriginalStableRow_target_point f).trans vt).symm) := by
    apply Path.ext
    funext t
    rfl
  rw [hLeftCast, hRightCast] at hPath
  have hConcat := hPath.hcomp (Path.Homotopic.refl q)
  exact (finiteBGLTelescopeScalarOriginalStableRow_original_root_trace f).trans hConcat.symm

/-- The SAME original source/target rank-zero paths descend to BGL with
both endpoints fixed, using the original inverse point law and full families. -/
public theorem ordinaryBGLScalarOriginalStableRow_original_root_trace (f : R →+* S) :
    (TopCat.pathEquiv (SSet.realizedEdgePath
      (nerve.edgeMk (finiteBGLTelescopeScalarSourceRootZeroIso f).hom))).Homotopic
      ((((ordinaryBGLScalarOriginalStableRowHomotopy f).evalAt (ordinaryBGLBasepoint R)).cast
        ((ordinaryBGLScalarOriginalStableRow_source_point f).trans
          (ordinaryFiniteBGLTelescopeRowScalarSourceMap_original_vertex f)).symm
        ((ordinaryBGLScalarOriginalStableRow_target_point f).trans
          (ordinaryFiniteBGLTelescopeRowScalarTargetMap_original_vertex f)).symm).trans
        (TopCat.pathEquiv (SSet.realizedEdgePath
          (nerve.edgeMk (finiteBGLTelescopeScalarTargetRootZeroIso f).hom)))) :=
  scalarBGLOriginalRootTraceComputed f

end AlgebraicKTheory.StableGL

end
