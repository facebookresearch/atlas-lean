/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteBGLTelescopeGlobalRowHomotopy
public import
  MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteBGLTelescopeScalarProjection
public import
  MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteBGLTelescopeRowScalarSourceSquare

/-!
# The original Global/scalar/Global stable-row family

The same two original global families surround the original scalar-row
family. Whole-map factors and the literal original coefficient projection
square derive its endpoints. The original rank-zero root paths are retained
by endpoint-fixed homotopies that remove the stationary pasting pieces.
-/

noncomputable section

open CategoryTheory
open scoped ContinuousMap Simplicial

universe uR uS uX uY

namespace AlgebraicKTheory.StableGL

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

private abbrev scalarOriginalSourceCoefficientFunctor (f : R →+* S) :=
  SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
    FGProjectiveCat.scalarExtension.{uR, uS, uR} f)

private abbrev scalarOriginalTargetCoefficientFunctor.{uSourceCarrier, uTargetRing}
    (S : Type uTargetRing) [Ring S] :=
  SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
    (FGProjectiveCat.universeEquivalence.{uTargetRing, uSourceCarrier} S).inverse)

private abbrev scalarOriginalSourceCoefficientMap (f : R →+* S) :=
  CategoryTheory.realizedNerveFunctorMap (scalarOriginalSourceCoefficientFunctor f)

private abbrev scalarOriginalTargetCoefficientMap.{uSourceCarrier, uTargetRing}
    (S : Type uTargetRing) [Ring S] :=
  CategoryTheory.realizedNerveFunctorMap
    (scalarOriginalTargetCoefficientFunctor.{uSourceCarrier, uTargetRing} S)

private abbrev scalarOriginalStableSource (f : R →+* S) :=
  (scalarOriginalSourceCoefficientMap f).comp
    (ordinaryFiniteBGLTelescopeToBGL R ≫ finiteFreeRowStableZeroComparison R).hom

private abbrev scalarOriginalStableTarget (f : R →+* S) :=
  (scalarOriginalTargetCoefficientMap.{uR, uS} S).comp
    ((finiteFreeRowStableZeroComparison S).hom.comp
      ((ordinaryBGLScalarMap f).comp (ordinaryFiniteBGLTelescopeToBGL R).hom))

private theorem scalarOriginalTelescopeCoefficientValueComputed (f : R →+* S) :
    ordinaryFiniteBGLTelescopeScalarMap f =
      CategoryTheory.realizedNerveFunctorMap.{0, uR, 0, uS}
        (finiteBGLTelescopeScalarFunctor f) := by
  exact ordinaryFiniteBGLTelescopeScalarMap_eq_realizedFunctorMap f

private theorem scalarOriginalTargetFactorWithCoefficientComputed (f : R →+* S) :
    ordinaryFiniteBGLTelescopeRowScalarTargetMap f =
      (scalarOriginalTargetCoefficientMap.{uR, uS} S).comp
        ((finiteBGLTelescopeToRowZeroComponentTop S).hom.comp
          (ordinaryFiniteBGLTelescopeScalarMap f)) :=
  (ordinaryFiniteBGLTelescopeRowScalarTargetMap_factor f).trans
    (congrArg (fun q => (scalarOriginalTargetCoefficientMap.{uR, uS} S).comp
      ((finiteBGLTelescopeToRowZeroComponentTop S).hom.comp q))
      (scalarOriginalTelescopeCoefficientValueComputed f).symm)

private theorem scalarOriginalTargetProjectionValueComputed (f : R →+* S) :
    (scalarOriginalTargetCoefficientMap.{uR, uS} S).comp
        ((ordinaryFiniteBGLTelescopeToBGL S ≫ finiteFreeRowStableZeroComparison S).hom.comp
          (ordinaryFiniteBGLTelescopeScalarMap f)) =
      scalarOriginalStableTarget f := by
  apply ContinuousMap.ext
  intro x
  have h := congrArg
    (fun q : C(ordinaryFiniteBGLTelescope R, ordinaryBGL S) => q x)
    (ordinaryFiniteBGLTelescopeScalarMap_projection f)
  change scalarOriginalTargetCoefficientMap.{uR, uS} S
      ((finiteFreeRowStableZeroComparison S).hom
        (ordinaryFiniteBGLTelescopeToBGL S (ordinaryFiniteBGLTelescopeScalarMap f x))) =
    scalarOriginalTargetCoefficientMap.{uR, uS} S
      ((finiteFreeRowStableZeroComparison S).hom
        (ordinaryBGLScalarMap f (ordinaryFiniteBGLTelescopeToBGL R x)))
  exact congrArg (fun q : ordinaryBGL S =>
    scalarOriginalTargetCoefficientMap.{uR, uS} S
      ((finiteFreeRowStableZeroComparison S).hom q)) h.symm

private def scalarOriginalFirstRelative (f : R →+* S) :
    ContinuousMap.HomotopyRel (scalarOriginalStableSource f)
      (ordinaryFiniteBGLTelescopeRowScalarSourceMap f) {ordinaryFiniteBGLTelescopeBasepoint R} :=
  ((finiteBGLTelescopeGlobalOriginalStableRowPointRelative R).symm.compContinuousMap
    (scalarOriginalSourceCoefficientMap f)).cast rfl
      (ordinaryFiniteBGLTelescopeRowScalarSourceMap_factor f).symm

private def scalarOriginalLastRelative (f : R →+* S) :
    ContinuousMap.HomotopyRel (ordinaryFiniteBGLTelescopeRowScalarTargetMap f)
      (scalarOriginalStableTarget f) {ordinaryFiniteBGLTelescopeBasepoint R} := by
  let U := scalarOriginalTargetCoefficientMap.{uR, uS} S
  let T := ordinaryFiniteBGLTelescopeScalarMap f
  let H := (finiteBGLTelescopeGlobalOriginalStableRowPointRelative S).compContinuousMap U
  let K : ContinuousMap.HomotopyRel
      (U.comp ((finiteBGLTelescopeToRowZeroComponentTop S).hom.comp T))
      (U.comp ((ordinaryFiniteBGLTelescopeToBGL S ≫
        finiteFreeRowStableZeroComparison S).hom.comp T))
      {ordinaryFiniteBGLTelescopeBasepoint R} :=
    { toHomotopy := H.toHomotopy.compContinuousMap T
      prop' := by
        intro t x hx
        have hx0 : x = ordinaryFiniteBGLTelescopeBasepoint R := Set.mem_singleton_iff.mp hx
        subst x
        have hPoint : T (ordinaryFiniteBGLTelescopeBasepoint R) ∈
            ({ordinaryFiniteBGLTelescopeBasepoint S} : Set (ordinaryFiniteBGLTelescope S)) :=
          Set.mem_singleton_iff.mpr (ordinaryFiniteBGLTelescopeScalarMap_point f)
        change U (finiteBGLTelescopeGlobalOriginalStableRowPointRelative S
            (t, T (ordinaryFiniteBGLTelescopeBasepoint R))) =
          U ((finiteBGLTelescopeToRowZeroComponentTop S).hom
            (T (ordinaryFiniteBGLTelescopeBasepoint R)))
        exact congrArg U
          ((finiteBGLTelescopeGlobalOriginalStableRowPointRelative S).eq_fst t hPoint) }
  exact K.cast (scalarOriginalTargetFactorWithCoefficientComputed f).symm
    (scalarOriginalTargetProjectionValueComputed f)

private def scalarOriginalStableRowPaste (f : R →+* S) :
    ContinuousMap.Homotopy (scalarOriginalStableSource f) (scalarOriginalStableTarget f) :=
  (scalarOriginalFirstRelative f).toHomotopy.trans
    ((ordinaryFiniteBGLTelescopeRowScalarHomotopy f).trans
      (scalarOriginalLastRelative f).toHomotopy)

/-- The actual original Global_R reversed, scalar-row, Global_S family,
with both whole endpoint equations internally derived on the same telescope. -/
public def finiteBGLTelescopeScalarOriginalStableRowHomotopy (f : R →+* S) :
    ContinuousMap.Homotopy
      ((CategoryTheory.realizedNerveFunctorMap
        (SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
          FGProjectiveCat.scalarExtension.{uR, uS, uR} f))).comp
        (ordinaryFiniteBGLTelescopeToBGL R ≫ finiteFreeRowStableZeroComparison R).hom)
      ((CategoryTheory.realizedNerveFunctorMap
        (SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
          (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse))).comp
        ((finiteFreeRowStableZeroComparison S).hom.comp
          ((ordinaryBGLScalarMap f).comp (ordinaryFiniteBGLTelescopeToBGL R).hom))) :=
  scalarOriginalStableRowPaste f

/-- The entire same original pasted continuous family, with no new choice. -/
public def finiteBGLTelescopeScalarOriginalStableRowFamily (f : R →+* S) :
    C(unitInterval × ordinaryFiniteBGLTelescope R,
      SSet.toTop.obj (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uR} S)))) :=
  (finiteBGLTelescopeScalarOriginalStableRowHomotopy f).toContinuousMap

private theorem scalarOriginalPastedFamilyValueComputed (f : R →+* S) :
    (finiteBGLTelescopeScalarOriginalStableRowHomotopy f).toContinuousMap =
      finiteBGLTelescopeScalarOriginalStableRowFamily f := by
  rfl

/-- The homotopy keeps the same whole original three-piece family value. -/
public theorem finiteBGLTelescopeScalarOriginalStableRowHomotopy_toContinuousMap
    (f : R →+* S) :
    (finiteBGLTelescopeScalarOriginalStableRowHomotopy f).toContinuousMap =
      finiteBGLTelescopeScalarOriginalStableRowFamily f :=
  scalarOriginalPastedFamilyValueComputed f

/-- The source endpoint at rank zero is the SAME original scalar-row source value. -/
public theorem finiteBGLTelescopeScalarOriginalStableRow_source_point (f : R →+* S) :
    ((CategoryTheory.realizedNerveFunctorMap
      (SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
        FGProjectiveCat.scalarExtension.{uR, uS, uR} f))).comp
      (ordinaryFiniteBGLTelescopeToBGL R ≫ finiteFreeRowStableZeroComparison R).hom)
        (ordinaryFiniteBGLTelescopeBasepoint R) =
      ordinaryFiniteBGLTelescopeRowScalarSourceMap f (ordinaryFiniteBGLTelescopeBasepoint R) :=
  (scalarOriginalFirstRelative f).fst_eq_snd (by rfl)

/-- The target endpoint at rank zero is the SAME original scalar-row target value. -/
public theorem finiteBGLTelescopeScalarOriginalStableRow_target_point (f : R →+* S) :
    ((CategoryTheory.realizedNerveFunctorMap
      (SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
        (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse))).comp
      ((finiteFreeRowStableZeroComparison S).hom.comp
        ((ordinaryBGLScalarMap f).comp (ordinaryFiniteBGLTelescopeToBGL R).hom)))
          (ordinaryFiniteBGLTelescopeBasepoint R) =
      ordinaryFiniteBGLTelescopeRowScalarTargetMap f (ordinaryFiniteBGLTelescopeBasepoint R) :=
  ((scalarOriginalLastRelative f).fst_eq_snd (by rfl)).symm

private theorem scalarOriginalEvalAtTransComputed
    {X : Type uX} [TopologicalSpace X] {Y : Type uY} [TopologicalSpace Y]
    {a b c : C(X, Y)} (H : ContinuousMap.Homotopy a b) (K : ContinuousMap.Homotopy b c)
    (x : X) : (H.trans K).evalAt x = (H.evalAt x).trans (K.evalAt x) := by
  apply Path.ext
  funext t
  rfl

private theorem scalarOriginalStableRootClockComputed (f : R →+* S) :
    (((finiteBGLTelescopeScalarOriginalStableRowHomotopy f).evalAt
      (ordinaryFiniteBGLTelescopeBasepoint R)).cast
        (finiteBGLTelescopeScalarOriginalStableRow_source_point f).symm
        (finiteBGLTelescopeScalarOriginalStableRow_target_point f).symm).Homotopic
      ((ordinaryFiniteBGLTelescopeRowScalarHomotopy f).evalAt
        (ordinaryFiniteBGLTelescopeBasepoint R)) := by
  let x := ordinaryFiniteBGLTelescopeBasepoint R
  let P := (scalarOriginalFirstRelative f).toHomotopy.evalAt x
  let Q := (ordinaryFiniteBGLTelescopeRowScalarHomotopy f).evalAt x
  let W := (scalarOriginalLastRelative f).toHomotopy.evalAt x
  let hs := finiteBGLTelescopeScalarOriginalStableRow_source_point f
  let ht := finiteBGLTelescopeScalarOriginalStableRow_target_point f
  have hP : P.cast hs.symm rfl = Path.refl (ordinaryFiniteBGLTelescopeRowScalarSourceMap f x) := by
    apply Path.ext
    funext t
    change scalarOriginalFirstRelative f (t, x) = ordinaryFiniteBGLTelescopeRowScalarSourceMap f x
    exact (scalarOriginalFirstRelative f).eq_snd t (by rfl)
  have hW : W.cast rfl ht.symm = Path.refl (ordinaryFiniteBGLTelescopeRowScalarTargetMap f x) := by
    apply Path.ext
    funext t
    change scalarOriginalLastRelative f (t, x) = ordinaryFiniteBGLTelescopeRowScalarTargetMap f x
    exact (scalarOriginalLastRelative f).eq_fst t (by rfl)
  have hEval : (finiteBGLTelescopeScalarOriginalStableRowHomotopy f).evalAt x =
      P.trans (Q.trans W) :=
    (scalarOriginalEvalAtTransComputed (scalarOriginalFirstRelative f).toHomotopy
      ((ordinaryFiniteBGLTelescopeRowScalarHomotopy f).trans
        (scalarOriginalLastRelative f).toHomotopy) x).trans
      (congrArg (fun q => P.trans q)
        (scalarOriginalEvalAtTransComputed (ordinaryFiniteBGLTelescopeRowScalarHomotopy f)
          (scalarOriginalLastRelative f).toHomotopy x))
  have hClock : ((finiteBGLTelescopeScalarOriginalStableRowHomotopy f).evalAt x).cast
        hs.symm ht.symm =
      (Path.refl (ordinaryFiniteBGLTelescopeRowScalarSourceMap f x)).trans
        (Q.trans (Path.refl (ordinaryFiniteBGLTelescopeRowScalarTargetMap f x))) := by
    calc
      _ = (P.trans (Q.trans W)).cast hs.symm ht.symm :=
        congrArg
          (fun p : Path (scalarOriginalStableSource f x) (scalarOriginalStableTarget f x) =>
            p.cast hs.symm ht.symm) hEval
      _ = (P.cast hs.symm rfl).trans ((Q.cast rfl rfl).trans (W.cast rfl ht.symm)) :=
        (Path.cast_trans P (Q.trans W) hs.symm rfl ht.symm).trans
          (congrArg (fun q => (P.cast hs.symm rfl).trans q)
            (Path.cast_trans Q W rfl rfl ht.symm))
      _ = _ := by rw [hP, hW, Path.cast_rfl_rfl]
  change (((finiteBGLTelescopeScalarOriginalStableRowHomotopy f).evalAt x).cast
    hs.symm ht.symm).Homotopic Q
  rw [hClock]
  exact (Path.Homotopic.refl_trans
      (Q.trans (Path.refl (ordinaryFiniteBGLTelescopeRowScalarTargetMap f x)))).trans
    (Path.Homotopic.trans_refl Q)

private theorem scalarOriginalFirstWhiskeredValueComputed (f : R →+* S)
    (t : unitInterval) (x : ordinaryFiniteBGLTelescope R) :
    (scalarOriginalFirstRelative f).toHomotopy (t, x) =
      scalarOriginalSourceCoefficientMap f
        ((finiteBGLTelescopeGlobalOriginalStableRowPointRelative R).symm (t, x)) := by
  rfl

private theorem scalarOriginalLastWhiskeredValueComputed (f : R →+* S)
    (t : unitInterval) (x : ordinaryFiniteBGLTelescope R) :
    (scalarOriginalLastRelative f).toHomotopy (t, x) =
      scalarOriginalTargetCoefficientMap.{uR, uS} S
        (finiteBGLTelescopeGlobalOriginalStableRowPointRelative S
          (t, ordinaryFiniteBGLTelescopeScalarMap f x)) := by
  rfl

private theorem scalarOriginalWholeClockValueComputed (f : R →+* S)
    (t : unitInterval) (x : ordinaryFiniteBGLTelescope R) :
    finiteBGLTelescopeScalarOriginalStableRowFamily f (t, x) =
    if ht : (t : ℝ) ≤ 1 / 2 then
      scalarOriginalSourceCoefficientMap f
        ((finiteBGLTelescopeGlobalOriginalStableRowPointRelative R).symm
          (⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩, x))
    else
      let s : unitInterval := ⟨2 * (t : ℝ) - 1,
        unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩
      if hs : (s : ℝ) ≤ 1 / 2 then
        ordinaryFiniteBGLTelescopeRowScalarHomotopy f
          (⟨2 * (s : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩, x)
      else
        scalarOriginalTargetCoefficientMap.{uR, uS} S
          (finiteBGLTelescopeGlobalOriginalStableRowPointRelative S
            (⟨2 * (s : ℝ) - 1,
              unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, s.2.2⟩⟩,
              ordinaryFiniteBGLTelescopeScalarMap f x)) := by
  change ((scalarOriginalFirstRelative f).toHomotopy.trans
    ((ordinaryFiniteBGLTelescopeRowScalarHomotopy f).trans
      (scalarOriginalLastRelative f).toHomotopy)) (t, x) = _
  simpa only [ContinuousMap.Homotopy.trans_apply,
    scalarOriginalFirstWhiskeredValueComputed, scalarOriginalLastWhiskeredValueComputed]

/-- Every point and interval time retains the SAME original first-half,
middle-quarter and final-quarter clocks and actual three family values. -/
public theorem finiteBGLTelescopeScalarOriginalStableRowFamily_value (f : R →+* S)
    (t : unitInterval) (x : ordinaryFiniteBGLTelescope R) :
    finiteBGLTelescopeScalarOriginalStableRowFamily f (t, x) =
    if ht : (t : ℝ) ≤ 1 / 2 then
      (CategoryTheory.realizedNerveFunctorMap
        (SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
          FGProjectiveCat.scalarExtension.{uR, uS, uR} f)))
        ((finiteBGLTelescopeGlobalOriginalStableRowPointRelative R).symm
          (⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩, x))
    else
      let s : unitInterval := ⟨2 * (t : ℝ) - 1,
        unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩
      if hs : (s : ℝ) ≤ 1 / 2 then
        ordinaryFiniteBGLTelescopeRowScalarHomotopy f
          (⟨2 * (s : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩, x)
      else
        (CategoryTheory.realizedNerveFunctorMap
          (SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
            (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse)))
          (finiteBGLTelescopeGlobalOriginalStableRowPointRelative S
            (⟨2 * (s : ℝ) - 1,
              unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, s.2.2⟩⟩,
              ordinaryFiniteBGLTelescopeScalarMap f x)) :=
  scalarOriginalWholeClockValueComputed f t x

private theorem scalarOriginalStableRowRootTraceComputed (f : R →+* S) :
    (TopCat.pathEquiv (SSet.realizedEdgePath
      (nerve.edgeMk (finiteBGLTelescopeScalarSourceRootZeroIso f).hom))).Homotopic
      ((((finiteBGLTelescopeScalarOriginalStableRowHomotopy f).evalAt
          (ordinaryFiniteBGLTelescopeBasepoint R)).cast
        ((finiteBGLTelescopeScalarOriginalStableRow_source_point f).trans
          (ordinaryFiniteBGLTelescopeRowScalarSourceMap_original_vertex f)).symm
        ((finiteBGLTelescopeScalarOriginalStableRow_target_point f).trans
          (ordinaryFiniteBGLTelescopeRowScalarTargetMap_original_vertex f)).symm).trans
        (TopCat.pathEquiv (SSet.realizedEdgePath
          (nerve.edgeMk (finiteBGLTelescopeScalarTargetRootZeroIso f).hom)))) := by
  let x := ordinaryFiniteBGLTelescopeBasepoint R
  let hs := finiteBGLTelescopeScalarOriginalStableRow_source_point f
  let ht := finiteBGLTelescopeScalarOriginalStableRow_target_point f
  let vs := ordinaryFiniteBGLTelescopeRowScalarSourceMap_original_vertex f
  let vt := ordinaryFiniteBGLTelescopeRowScalarTargetMap_original_vertex f
  let q := TopCat.pathEquiv (SSet.realizedEdgePath
    (nerve.edgeMk (finiteBGLTelescopeScalarTargetRootZeroIso f).hom))
  have hPath := (scalarOriginalStableRootClockComputed f).pathCast vs.symm vt.symm
  have hCast :
      ((((finiteBGLTelescopeScalarOriginalStableRowHomotopy f).evalAt x).cast
          hs.symm ht.symm).cast vs.symm vt.symm) =
        (((finiteBGLTelescopeScalarOriginalStableRowHomotopy f).evalAt x).cast
          (hs.trans vs).symm (ht.trans vt).symm) := by
    apply Path.ext
    funext t
    rfl
  rw [hCast] at hPath
  have hConcat := hPath.hcomp (Path.Homotopic.refl q)
  exact (finiteBGLTelescopeRowScalarOriginalRootTrace f).trans hConcat.symm

/-- The SAME original rank-zero source and target roots satisfy the actual
pasted-family trace, with both endpoints fixed and all stationary clocks removed. -/
public theorem finiteBGLTelescopeScalarOriginalStableRow_original_root_trace (f : R →+* S) :
    (TopCat.pathEquiv (SSet.realizedEdgePath
      (nerve.edgeMk (finiteBGLTelescopeScalarSourceRootZeroIso f).hom))).Homotopic
      ((((finiteBGLTelescopeScalarOriginalStableRowHomotopy f).evalAt
          (ordinaryFiniteBGLTelescopeBasepoint R)).cast
        ((finiteBGLTelescopeScalarOriginalStableRow_source_point f).trans
          (ordinaryFiniteBGLTelescopeRowScalarSourceMap_original_vertex f)).symm
        ((finiteBGLTelescopeScalarOriginalStableRow_target_point f).trans
          (ordinaryFiniteBGLTelescopeRowScalarTargetMap_original_vertex f)).symm).trans
        (TopCat.pathEquiv (SSet.realizedEdgePath
          (nerve.edgeMk (finiteBGLTelescopeScalarTargetRootZeroIso f).hom)))) :=
  scalarOriginalStableRowRootTraceComputed f

end AlgebraicKTheory.StableGL

end
