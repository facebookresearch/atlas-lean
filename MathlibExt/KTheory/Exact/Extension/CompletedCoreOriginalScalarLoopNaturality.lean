/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.OriginalConullScalarReturnCalibration
public import MathlibExt.Topology.Homotopy.MixedHomotopyGroupTrace

/-!
# The whole original completed-Core scalar square into Q loops

The original completed-Core Q comparison, actual Core scalar functor,
original full mixed fiber map and calibrated conull return give the whole
scalar square. Both original full conull inverse families are retained.
The actual selected-point law makes the fiber inverse family relative to
the completed unit. No component restriction or replacement map is used.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CoreLocalizationComparison
open AlgebraicKTheory.QuillenMixedUniverseTransport
open AlgebraicKTheory.OriginalQuillenUnliftedTransport
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal
  CategoryTheory.MonoidalCategory ContinuousMap Simplicial Topology

attribute [local instance] AlgebraicKTheory.ExtensionCategory.leftSumAction
attribute [local instance] AlgebraicKTheory.FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

universe uC vC uD vD uE vE

namespace AlgebraicKTheory.OriginalQZeroComparison

private abbrev originalScalarCorePoint
    (E : Type uE) [Category.{vE} E] [Preadditive E]
    [HasZeroObject E] [HasBinaryBiproducts E] :=
  BasedSplitExactQLoop.completedCorePoint (C := E)

private abbrev originalScalarCoreQMap
    (E : Type uE) [Category.{vE} E] [Preadditive E]
    [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E] :
    C(BasedSplitExactQLoop.completedCoreSpace (C := E), NQKSpace E) :=
  (originalNQLoopPointHomeomorph E).symm.toHomotopyEquiv.toFun.comp
    (BasedSplitExactQLoop.comparisonMap (C := E)).hom

private abbrev originalScalarFiberQReturn
    (E : Type uE) [Category.{vE} E] [Preadditive E]
    [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E] :=
  (originalNQLoopPointHomeomorph E).symm.toHomotopyEquiv.toFun.comp
    (zeroOriginalHomotopyFiberToLoops (C := E)).hom

private theorem originalScalarCoreFiberPoint
    (E : Type uE) [Category.{vE} E] [Preadditive E]
    [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E] :
    completedCoreToOriginalHomotopyFiber (C := E) (originalScalarCorePoint E) =
      BasedSplitExactQLoop.selectedZeroFiberPoint (C := E) := by
  let c : TopCat.of PUnit.{(max uE vE) + 1} ⟶
      BasedSplitExactQLoop.completedCoreSpace (C := E) :=
    TopCat.const (originalScalarCorePoint E)
  exact (TopCat.comp_app c (completedCoreToOriginalHomotopyFiber (C := E))
    (PUnit.unit : PUnit.{(max uE vE) + 1})).symm.trans
      (ConcreteCategory.congr_hom
        (completedCoreToOriginalHomotopyFiber_unit_selectedPoint (C := E))
        (PUnit.unit : PUnit.{(max uE vE) + 1}))

private theorem originalScalarCoreQPoint
    (E : Type uE) [Category.{vE} E] [Preadditive E]
    [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E] :
    originalScalarCoreQMap E (originalScalarCorePoint E) = Path.refl (NQReal.basepoint E) := by
  have hRaw := BasedSplitExactQLoop.comparisonMap_point (C := E)
  have hPoint :
      (originalNQLoopPointHomeomorph E).symm (Path.refl (zeroQVertex (C := E))) =
        Path.refl (NQReal.basepoint E) := by
    apply Path.ext
    funext t
    exact (originalNQLoopPointHomeomorph_symm_value E (Path.refl (zeroQVertex (C := E))) t).trans
      (NQReal.basepoint_eq_realizedVertex E).symm
  exact (congrArg (originalNQLoopPointHomeomorph E).symm hRaw).trans hPoint

/-- BOTH original complete conull inverse families retain the exact original
return and selected-loop maps, points, independent worlds and every component. -/
public def completedCoreOriginalConullInverseFamilies
    (E : Type uE) [Category.{vE} E] [Preadditive E]
    [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E] :
    ContinuousMap.HomotopyRel
      ((zeroLoopToOriginalHomotopyFiber (C := E)).hom.comp
        (zeroOriginalHomotopyFiberToLoops (C := E)).hom)
      (ContinuousMap.id (BasedSplitExactQLoop.originalZeroFiber (C := E)))
      {BasedSplitExactQLoop.selectedZeroFiberPoint (C := E)} ×
    ContinuousMap.HomotopyRel
      ((zeroOriginalHomotopyFiberToLoops (C := E)).hom.comp
        (zeroLoopToOriginalHomotopyFiber (C := E)).hom)
      (ContinuousMap.id (BasedSplitExactQLoop.originalQLoops (C := E)))
      {BasedSplitExactQLoop.constantQLoop (C := E)} := by
  refine ⟨(zeroOriginalHomotopyFiberLoopEquiv_leftHomotopyRel (C := E)).cast ?_ rfl,
    (zeroOriginalHomotopyFiberLoopEquiv_rightHomotopyRel (C := E)).cast ?_ rfl⟩
  · rw [zeroOriginalHomotopyFiberLoopEquiv_invFun, zeroOriginalHomotopyFiberLoopEquiv_toFun]
  · rw [zeroOriginalHomotopyFiberLoopEquiv_invFun, zeroOriginalHomotopyFiberLoopEquiv_toFun]

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

private abbrev originalScalarFiberAfterMixed :=
  (originalScalarFiberQReturn D).comp (mixedOriginalZeroFiberMap F)

private abbrev originalScalarCoreLoopIntermediate :=
  (originalScalarFiberAfterMixed F).comp
    (((zeroLoopToOriginalHomotopyFiber (C := C)).hom.comp
      (zeroOriginalHomotopyFiberToLoops (C := C)).hom).comp
        (completedCoreToOriginalHomotopyFiber (C := C)).hom)

private def originalScalarCoreLoopLeading :
    ContinuousMap.Homotopy ((mixedNQKSpaceMap F).comp (originalScalarCoreQMap C))
      (originalScalarCoreLoopIntermediate F) := by
  let H := (originalConullScalarCalibratedReturnHomotopy F).symm.compContinuousMap
    (originalScalarCoreQMap C)
  refine H.cast rfl ?_
  apply ContinuousMap.ext
  intro x
  change (originalNQLoopPointHomeomorph D).symm
    (zeroOriginalHomotopyFiberToLoops (C := D)
      (mixedOriginalZeroFiberMap F
        (zeroLoopToOriginalHomotopyFiber (C := C)
          (originalNQLoopPointHomeomorph C
            ((originalNQLoopPointHomeomorph C).symm
              (zeroOriginalHomotopyFiberToLoops (C := C)
                (completedCoreToOriginalHomotopyFiber (C := C) x))))))) = _
  rw [Homeomorph.apply_symm_apply]
  rfl

private def originalScalarCoreLoopMiddle :
    ContinuousMap.HomotopyRel
      (originalScalarCoreLoopIntermediate F)
      ((originalScalarFiberAfterMixed F).comp (completedCoreToOriginalHomotopyFiber (C := C)).hom)
      {originalScalarCorePoint C} := by
  let L := (((completedCoreOriginalConullInverseFamilies C).1).precomposePointRelative
    (completedCoreToOriginalHomotopyFiber (C := C)).hom (originalScalarCorePoint C)
      (originalScalarCoreFiberPoint C)).compContinuousMap (originalScalarFiberAfterMixed F)
  refine L.cast rfl ?_
  apply ContinuousMap.ext
  intro x
  rfl

private def originalScalarCoreLoopTail :
    ContinuousMap.Homotopy
      ((originalScalarFiberAfterMixed F).comp (completedCoreToOriginalHomotopyFiber (C := C)).hom)
      ((originalScalarCoreQMap D).comp
        (realizedNerveFunctorMap
          (CategoryTheory.CoreLocalizationComparison.completedCoreFunctor F))) := by
  let H := (ContinuousMap.Homotopy.refl (originalScalarFiberQReturn D)).comp
    (completedCoreOriginalFiberNaturalityHomotopy F)
  refine H.cast ?_ ?_
  · apply ContinuousMap.ext
    intro x
    rfl
  · apply ContinuousMap.ext
    intro x
    rfl

/-- The WHOLE original completed-Core Q maps satisfy the actual mixed scalar
square on all components and independent category worlds. The first family is
the calibrated conull return; the middle is the exact original fiber inverse;
the final family is the SAME189 whole completed-Core fiber homotopy. -/
public def completedCoreOriginalScalarQLoopHomotopy :
    ContinuousMap.Homotopy
      ((mixedNQKSpaceMap F).comp
        ((originalNQLoopPointHomeomorph C).symm.toHomotopyEquiv.toFun.comp
          (BasedSplitExactQLoop.comparisonMap (C := C)).hom))
      (((originalNQLoopPointHomeomorph D).symm.toHomotopyEquiv.toFun.comp
        (BasedSplitExactQLoop.comparisonMap (C := D)).hom).comp
          (realizedNerveFunctorMap
            (CategoryTheory.CoreLocalizationComparison.completedCoreFunctor F))) :=
  (originalScalarCoreLoopLeading F).trans
    ((originalScalarCoreLoopMiddle F).toHomotopy.trans (originalScalarCoreLoopTail F))

end AlgebraicKTheory.OriginalQZeroComparison

end


/-!
# The actual completed-unit root and every positive scalar group map

The actual original conull inverse is relative to the original selected
fiber point. At the completed unit, its constant trace sits between the
reverse calibrated return trace and the original full fiber trace. The
latter followed by the actual Core unit root is literal betaFiber. The
proved original081 return-unit calibration and genuine cancellation earn
the scalar square's designated root law before all-index transport.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CoreLocalizationComparison
open AlgebraicKTheory.QuillenMixedUniverseTransport
open AlgebraicKTheory.OriginalQuillenUnliftedTransport
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal
  CategoryTheory.MonoidalCategory ContinuousMap Simplicial Topology

attribute [local instance] AlgebraicKTheory.ExtensionCategory.leftSumAction
attribute [local instance] AlgebraicKTheory.FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

universe uE uC vC uD vD

namespace AlgebraicKTheory.OriginalQZeroComparison

private theorem originalFixedPathBefore
    {X : Type uE} [TopologicalSpace X] {a b c : X}
    (p : Path a b) (q : Path b c) (h : a = b) (hp : ∀ s, p s = b) :
    (p.trans q).Homotopic (q.cast h rfl) := by
  cases h
  have hPath : p = Path.refl a := by
    apply Path.ext
    funext s
    exact hp s
  rw [hPath]
  exact Path.Homotopic.refl_trans q

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

private abbrev originalScalarFullReturnMap : C(NQKSpace C, NQKSpace D) :=
  (originalNQLoopPointHomeomorph D).symm.toHomotopyEquiv.toFun.comp
    ((((zeroOriginalHomotopyFiberToLoops (C := D)).hom.comp (mixedOriginalZeroFiberMap F)).comp
      (zeroLoopToOriginalHomotopyFiber (C := C)).hom).comp
        (originalNQLoopPointHomeomorph C).toHomotopyEquiv.toFun)

private theorem originalScalarCoreLoopLeading_value (s : unitInterval)
    (x : BasedSplitExactQLoop.completedCoreSpace (C := C)) :
    originalScalarCoreLoopLeading F (s, x) =
      originalConullScalarCalibratedReturnHomotopy F
        (unitInterval.symm s, originalScalarCoreQMap C x) := rfl

private theorem originalScalarCoreLoopTail_value (s : unitInterval)
    (x : BasedSplitExactQLoop.completedCoreSpace (C := C)) :
    originalScalarCoreLoopTail F (s, x) =
      originalScalarFiberQReturn D (completedCoreOriginalFiberNaturalityHomotopy F (s, x)) := rfl

/-- The source root is EXACT081 for the SAME canonical139 loop map, cast only
by the proved actual original Core/Q unit equation. It is not strict reflexivity
at the canonical loop-map image of the constant loop. -/
public def completedCoreOriginalScalarQLoopSourceRoot :
    Path
      (mixedNQKSpaceMap F
        ((originalNQLoopPointHomeomorph C).symm
          (BasedSplitExactQLoop.comparisonMap (C := C)
            (BasedSplitExactQLoop.completedCorePoint (C := C)))))
      (Path.refl (NQReal.basepoint D)) :=
  (originalConullScalarCanonicalLoopUnit F).cast
    (congrArg (mixedNQKSpaceMap F) (originalScalarCoreQPoint C)) rfl

/-- The target root is SAME188 actual completed-Core unit root mapped by the
original Core/Q comparison, with its original target point equation. -/
public def completedCoreOriginalScalarQLoopTargetRoot :
    Path
      ((originalNQLoopPointHomeomorph D).symm
        (BasedSplitExactQLoop.comparisonMap (C := D)
          (realizedNerveFunctorMap
            (CategoryTheory.CoreLocalizationComparison.completedCoreFunctor F)
            (BasedSplitExactQLoop.completedCorePoint (C := C)))))
      (Path.refl (NQReal.basepoint D)) :=
  ((completedCoreOriginalUnitRootPath F).map (originalScalarCoreQMap D).continuous).cast
    rfl (originalScalarCoreQPoint D).symm

omit [ExactCategory C] [F.IsExact] in
private theorem originalScalarCoreQLoopTargetRootValueComputed (s : unitInterval) :
    (completedCoreOriginalScalarQLoopTargetRoot F).toContinuousMap.toFun s =
      (originalNQLoopPointHomeomorph D).symm
        (BasedSplitExactQLoop.comparisonMap (C := D)
          ((completedCoreOriginalUnitRootPath F).toContinuousMap.toFun s)) := rfl

omit [ExactCategory C] [F.IsExact] in
/-- Every target-root time uses the original Core/Q comparison of the completed-unit root. -/
public theorem completedCoreOriginalScalarQLoopTargetRoot_value (s : unitInterval) :
    (completedCoreOriginalScalarQLoopTargetRoot F).toContinuousMap.toFun s =
      (originalNQLoopPointHomeomorph D).symm
        (BasedSplitExactQLoop.comparisonMap (C := D)
          ((completedCoreOriginalUnitRootPath F).toContinuousMap.toFun s)) :=
  originalScalarCoreQLoopTargetRootValueComputed F s

/-- Root compatibility for the original completed-Core scalar square,
retaining its actual full homotopy and both chosen unit paths. -/
public abbrev completedCoreOriginalScalarQLoopRootCompatibility : Prop :=
    (((completedCoreOriginalScalarQLoopHomotopy F).evalAt
        (BasedSplitExactQLoop.completedCorePoint (C := C))).trans
      (completedCoreOriginalScalarQLoopTargetRoot F)).Homotopic
        (completedCoreOriginalScalarQLoopSourceRoot F)

/-- The WHOLE original Core/scalar/Q square has its ACTUAL designated root
compatibility, earned from the exact197 original081 unit law, literal189/188
betaFiber and the point-relative original conull inverse; no root outcome is given. -/
public theorem completedCoreOriginalScalarQLoopHomotopy_ROOT :
    completedCoreOriginalScalarQLoopRootCompatibility F := by
  change (((completedCoreOriginalScalarQLoopHomotopy F).evalAt
        (BasedSplitExactQLoop.completedCorePoint (C := C))).trans
      (completedCoreOriginalScalarQLoopTargetRoot F)).Homotopic
        (completedCoreOriginalScalarQLoopSourceRoot F)
  let x : BasedSplitExactQLoop.completedCoreSpace (C := C) := originalScalarCorePoint C
  let c : NQKSpace C := Path.refl (NQReal.basepoint C)
  let e : NQKSpace D := Path.refl (NQReal.basepoint D)
  let A : C(NQKSpace C, NQKSpace D) := originalScalarFullReturnMap F
  let gc : C(BasedSplitExactQLoop.completedCoreSpace (C := C), NQKSpace C) :=
    originalScalarCoreQMap C
  let T : Path (A c) (mixedNQKSpaceMap F c) :=
    (originalConullScalarCalibratedReturnHomotopy F).evalAt c
  let U : Path (mixedNQKSpaceMap F c) e := originalConullScalarCanonicalLoopUnit F
  let alpha : Path (A c) e := originalConullScalarBetaReturnTrace F
  let r : Path (mixedNQKSpaceMap F (gc x)) (originalScalarCoreLoopIntermediate F x) :=
    (originalScalarCoreLoopLeading F).evalAt x
  let l : Path (originalScalarCoreLoopIntermediate F x)
      (originalScalarFiberAfterMixed F (completedCoreToOriginalHomotopyFiber (C := C) x)) :=
    (originalScalarCoreLoopMiddle F).toHomotopy.evalAt x
  let h : Path
      (originalScalarFiberAfterMixed F (completedCoreToOriginalHomotopyFiber (C := C) x))
      (originalScalarCoreQMap D (realizedNerveFunctorMap (completedCoreFunctor F) x)) :=
    (originalScalarCoreLoopTail F).evalAt x
  let q : Path
      (originalScalarCoreQMap D (realizedNerveFunctorMap (completedCoreFunctor F) x)) e :=
    completedCoreOriginalScalarQLoopTargetRoot F
  have hGc : gc x = c := originalScalarCoreQPoint C
  have hB := congrArg (mixedNQKSpaceMap F) hGc
  have hx : x ∈ ({originalScalarCorePoint C} :
      Set (BasedSplitExactQLoop.completedCoreSpace (C := C))) := by
    change x = originalScalarCorePoint C
    rfl
  have hb : originalScalarCoreLoopIntermediate F x =
      originalScalarFiberAfterMixed F (completedCoreToOriginalHomotopyFiber (C := C) x) :=
    (originalScalarCoreLoopMiddle F).fst_eq_snd hx
  have hlValue (s : unitInterval) :
      l.toContinuousMap.toFun s =
        originalScalarFiberAfterMixed F (completedCoreToOriginalHomotopyFiber (C := C) x) :=
    (originalScalarCoreLoopMiddle F).eq_snd s hx
  have hLink : originalScalarCoreLoopIntermediate F x = A c := by
    have hEnd := (originalScalarCoreLoopLeading F).map_one_left x
    have hValue := originalScalarCoreLoopLeading_value F 1 x
    rw [unitInterval.symm_one] at hValue
    exact hEnd.symm.trans (hValue.trans
      (((originalConullScalarCalibratedReturnHomotopy F).map_zero_left (gc x)).trans
        (congrArg A hGc)))
  have hr : r = T.symm.cast hB hLink := by
    apply Path.ext (X := NQKSpace D)
    funext s
    change (originalScalarCoreLoopLeading F).toContinuousMap.toFun (s, x) =
      (originalConullScalarCalibratedReturnHomotopy F).toContinuousMap.toFun
        (unitInterval.symm s, c)
    exact (originalScalarCoreLoopLeading_value F s x).trans
      (congrArg (fun gamma => originalConullScalarCalibratedReturnHomotopy F
        (unitInterval.symm s, gamma)) hGc)
  have hAlpha : (h.trans q).cast hb rfl = alpha.cast hLink rfl := by
    apply Path.ext (X := NQKSpace D)
    funext s
    change (h.trans q).toContinuousMap.toFun s =
      (originalConullScalarBetaReturnTrace F).toContinuousMap.toFun s
    have hLeft := Path.trans_apply (X := NQKSpace D) h q s
    refine hLeft.trans ?_
    rw [originalConullScalarBetaReturnTrace_value, originalConullScalarBetaFiber_value]
    by_cases hs : (s : ℝ) ≤ 1 / 2
    · simp only [dite_eq_left hs]
      exact originalScalarCoreLoopTail_value F _ x
    · simp only [dite_eq_right hs]
      exact completedCoreOriginalScalarQLoopTargetRoot_value F _
  have hCal : (T.trans U).Homotopic alpha :=
    originalConullScalarCalibratedReturnHomotopy_OWNunit F
  have hBack : (T.symm.trans alpha).Homotopic U :=
    (((Path.Homotopic.refl T.symm).hcomp hCal.symm).trans
      ((Path.Homotopic.trans_assoc T.symm T U).symm.trans
        (((Path.Homotopic.symm_trans T).hcomp (Path.Homotopic.refl U)).trans
          (Path.Homotopic.refl_trans U))))
  have hPrefix : r.trans (alpha.cast hLink rfl) = (T.symm.trans alpha).cast hB rfl := by
    rw [hr]
    exact (Path.cast_trans (X := NQKSpace D) T.symm alpha hB hLink rfl).symm
  have hEnd : (r.trans (alpha.cast hLink rfl)).Homotopic
      (completedCoreOriginalScalarQLoopSourceRoot F) := by
    rw [hPrefix]
    exact hBack.pathCast hB rfl
  have hTrace : (completedCoreOriginalScalarQLoopHomotopy F).evalAt x =
      r.trans (l.trans h) := by
    apply Path.ext (X := NQKSpace D)
    funext s
    let K := (originalScalarCoreLoopMiddle F).toHomotopy.trans (originalScalarCoreLoopTail F)
    change ((originalScalarCoreLoopLeading F).trans K).toContinuousMap.toFun (s, x) =
      (r.trans (l.trans h)).toContinuousMap.toFun s
    have hLeft := ContinuousMap.Homotopy.trans_apply
      (X := BasedSplitExactQLoop.completedCoreSpace (C := C)) (Y := NQKSpace D)
      (originalScalarCoreLoopLeading F) K (s, x)
    have hRight := Path.trans_apply (X := NQKSpace D) r (l.trans h) s
    refine hLeft.trans (Eq.trans ?_ hRight.symm)
    by_cases hs : (s : ℝ) ≤ 1 / 2
    · simp only [dite_eq_left hs]
      rfl
    · simp only [dite_eq_right hs]
      let t : unitInterval := ⟨2 * s - 1, unitInterval.two_mul_sub_one_mem_iff.2
        ⟨(not_le.1 hs).le, s.2.2⟩⟩
      change K.toContinuousMap.toFun (t, x) = (l.trans h).toContinuousMap.toFun t
      have hMiddle := ContinuousMap.Homotopy.trans_apply
        (X := BasedSplitExactQLoop.completedCoreSpace (C := C)) (Y := NQKSpace D)
        (originalScalarCoreLoopMiddle F).toHomotopy (originalScalarCoreLoopTail F) (t, x)
      have hPaths := Path.trans_apply (X := NQKSpace D) l h t
      refine hMiddle.trans (Eq.trans ?_ hPaths.symm)
      by_cases ht : (t : ℝ) ≤ 1 / 2
      · simp only [dite_eq_left ht]
        rfl
      · simp only [dite_eq_right ht]
        rfl
  have hRemove : (l.trans (h.trans q)).Homotopic ((h.trans q).cast hb rfl) :=
    originalFixedPathBefore l (h.trans q) hb hlValue
  have hLast : (r.trans ((h.trans q).cast hb rfl)).Homotopic
      (completedCoreOriginalScalarQLoopSourceRoot F) := by
    rw [hAlpha]
    exact hEnd
  rw [hTrace]
  exact (Path.Homotopic.trans_assoc r (l.trans h) q).trans
    (((Path.Homotopic.refl r).hcomp (Path.Homotopic.trans_assoc l h q)).trans
      (((Path.Homotopic.refl r).hcomp hRemove).trans hLast))

/-- Equality of the original rooted group maps in degree `n + 1`,
using the whole completed-Core square and its two actual designated roots. -/
public abbrev completedCoreOriginalScalarQLoopGroupNaturality (n : ℕ) : Prop :=
  letI : Group (HomotopyGroup.Pi (n + 1) (NQKSpace D)
      (Path.refl (NQReal.basepoint D) : NQKSpace D)) :=
    HomotopyGroup.group (X := NQKSpace D)
      (x := (Path.refl (NQReal.basepoint D) : NQKSpace D)) (Fin (n + 1));
    (TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of (NQKSpace D))
      (completedCoreOriginalScalarQLoopSourceRoot F)).toMonoidHom.comp
        (HomotopyGroup.mapHom
          ((mixedNQKSpaceMap F).comp
            ((originalNQLoopPointHomeomorph C).symm.toHomotopyEquiv.toFun.comp
              (BasedSplitExactQLoop.comparisonMap (C := C)).hom))) =
    (TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of (NQKSpace D))
      (completedCoreOriginalScalarQLoopTargetRoot F)).toMonoidHom.comp
        (HomotopyGroup.mapHom
          (((originalNQLoopPointHomeomorph D).symm.toHomotopyEquiv.toFun.comp
            (BasedSplitExactQLoop.comparisonMap (C := D)).hom).comp
              (realizedNerveFunctorMap
                (CategoryTheory.CoreLocalizationComparison.completedCoreFunctor F))))

/-- EVERY positive original cube index uses the actual scalar/Q maps and
BOTH designated roots of the WHOLE original Core square. Its actual root law
is derived above; the existing mixed trace transport keeps the full basepoint action. -/
public theorem completedCoreOriginalScalarQLoop_allIndices (n : ℕ) :
    completedCoreOriginalScalarQLoopGroupNaturality F n :=
  TopCat.homotopyGroup_rooted_map_homotopy_mixed n
    (completedCoreOriginalScalarQLoopHomotopy F)
    (completedCoreOriginalScalarQLoopSourceRoot F)
    (completedCoreOriginalScalarQLoopTargetRoot F)
    (completedCoreOriginalScalarQLoopHomotopy_ROOT F)

end AlgebraicKTheory.OriginalQZeroComparison

end
