/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.BasedSplitExactQLoopComparison
public import MathlibExt.KTheory.Ring.StableGeneralLinear.NativeProjectiveScalarPositiveNaturality
public import MathlibExt.CategoryTheory.Monoidal.CoreRealizedTranslations

/-!
# A genuine original Q source comparator for the exact normalization

The original native zero inclusion, original Core inverse functor and original
completed-Core Q forward comparison define the actual map into original Q
loops. The exact226 normalization supplies its plus and BGL source maps.
Their source triangle is derived from the SAME strict inverse source triangle.
The original Q comparison's full inverse families are retained. No selected
CoreRingData.a is changed or asserted natural.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open CategoryTheory.CoreLocalizationComparison
open CategoryTheory.SInverseS.ComponentTranslation
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ContinuousMap

attribute [local instance] MonoidalActionCategory.diagonalAction

namespace AlgebraicKTheory.QuillenPlus

private def originalProjectiveSplitRows.{uR, uM} (R : Type uR) [Ring R] :
    ∀ S : ShortComplex (FGProjectiveCat.{max uR uM} R),
      IsAdmissibleExact S → Nonempty S.Splitting := by
  intro S hS
  change Nonempty S.Splitting at hS
  exact hS

/-- Projective admissible rows have their original split-exact splitting antecedent. -/
public theorem originalCanonicalProjectiveSplitRows.{uR, uM} (R : Type uR) [Ring R] :
    ∀ S : ShortComplex (FGProjectiveCat.{max uR uM} R),
      IsAdmissibleExact S → Nonempty S.Splitting :=
  originalProjectiveSplitRows R

private theorem originalCoreInverseZeroObject.{uR, uM} (R : Type uR) [Ring R] :
    (coreAdditivePairEquivalence (C := FGProjectiveCat.{max uR uM} R)).inverse.obj
        (⟨0, 0⟩ : SInverseS.Pair (FGProjectiveCat.{max uR uM} R)) =
      ((SInverse.inclusion (Core (FGProjectiveCat.{max uR uM} R))
        (Core (FGProjectiveCat.{max uR uM} R))).obj
          (𝟙_ (Core (FGProjectiveCat.{max uR uM} R)))) := by
  rw [coreAdditivePairEquivalence_inverse_obj]
  rfl

private theorem originalCoreInverseRealizationZeroPoint.{uR, uM}
    (R : Type uR) [Ring R] :
    (SSet.toTop.map (nerveMap
      (coreAdditivePairEquivalence (C := FGProjectiveCat.{max uR uM} R)).inverse))
      (originalSpacePoint (C := FGProjectiveCat.{max uR uM} R)) =
        BasedSplitExactQLoop.completedCorePoint (C := FGProjectiveCat.{max uR uM} R) := by
  let C := FGProjectiveCat.{max uR uM} R
  let E := coreAdditivePairEquivalence (C := C)
  let x : SInverseS.Pair C := ⟨(0 : C), (0 : C)⟩
  let M := SSet.toTop.map (nerveMap E.inverse)
  let y := (SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C))
  have hPoint : originalSpacePoint (C := C) =
      SSet.realizedVertex (X := nerve (SInverseS.Pair C)) (ComposableArrows.mk₀ x) :=
    originalSpacePoint_eq_realizedVertex (C := C)
  have hVertex := (SSet.realizedVertex_naturality (nerveMap E.inverse)
    (ComposableArrows.mk₀ x)).symm
  have hChain : SSet.realizedVertex ((nerveMap E.inverse).app _ (ComposableArrows.mk₀ x)) =
      SSet.realizedVertex (X := nerve (SInverse (Core C) (Core C)))
        (ComposableArrows.mk₀ (E.inverse.obj x)) :=
    congrArg (SSet.realizedVertex (X := nerve (SInverse (Core C) (Core C))))
      (nerveMap_app_mk₀ E.inverse x)
  have hObj : E.inverse.obj x = y := originalCoreInverseZeroObject.{uR, uM} R
  have hObjectVertex : SSet.realizedVertex (X := nerve (SInverse (Core C) (Core C)))
      (ComposableArrows.mk₀ (E.inverse.obj x)) =
      SSet.realizedVertex (X := nerve (SInverse (Core C) (Core C))) (ComposableArrows.mk₀ y) :=
    congrArg (fun z : SInverse (Core C) (Core C) => SSet.realizedVertex
      (X := nerve (SInverse (Core C) (Core C))) (ComposableArrows.mk₀ z)) hObj
  have hCompleted : SSet.realizedVertex (X := nerve (SInverse (Core C) (Core C)))
      (ComposableArrows.mk₀ y) = BasedSplitExactQLoop.completedCorePoint (C := C) := rfl
  exact (congrArg M hPoint).trans
    (hVertex.trans (hChain.trans (hObjectVertex.trans hCompleted)))

/-- The actual native-zero-to-Q map uses only original inclusion/Core/Q forward recipes. -/
public def originalNativeZeroToQLoops.{uR, uM, uNative} (R : Type uR) [Ring R] :
    C(RingK0.projectiveZeroSpace.{uR, uM, uNative} R,
      BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max uR uM} R)) := by
  let C := FGProjectiveCat.{max uR uM} R
  let I := nativeOriginalRealizationIso.{max uR uM + 1, max uR uM, uNative} (C := C)
  let E := coreAdditivePairEquivalence (C := C)
  let J := nativeZeroInclusion.{max uR uM + 1, max uR uM, uNative} (C := C)
  exact (BasedSplitExactQLoop.comparisonMap (C := C)).hom.comp
    ((SSet.toTop.map (nerveMap E.inverse)).hom.comp (I.hom.hom.comp J))

private theorem originalNativeZeroToQLoopsPointComputed.{uR, uM, uNative}
    (R : Type uR) [Ring R] :
    originalNativeZeroToQLoops.{uR, uM, uNative} R
        (RingK0.projectiveZeroPoint.{uR, uM, uNative} R) =
      BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR uM} R) := by
  let C := FGProjectiveCat.{max uR uM} R
  let I := nativeOriginalRealizationIso.{max uR uM + 1, max uR uM, uNative} (C := C)
  let E := coreAdditivePairEquivalence (C := C)
  let J := nativeZeroInclusion.{max uR uM + 1, max uR uM, uNative} (C := C)
  have hNative : J (RingK0.projectiveZeroPoint.{uR, uM, uNative} R) =
      nativeOriginalPoint.{max uR uM + 1, max uR uM, uNative} (C := C) :=
    (congrArg J (RingK0.projectiveZeroPoint_eq_native.{uR, uM, uNative} R)).trans
      (nativeZeroInclusion_point.{max uR uM + 1, max uR uM, uNative} (C := C))
  have hOrdinary := nativeOriginalRealizationIso_point.{max uR uM + 1, max uR uM, uNative}
    (C := C)
  have hCore := originalCoreInverseRealizationZeroPoint.{uR, uM} R
  have hQ := BasedSplitExactQLoop.comparisonMap_point (C := C)
  exact (congrArg (fun z => (BasedSplitExactQLoop.comparisonMap (C := C))
      (SSet.toTop.map (nerveMap E.inverse) (I.hom z))) hNative).trans
    ((congrArg (fun y => (BasedSplitExactQLoop.comparisonMap (C := C))
      (SSet.toTop.map (nerveMap E.inverse) y)) hOrdinary).trans
      ((congrArg (BasedSplitExactQLoop.comparisonMap (C := C)) hCore).trans hQ))

/-- The genuine comparator retains the original native and original constant-Q-loop points. -/
public theorem originalNativeZeroToQLoops_point.{uR, uM, uNative}
    (R : Type uR) [Ring R] :
    originalNativeZeroToQLoops.{uR, uM, uNative} R
        (RingK0.projectiveZeroPoint.{uR, uM, uNative} R) =
      BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR uM} R) :=
  originalNativeZeroToQLoopsPointComputed.{uR, uM, uNative} R

/-- The exact original normalization backward map precedes this canonical Q comparator. -/
public def originalNormalizedPlusToQLoops.{uR, uM, uNative} (R : Type uR) [Ring R] :
    C(StableGL.independentBGLCellTarget R,
      BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max uR uM} R)) :=
  (originalNativeZeroToQLoops.{uR, uM, uNative} R).comp
    (StableGL.nativeProjectiveZeroPlusNormalizationOfRing.{uR, uM, uNative} R).equiv.invFun

private theorem originalNormalizedPlusToQLoopsPointComputed.{uR, uM, uNative}
    (R : Type uR) [Ring R] :
    originalNormalizedPlusToQLoops.{uR, uM, uNative} R (StableGL.independentBGLCellPoint R) =
      BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR uM} R) := by
  let Q := originalNativeZeroToQLoops.{uR, uM, uNative} R
  let N := StableGL.nativeProjectiveZeroPlusNormalizationOfRing.{uR, uM, uNative} R
  exact (congrArg Q N.backwardPoint).trans (originalNativeZeroToQLoops_point.{uR, uM, uNative} R)

/-- The genuine plus/Q comparator preserves the SAME original independent plus root. -/
public theorem originalNormalizedPlusToQLoops_point.{uR, uM, uNative}
    (R : Type uR) [Ring R] :
    originalNormalizedPlusToQLoops.{uR, uM, uNative} R (StableGL.independentBGLCellPoint R) =
      BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR uM} R) :=
  originalNormalizedPlusToQLoopsPointComputed.{uR, uM, uNative} R

/-- The genuine original BGL/Q source map uses the exact226 normalized source recipe. -/
public def originalNormalizedBGLToQLoopsSource.{uR, uM, uNative} (R : Type uR) [Ring R] :
    C(StableGL.ordinaryBGL R,
      BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max uR uM} R)) :=
  (originalNativeZeroToQLoops.{uR, uM, uNative} R).comp
    (StableGL.nativeProjectiveZeroPlusNormalizationOfRing.{uR, uM, uNative} R).sourceMap

private theorem originalNormalizedBGLToQLoopsSourcePointComputed.{uR, uM, uNative}
    (R : Type uR) [Ring R] :
    originalNormalizedBGLToQLoopsSource.{uR, uM, uNative} R (StableGL.ordinaryBGLBasepoint R) =
      BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR uM} R) := by
  let Q := originalNativeZeroToQLoops.{uR, uM, uNative} R
  let N := StableGL.nativeProjectiveZeroPlusNormalizationOfRing.{uR, uM, uNative} R
  exact (congrArg Q N.sourcePoint).trans (originalNativeZeroToQLoops_point.{uR, uM, uNative} R)

/-- The actual BGL source root maps to the SAME original constant Q loop. -/
public theorem originalNormalizedBGLToQLoopsSource_point.{uR, uM, uNative}
    (R : Type uR) [Ring R] :
    originalNormalizedBGLToQLoopsSource.{uR, uM, uNative} R (StableGL.ordinaryBGLBasepoint R) =
      BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR uM} R) :=
  originalNormalizedBGLToQLoopsSourcePointComputed.{uR, uM, uNative} R

private theorem originalNormalizedPlusToQLoopsSourceTriangleComputed.{uR, uM, uNative}
    (R : Type uR) [Ring R] :
    (originalNormalizedPlusToQLoops.{uR, uM, uNative} R).comp
        (StableGL.independentBGLCellInclusion R).hom =
      originalNormalizedBGLToQLoopsSource.{uR, uM, uNative} R := by
  let Q := originalNativeZeroToQLoops.{uR, uM, uNative} R
  let N := StableGL.nativeProjectiveZeroPlusNormalizationOfRing.{uR, uM, uNative} R
  have hAssoc : (Q.comp N.equiv.invFun).comp (StableGL.independentBGLCellInclusion R).hom =
      Q.comp (N.equiv.invFun.comp (StableGL.independentBGLCellInclusion R).hom) := by
    apply ContinuousMap.ext
    intro x
    rfl
  exact hAssoc.trans (congrArg (fun f => Q.comp f) N.inverseSourceTriangle)

/-- The original STRICT inverse source triangle derives the actual BGL/plus/Q source triangle. -/
public theorem originalNormalizedPlusToQLoops_sourceTriangle.{uR, uM, uNative}
    (R : Type uR) [Ring R] :
    (originalNormalizedPlusToQLoops.{uR, uM, uNative} R).comp
        (StableGL.independentBGLCellInclusion R).hom =
      originalNormalizedBGLToQLoopsSource.{uR, uM, uNative} R :=
  originalNormalizedPlusToQLoopsSourceTriangleComputed.{uR, uM, uNative} R

/-- The original split-exact Q comparison retains its literal return and BOTH complete families. -/
public def originalCanonicalQCoreInverseFamilies.{uR, uM}
    (R : Type uR) [Ring R] :
    let C := FGProjectiveCat.{max uR uM} R
    let D := BasedSplitExactQLoop.comparison (C := C)
      (originalCanonicalProjectiveSplitRows.{uR, uM} R)
    ContinuousMap.HomotopyRel
      (D.loopInverse.comp (BasedSplitExactQLoop.comparisonMap (C := C)).hom)
      (ContinuousMap.id (BasedSplitExactQLoop.completedCoreSpace (C := C)))
      {BasedSplitExactQLoop.completedCorePoint (C := C)} ×
    ContinuousMap.HomotopyRel
      ((BasedSplitExactQLoop.comparisonMap (C := C)).hom.comp D.loopInverse)
      (ContinuousMap.id (BasedSplitExactQLoop.originalQLoops (C := C)))
      {BasedSplitExactQLoop.constantQLoop (C := C)} := by
  let C := FGProjectiveCat.{max uR uM} R
  let D := BasedSplitExactQLoop.comparison (C := C)
      (originalCanonicalProjectiveSplitRows.{uR, uM} R)
  exact ⟨D.loopSourceHomotopy, D.loopTargetHomotopy⟩

end AlgebraicKTheory.QuillenPlus

end


noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open CategoryTheory.CoreLocalizationComparison
open CategoryTheory.SInverseS.ComponentTranslation
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ContinuousMap

attribute [local instance] MonoidalActionCategory.diagonalAction

namespace AlgebraicKTheory.QuillenPlus

private theorem originalNativeZeroToQLoopsValueComputed.{uR, uM, uNative}
    (R : Type uR) [Ring R] : originalNativeZeroToQLoops.{uR, uM, uNative} R =
      (BasedSplitExactQLoop.comparisonMap (C := FGProjectiveCat.{max uR uM} R)).hom.comp
        ((SSet.toTop.map (nerveMap
          (coreAdditivePairEquivalence (C := FGProjectiveCat.{max uR uM} R)).inverse)).hom.comp
          ((nativeOriginalRealizationIso.{max uR uM + 1, max uR uM, uNative}
            (C := FGProjectiveCat.{max uR uM} R)).hom.hom.comp
            (nativeZeroInclusion.{max uR uM + 1, max uR uM, uNative}
              (C := FGProjectiveCat.{max uR uM} R)))) := by
  rfl

/-- The WHOLE genuine Q comparator has its exact original inclusion/Core/κ recipe. -/
public theorem originalNativeZeroToQLoops_value.{uR, uM, uNative}
    (R : Type uR) [Ring R] : originalNativeZeroToQLoops.{uR, uM, uNative} R =
      (BasedSplitExactQLoop.comparisonMap (C := FGProjectiveCat.{max uR uM} R)).hom.comp
        ((SSet.toTop.map (nerveMap
          (coreAdditivePairEquivalence (C := FGProjectiveCat.{max uR uM} R)).inverse)).hom.comp
          ((nativeOriginalRealizationIso.{max uR uM + 1, max uR uM, uNative}
            (C := FGProjectiveCat.{max uR uM} R)).hom.hom.comp
            (nativeZeroInclusion.{max uR uM + 1, max uR uM, uNative}
              (C := FGProjectiveCat.{max uR uM} R)))) :=
  originalNativeZeroToQLoopsValueComputed R

private theorem originalNormalizedPlusToQLoopsValueComputed.{uR, uM, uNative}
    (R : Type uR) [Ring R] : originalNormalizedPlusToQLoops.{uR, uM, uNative} R =
      (originalNativeZeroToQLoops.{uR, uM, uNative} R).comp
        (StableGL.nativeProjectiveZeroPlusNormalizationOfRing.{uR, uM, uNative} R).equiv.invFun :=
  by
    rfl

/-- The WHOLE source-bearing plus/Q map uses the SAME exact226 normalization backward map. -/
public theorem originalNormalizedPlusToQLoops_value.{uR, uM, uNative}
    (R : Type uR) [Ring R] : originalNormalizedPlusToQLoops.{uR, uM, uNative} R =
      (originalNativeZeroToQLoops.{uR, uM, uNative} R).comp
        (StableGL.nativeProjectiveZeroPlusNormalizationOfRing.{uR, uM, uNative} R).equiv.invFun :=
  originalNormalizedPlusToQLoopsValueComputed R

end AlgebraicKTheory.QuillenPlus

end
