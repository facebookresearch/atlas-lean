/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.Comparison.ScalarExtension
public import MathlibExt.KTheory.Exact.Extension.CompletedCoreOriginalScalarLoopNaturality
public import MathlibExt.KTheory.Ring.Comparison.OriginalNormalizedQPositiveComparison
public import MathlibExt.KTheory.Ring.StableGeneralLinear.NativeProjectiveScalarK1Naturality
public import MathlibExt.KTheory.Ring.StableGeneralLinear.MixedOriginalQK0Naturality

/-!
# Actual native zero inclusion, original Core inverse and scalar Q maps

The intrinsic scalar functor, original zero inclusion and actual native
realization Isos give the original Core inverse square. The old Core/Pair
counit and zero-functor inclusion Iso supply its whole families. The original
Core/Q scalar square and SAME chosen native retuning then compare the actual
native/Q maps. The prescribed original081 and strict-point roots are earned
in the actual loop target, with every original map and choice retained.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.CoreLocalizationComparison
open CategoryTheory.SInverseS.ComponentTranslation
open AlgebraicKTheory.QuillenMixedUniverseTransport
open AlgebraicKTheory.OriginalQuillenUnliftedTransport
open AlgebraicKTheory.OriginalQZeroComparison
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal
  CategoryTheory.MonoidalCategory ContinuousMap Simplicial Topology

attribute [local instance] MonoidalActionCategory.diagonalAction
attribute [local instance] AlgebraicKTheory.StableGL.nativeProjectiveZeroScalarFunctor_additive
attribute [local instance] AlgebraicKTheory.StableGL.nativeProjectiveZeroScalarFunctor_isExact

universe uR uS uMR uMS uNR uNS

namespace AlgebraicKTheory.QuillenPlus

private abbrev originalNativeZeroCoreMap.{uR', uMR', uNR'}
    (R : Type uR') [Ring R] :
    C(RingK0.projectiveZeroSpace.{uR', uMR', uNR'} R,
      BasedSplitExactQLoop.completedCoreSpace (C := FGProjectiveCat.{max uR' uMR'} R)) :=
  (SSet.toTop.map (nerveMap
    (coreAdditivePairEquivalence (C := FGProjectiveCat.{max uR' uMR'} R)).inverse)).hom.comp
      ((nativeOriginalRealizationIso.{max uR' uMR' + 1, max uR' uMR', uNR'}
        (C := FGProjectiveCat.{max uR' uMR'} R)).hom.hom.comp
          (nativeZeroInclusion.{max uR' uMR' + 1, max uR' uMR', uNR'}
            (C := FGProjectiveCat.{max uR' uMR'} R)))

private abbrev originalCoreNQLoopMap.{uR', uMR'}
    (R : Type uR') [Ring R] :=
  (originalNQLoopPointHomeomorph (FGProjectiveCat.{max uR' uMR'} R)).symm.toHomotopyEquiv.toFun.comp
    (BasedSplitExactQLoop.comparisonMap (C := FGProjectiveCat.{max uR' uMR'} R)).hom

private abbrev originalNativeZeroNQLoopMap.{uR', uMR', uNR'}
    (R : Type uR') [Ring R] :=
  (originalNQLoopPointHomeomorph (FGProjectiveCat.{max uR' uMR'} R)).symm.toHomotopyEquiv.toFun.comp
    (originalNativeZeroToQLoops.{uR', uMR', uNR'} R)

private theorem originalNativeZeroQCoreRecipe.{uR', uMR', uNR'}
    (R : Type uR') [Ring R] :
    originalNativeZeroNQLoopMap.{uR', uMR', uNR'} R =
      (originalCoreNQLoopMap.{uR', uMR'} R).comp (originalNativeZeroCoreMap.{uR', uMR', uNR'} R) :=
          by
  unfold originalNativeZeroNQLoopMap originalCoreNQLoopMap originalNativeZeroCoreMap
  rw [originalNativeZeroToQLoops_value]
  apply ContinuousMap.ext
  intro x
  rfl

private theorem originalNativeZeroInclusionRealizationValue.{uR', uMR', uNR'}
    (R : Type uR') [Ring R] :
    (nativeOriginalRealizationIso.{max uR' uMR' + 1, max uR' uMR', uNR'}
        (C := FGProjectiveCat.{max uR' uMR'} R)).hom.hom.comp
      (nativeZeroInclusion.{max uR' uMR' + 1, max uR' uMR', uNR'}
        (C := FGProjectiveCat.{max uR' uMR'} R)) =
    (SSet.toTop.map (nerveMap
      (SInverseS.zeroComponentProperty (C := FGProjectiveCat.{max uR' uMR'} R)).ι)).hom.comp
        (nativeZeroRealizationIso.{max uR' uMR' + 1, max uR' uMR', uNR'}
          (C := FGProjectiveCat.{max uR' uMR'} R)).hom.hom := by
  apply ContinuousMap.ext
  intro z
  let C0 := FGProjectiveCat.{max uR' uMR'} R
  let J := CGWH.cgwhToTop.{uNR', max (max uR' uMR' + 1) (max uR' uMR')}.map
    (SInverseS.zeroComponentClassifyingSpaceInclusion.{uNR'} C0)
  let I := nativeOriginalRealizationIso.{max uR' uMR' + 1, max uR' uMR', uNR'} (C := C0)
  let Z := nativeZeroRealizationIso.{max uR' uMR' + 1, max uR' uMR', uNR'} (C := C0)
  let K := SSet.toTop.map (nerveMap (SInverseS.zeroComponentProperty (C := C0)).ι)
  have hNat := ConcreteCategory.congr_hom
    (nativeZeroInclusion_realization.{max uR' uMR' + 1, max uR' uMR', uNR'} (C := C0)) z
  have hWhole := DFunLike.congr_fun
    (nativeZeroInclusion_value.{max uR' uMR' + 1, max uR' uMR', uNR'} (C := C0)) z
  exact (congrArg I.hom hWhole).trans
    ((TopCat.comp_app J I.hom z).symm.trans (hNat.trans (TopCat.comp_app Z.hom K z)))

private theorem originalCoreInverseRealMapValue.{uR', uMR'}
    (R : Type uR') [Ring R] :
    realizedNerveFunctorMap
        (coreAdditivePairEquivalence (C := FGProjectiveCat.{max uR' uMR'} R)).inverse =
      (SSet.toTop.map (nerveMap
        (coreAdditivePairEquivalence (C := FGProjectiveCat.{max uR' uMR'} R)).inverse)).hom :=
  realizedNerveFunctorMap_sameFrame _

private theorem originalZeroInclusionRealMapValue.{uR', uMR'}
    (R : Type uR') [Ring R] :
    realizedNerveFunctorMap
        (SInverseS.zeroComponentProperty (C := FGProjectiveCat.{max uR' uMR'} R)).ι =
      (SSet.toTop.map (nerveMap
        (SInverseS.zeroComponentProperty (C := FGProjectiveCat.{max uR' uMR'} R)).ι)).hom :=
  realizedNerveFunctorMap_sameFrame _

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
variable (f : R →+* S)

private def originalCoreInverseScalarIso :
    (coreAdditivePairEquivalence (C := FGProjectiveCat.{max uR uMR} R)).inverse ⋙
        completedCoreFunctor (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f) ≅
      SInverseS.pairFunctor (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f) ⋙
        (coreAdditivePairEquivalence (C := FGProjectiveCat.{max uS uMS} S)).inverse := by
  let E := coreAdditivePairEquivalence (C := FGProjectiveCat.{max uR uMR} R)
  let P := SInverseS.pairFunctor (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)
  let G := (coreAdditivePairEquivalence (C := FGProjectiveCat.{max uS uMS} S)).inverse
  rw [completedCoreFunctor_value]
  exact (Functor.associator E.inverse E.functor (P ⋙ G)).symm ≪≫
    Functor.isoWhiskerRight E.counitIso (P ⋙ G) ≪≫ Functor.leftUnitor (P ⋙ G)

private def originalCoreInverseScalarRealHomotopy :
    ContinuousMap.Homotopy
      ((realizedNerveFunctorMap
        (completedCoreFunctor (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS}
            f))).comp
          (SSet.toTop.map (nerveMap
            (coreAdditivePairEquivalence (C := FGProjectiveCat.{max uR uMR} R)).inverse)).hom)
      ((SSet.toTop.map (nerveMap
        (coreAdditivePairEquivalence (C := FGProjectiveCat.{max uS uMS} S)).inverse)).hom.comp
          (realizedNerveFunctorMap
            (SInverseS.pairFunctor (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS}
                f)))) := by
  let A := (coreAdditivePairEquivalence (C := FGProjectiveCat.{max uR uMR} R)).inverse
  let K := completedCoreFunctor (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)
  let P := SInverseS.pairFunctor (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)
  let B := (coreAdditivePairEquivalence (C := FGProjectiveCat.{max uS uMS} S)).inverse
  let H := realizedNerveFunctorMapHomotopy (originalCoreInverseScalarIso.{uR, uS, uMR, uMS} f).hom
  have hL := realizedNerveFunctorMap_comp_independent A K
  have hR := realizedNerveFunctorMap_comp_independent P B
  rw [originalCoreInverseRealMapValue.{uR, uMR} R] at hL
  rw [originalCoreInverseRealMapValue.{uS, uMS} S] at hR
  exact H.cast hL hR

private def originalZeroInclusionScalarRealHomotopy :
    ContinuousMap.Homotopy
      ((SSet.toTop.map (nerveMap
        (SInverseS.zeroComponentProperty (C := FGProjectiveCat.{max uS uMS} S)).ι)).hom.comp
          (realizedNerveFunctorMap
            (StableGL.nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f)))
      ((realizedNerveFunctorMap
        (SInverseS.pairFunctor (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS}
            f))).comp
          (SSet.toTop.map (nerveMap
            (SInverseS.zeroComponentProperty (C := FGProjectiveCat.{max uR uMR} R)).ι)).hom) := by
  let F := StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f
  let Z := StableGL.nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS} f
  let A := (SInverseS.zeroComponentProperty (C := FGProjectiveCat.{max uR uMR} R)).ι
  let B := (SInverseS.zeroComponentProperty (C := FGProjectiveCat.{max uS uMS} S)).ι
  let H := realizedNerveFunctorMapHomotopy (SInverseS.zeroComponentFunctorInclusionIso F).hom
  have hL := realizedNerveFunctorMap_comp_independent Z B
  have hR := realizedNerveFunctorMap_comp_independent A (SInverseS.pairFunctor F)
  rw [originalZeroInclusionRealMapValue.{uS, uMS} S] at hL
  rw [originalZeroInclusionRealMapValue.{uR, uMR} R] at hR
  exact H.cast hL hR

private theorem originalNativeScalarRawDirectRealization :
    (nativeZeroRealizationIso.{max uS uMS + 1, max uS uMS, uNS}
        (C := FGProjectiveCat.{max uS uMS} S)).hom.hom.comp
      (StableGL.nativeProjectiveZeroScalarRawMap.{uR, uS, uMR, uMS, uNR, uNS} f) =
    (realizedNerveFunctorMap (StableGL.nativeProjectiveZeroScalarZeroFunctor.{uR, uS, uMR, uMS}
        f)).comp
      (nativeZeroRealizationIso.{max uR uMR + 1, max uR uMR, uNR}
        (C := FGProjectiveCat.{max uR uMR} R)).hom.hom := by
  rw [StableGL.nativeProjectiveZeroScalarRawMap_value]
  apply ContinuousMap.ext
  intro x
  exact TopCat.inv_hom_id_apply
    (nativeZeroRealizationIso.{max uS uMS + 1, max uS uMS, uNS}
      (C := FGProjectiveCat.{max uS uMS} S)) _

private def originalNativeZeroCoreScalarRawHomotopy :
    ContinuousMap.Homotopy
      ((realizedNerveFunctorMap
        (completedCoreFunctor (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS}
            f))).comp
          (originalNativeZeroCoreMap.{uR, uMR, uNR} R))
      ((originalNativeZeroCoreMap.{uS, uMS, uNS} S).comp
        (StableGL.nativeProjectiveZeroScalarRawMap.{uR, uS, uMR, uMS, uNR, uNS} f)) := by
  let IR := (nativeOriginalRealizationIso.{max uR uMR + 1, max uR uMR, uNR}
    (C := FGProjectiveCat.{max uR uMR} R)).hom.hom.comp
      (nativeZeroInclusion.{max uR uMR + 1, max uR uMR, uNR}
        (C := FGProjectiveCat.{max uR uMR} R))
  let I0 := (nativeZeroRealizationIso.{max uR uMR + 1, max uR uMR, uNR}
    (C := FGProjectiveCat.{max uR uMR} R)).hom.hom
  let G := (SSet.toTop.map (nerveMap
    (coreAdditivePairEquivalence (C := FGProjectiveCat.{max uS uMS} S)).inverse)).hom
  let P := realizedNerveFunctorMap
    (SInverseS.pairFunctor (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f))
  let iS := (SSet.toTop.map (nerveMap
    (SInverseS.zeroComponentProperty (C := FGProjectiveCat.{max uS uMS} S)).ι)).hom
  let H1 := (originalCoreInverseScalarRealHomotopy.{uR, uS, uMR, uMS} f).compContinuousMap IR
  let H2 := (ContinuousMap.Homotopy.refl G).comp
    ((originalZeroInclusionScalarRealHomotopy.{uR, uS, uMR, uMS} f).symm.compContinuousMap I0)
  refine (H1.cast ?_ ?_).trans (H2.cast rfl ?_)
  · apply ContinuousMap.ext
    intro x
    rfl
  · apply ContinuousMap.ext
    intro x
    exact congrArg (fun z => G (P z))
      (congrArg (fun m => m x) (originalNativeZeroInclusionRealizationValue.{uR, uMR, uNR} R))
  · apply ContinuousMap.ext
    intro x
    have hIncl := congrArg
      (fun m => m (StableGL.nativeProjectiveZeroScalarRawMap.{uR, uS, uMR, uMS, uNR, uNS} f x))
      (originalNativeZeroInclusionRealizationValue.{uS, uMS, uNS} S)
    have hRaw := congrArg (fun m => m x)
      (originalNativeScalarRawDirectRealization.{uR, uS, uMR, uMS, uNR, uNS} f)
    exact congrArg G (hIncl.trans (congrArg iS hRaw)).symm

private def originalNativeZeroQScalarUncalibratedHomotopy :
    ContinuousMap.Homotopy
      ((mixedNQKSpaceMap (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)).comp
        (originalNativeZeroNQLoopMap.{uR, uMR, uNR} R))
      ((originalNativeZeroNQLoopMap.{uS, uMS, uNS} S).comp
        (StableGL.nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f)) := by
  let F := StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f
  let A := originalNativeZeroCoreMap.{uR, uMR, uNR} R
  let B := originalCoreNQLoopMap.{uS, uMS} S
  let Q := originalNativeZeroNQLoopMap.{uS, uMS, uNS} S
  let H1 := (completedCoreOriginalScalarQLoopHomotopy F).compContinuousMap A
  let H2 := (ContinuousMap.Homotopy.refl B).comp
    (originalNativeZeroCoreScalarRawHomotopy.{uR, uS, uMR, uMS, uNR, uNS} f)
  let H3 := (ContinuousMap.Homotopy.refl Q).comp
    (StableGL.nativeProjectiveZeroScalarRetuning.{uR, uS, uMR, uMS, uNR, uNS} f)
  refine (H1.cast ?_ rfl).trans ((H2.cast rfl ?_).trans H3)
  · apply ContinuousMap.ext
    intro x
    exact congrArg (mixedNQKSpaceMap F)
      (congrArg (fun m => m x) (originalNativeZeroQCoreRecipe.{uR, uMR, uNR} R).symm)
  · apply ContinuousMap.ext
    intro x
    exact congrArg
      (fun m => m (StableGL.nativeProjectiveZeroScalarRawMap.{uR, uS, uMR, uMS, uNR, uNS} f x))
      (originalNativeZeroQCoreRecipe.{uS, uMS, uNS} S).symm

/-- The actual original native-zero/Q map followed by the SAME145 point inverse
preserves its specified original unit. This is a whole-point equation from157. -/
public theorem originalNativeZeroToNQLoops_point.{uR', uMR', uNR'}
    (R : Type uR') [Ring R] :
    (originalNQLoopPointHomeomorph (FGProjectiveCat.{max uR' uMR'} R)).symm
      (originalNativeZeroToQLoops.{uR', uMR', uNR'} R
        (RingK0.projectiveZeroPoint.{uR', uMR', uNR'} R)) =
      Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R)) := by
  have h := originalNativeZeroToQLoops_point.{uR', uMR', uNR'} R
  have hP :
      (originalNQLoopPointHomeomorph (FGProjectiveCat.{max uR' uMR'} R)).symm
        (Path.refl (zeroQVertex (C := FGProjectiveCat.{max uR' uMR'} R))) =
      Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R)) := by
    apply Path.ext
    funext t
    exact (originalNQLoopPointHomeomorph_symm_value _ _ t).trans
      (NQReal.basepoint_eq_realizedVertex _).symm
  exact (congrArg (originalNQLoopPointHomeomorph (FGProjectiveCat.{max uR' uMR'} R)).symm h).trans
      hP

/-- The native/Q scalar source root is SAME original081 canonical mixed Q unit,
with only the actual original native-zero/Q point equation as its source cast. -/
public def originalNativeZeroQScalarSourceRoot.{uR', uS', uMR', uMS', uNR'}
    {R : Type uR'} {S : Type uS'} [Ring R] [Ring S] (f : R →+* S) :
    Path
      (mixedNQKSpaceMap (StableGL.nativeProjectiveZeroScalarFunctor.{uR', uS', uMR', uMS'} f)
        ((originalNQLoopPointHomeomorph (FGProjectiveCat.{max uR' uMR'} R)).symm
          (originalNativeZeroToQLoops.{uR', uMR', uNR'} R
            (RingK0.projectiveZeroPoint.{uR', uMR', uNR'} R))))
      (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uS' uMS'} S))) :=
  (originalConullScalarCanonicalLoopUnit
    (StableGL.nativeProjectiveZeroScalarFunctor.{uR', uS', uMR', uMS'} f)).cast
      (congrArg (mixedNQKSpaceMap (StableGL.nativeProjectiveZeroScalarFunctor.{uR', uS', uMR', uMS'}
          f))
        (originalNativeZeroToNQLoops_point.{uR', uMR', uNR'} R)) rfl

/-- The native/Q scalar target root is the actual strict-point transport,
using060 intrinsic scalar point law and157 original Q point, with no new path choice. -/
public def originalNativeZeroQScalarTargetRoot :
    Path
      ((originalNQLoopPointHomeomorph (FGProjectiveCat.{max uS uMS} S)).symm
        (originalNativeZeroToQLoops.{uS, uMS, uNS} S
          (StableGL.nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f
            (RingK0.projectiveZeroPoint.{uR, uMR, uNR} R))))
      (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uS uMS} S))) :=
  (Path.refl (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uS uMS} S)))).cast
    ((congrArg (originalNativeZeroNQLoopMap.{uS, uMS, uNS} S)
      (StableGL.nativeProjectiveZeroScalarMap_point.{uR, uS, uMR, uMS, uNR, uNS} f)).trans
        (originalNativeZeroToNQLoops_point.{uS, uMS, uNS} S)) rfl

/-- The WHOLE original source-bearing native-zero/Q comparator is natural for
arbitrary unital RingHom and ALL six independent ring/module/native roles.
It retains the actual intrinsic native realization/Core.inverse square,201
whole Core/Q family and060 chosen retuning, with the prescribed roots calibrated
by the actual loop-target unit rectangle. -/
public def originalNativeZeroQScalarHomotopy :
    ContinuousMap.Homotopy
      ((mixedNQKSpaceMap (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)).comp
        ((originalNQLoopPointHomeomorph (FGProjectiveCat.{max uR uMR}
            R)).symm.toHomotopyEquiv.toFun.comp
          (originalNativeZeroToQLoops.{uR, uMR, uNR} R)))
      (((originalNQLoopPointHomeomorph (FGProjectiveCat.{max uS uMS}
          S)).symm.toHomotopyEquiv.toFun.comp
        (originalNativeZeroToQLoops.{uS, uMS, uNS} S)).comp
          (StableGL.nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f)) :=
  loopTargetRootCalibratedHomotopy
    (originalNativeZeroQScalarUncalibratedHomotopy.{uR, uS, uMR, uMS, uNR, uNS} f)
    (originalNativeZeroQScalarSourceRoot.{uR, uS, uMR, uMS, uNR} f)
    (originalNativeZeroQScalarTargetRoot.{uR, uS, uMR, uMS, uNR, uNS} f)

/-- The native/Q whole scalar square earns BOTH actual prescribed roots,
with EXACT original081 source unit and the original strict-point target path. -/
public theorem originalNativeZeroQScalarHomotopy_ROOT :
    (((originalNativeZeroQScalarHomotopy.{uR, uS, uMR, uMS, uNR, uNS} f).evalAt
        (RingK0.projectiveZeroPoint.{uR, uMR, uNR} R)).trans
      (originalNativeZeroQScalarTargetRoot.{uR, uS, uMR, uMS, uNR, uNS} f)).Homotopic
        (originalNativeZeroQScalarSourceRoot.{uR, uS, uMR, uMS, uNR} f) :=
  loopTargetRootCalibratedHomotopy_ROOT
    (originalNativeZeroQScalarUncalibratedHomotopy.{uR, uS, uMR, uMS, uNR, uNS} f)
    (originalNativeZeroQScalarSourceRoot.{uR, uS, uMR, uMS, uNR} f)
    (originalNativeZeroQScalarTargetRoot.{uR, uS, uMR, uMS, uNR, uNS} f)

end AlgebraicKTheory.QuillenPlus

end


/-!
# Original independent P_f and the whole normalized plus/Q scalar square

The original226 normalization backward map and original102 inverse f-chart
square attach to the actual native/Q square. Both original independent plus
maps, roots and complete inverse families remain. The whole loop-target
root calibration earns the exact081/strict-point roots before every positive
cube index is transported. All TEN original normalization family values
and both original BGL source triangles are retained.
-/

noncomputable section

universe uR uS uMR uMS uNR uNS

open CategoryTheory CategoryTheory.Limits CategoryTheory.CoreLocalizationComparison
open CategoryTheory.SInverseS.ComponentTranslation
open AlgebraicKTheory.QuillenMixedUniverseTransport
open AlgebraicKTheory.OriginalQuillenUnliftedTransport
open AlgebraicKTheory.OriginalQZeroComparison
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal
  CategoryTheory.MonoidalCategory ContinuousMap Simplicial Topology

attribute [local instance] AlgebraicKTheory.StableGL.nativeProjectiveZeroScalarFunctor_additive
attribute [local instance] AlgebraicKTheory.StableGL.nativeProjectiveZeroScalarFunctor_isExact

namespace AlgebraicKTheory.QuillenPlus

private abbrev originalNormalizedPlusNQLoopMap.{uR', uMR', uNR'}
    (R : Type uR') [Ring R] :=
  (originalNQLoopPointHomeomorph (FGProjectiveCat.{max uR' uMR'} R)).symm.toHomotopyEquiv.toFun.comp
    (originalNormalizedPlusToQLoops.{uR', uMR', uNR'} R)

private theorem originalNormalizedPlusNQRecipe.{uR', uMR', uNR'}
    (R : Type uR') [Ring R] :
    originalNormalizedPlusNQLoopMap.{uR', uMR', uNR'} R =
      (originalNativeZeroNQLoopMap.{uR', uMR', uNR'} R).comp
        (StableGL.nativeProjectiveZeroPlusNormalizationOfRing.{uR', uMR', uNR'} R).equiv.invFun :=
            by
  unfold originalNormalizedPlusNQLoopMap originalNativeZeroNQLoopMap
  rw [originalNormalizedPlusToQLoops_value]
  apply ContinuousMap.ext
  intro x
  rfl

/-- The original source-bearing normalized plus/Q comparison keeps its
original independent plus root through the SAME145 point inverse. -/
public theorem originalNormalizedPlusToNQLoops_point.{uR', uMR', uNR'}
    (R : Type uR') [Ring R] :
    (originalNQLoopPointHomeomorph (FGProjectiveCat.{max uR' uMR'} R)).symm
      (originalNormalizedPlusToQLoops.{uR', uMR', uNR'} R (StableGL.independentBGLCellPoint R)) =
      Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R)) := by
  let N := StableGL.nativeProjectiveZeroPlusNormalizationOfRing.{uR', uMR', uNR'} R
  have hRecipe := congrArg (fun m => m (StableGL.independentBGLCellPoint R))
    (originalNormalizedPlusNQRecipe.{uR', uMR', uNR'} R)
  exact hRecipe.trans ((congrArg (originalNativeZeroNQLoopMap.{uR', uMR', uNR'} R)
      N.backwardPoint).trans
    (originalNativeZeroToNQLoops_point.{uR', uMR', uNR'} R))

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
variable (f : R →+* S)

private def originalNormalizedPlusQScalarUncalibratedHomotopy :
    ContinuousMap.Homotopy
      ((mixedNQKSpaceMap (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)).comp
        (originalNormalizedPlusNQLoopMap.{uR, uMR, uNR} R))
      ((originalNormalizedPlusNQLoopMap.{uS, uMS, uNS} S).comp (StableGL.independentBGLScalarPlusMap
          f)) := by
  let N := StableGL.nativeProjectiveZeroPlusNormalizationOfRing.{uR, uMR, uNR} R
  let B := originalNativeZeroNQLoopMap.{uS, uMS, uNS} S
  let F := StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f
  let H1 := (originalNativeZeroQScalarHomotopy.{uR, uS, uMR, uMS, uNR, uNS} f).compContinuousMap
    N.equiv.invFun
  let H2 := (ContinuousMap.Homotopy.refl B).comp
    (StableGL.nativeProjectiveZeroScalarOriginalInverseSquare.{uR, uS, uMR, uMS, uNR, uNS}
        f).toHomotopy
  refine (H1.cast ?_ rfl).trans (H2.cast rfl ?_)
  · apply ContinuousMap.ext
    intro x
    exact congrArg (mixedNQKSpaceMap F)
      (congrArg (fun m => m x) (originalNormalizedPlusNQRecipe.{uR, uMR, uNR} R).symm)
  · apply ContinuousMap.ext
    intro x
    exact congrArg (fun m => m (StableGL.independentBGLScalarPlusMap f x))
      (originalNormalizedPlusNQRecipe.{uS, uMS, uNS} S).symm

/-- The plus/Q scalar source uses EXACT original081 canonical Q-loop unit,
with the ORIGINAL plus/Q point law as its only source transport. -/
public def originalNormalizedPlusQScalarSourceRoot.{uR', uS', uMR', uMS', uNR'}
    {R : Type uR'} {S : Type uS'} [Ring R] [Ring S] (f : R →+* S) :
    Path
      (mixedNQKSpaceMap (StableGL.nativeProjectiveZeroScalarFunctor.{uR', uS', uMR', uMS'} f)
        ((originalNQLoopPointHomeomorph (FGProjectiveCat.{max uR' uMR'} R)).symm
          (originalNormalizedPlusToQLoops.{uR', uMR', uNR'} R (StableGL.independentBGLCellPoint
              R))))
      (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uS' uMS'} S))) :=
  (originalConullScalarCanonicalLoopUnit
    (StableGL.nativeProjectiveZeroScalarFunctor.{uR', uS', uMR', uMS'} f)).cast
      (congrArg (mixedNQKSpaceMap (StableGL.nativeProjectiveZeroScalarFunctor.{uR', uS', uMR', uMS'}
          f))
        (originalNormalizedPlusToNQLoops_point.{uR', uMR', uNR'} R)) rfl

/-- The plus/Q scalar target uses the actual independent P_f marked-point
law and SAME original plus/Q point; the reflexive path is only endpoint-cast. -/
public def originalNormalizedPlusQScalarTargetRoot.{uR', uS', uMS', uNS'}
    {R : Type uR'} {S : Type uS'} [Ring R] [Ring S] (f : R →+* S) :
    Path
      ((originalNQLoopPointHomeomorph (FGProjectiveCat.{max uS' uMS'} S)).symm
        (originalNormalizedPlusToQLoops.{uS', uMS', uNS'} S
          (StableGL.independentBGLScalarPlusMap f (StableGL.independentBGLCellPoint R))))
      (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uS' uMS'} S))) :=
  (Path.refl (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uS' uMS'} S)))).cast
    ((congrArg (originalNormalizedPlusNQLoopMap.{uS', uMS', uNS'} S)
      (StableGL.independentBGLScalarPlusMap_point f)).trans
        (originalNormalizedPlusToNQLoops_point.{uS', uMS', uNS'} S)) rfl

/-- The WHOLE genuine original normalized plus/Q map is scalar natural for
SAME independent P_f, actual intrinsic scalar functor and all SIX independent
roles. Both original normalization inverse families and root choices remain. -/
public def originalNormalizedPlusQScalarHomotopy :
    ContinuousMap.Homotopy
      ((mixedNQKSpaceMap (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)).comp
        ((originalNQLoopPointHomeomorph (FGProjectiveCat.{max uR uMR}
            R)).symm.toHomotopyEquiv.toFun.comp
          (originalNormalizedPlusToQLoops.{uR, uMR, uNR} R)))
      (((originalNQLoopPointHomeomorph (FGProjectiveCat.{max uS uMS}
          S)).symm.toHomotopyEquiv.toFun.comp
        (originalNormalizedPlusToQLoops.{uS, uMS, uNS} S)).comp
            (StableGL.independentBGLScalarPlusMap f)) :=
  loopTargetRootCalibratedHomotopy
    (originalNormalizedPlusQScalarUncalibratedHomotopy.{uR, uS, uMR, uMS, uNR, uNS} f)
    (originalNormalizedPlusQScalarSourceRoot.{uR, uS, uMR, uMS, uNR} f)
    (originalNormalizedPlusQScalarTargetRoot.{uR, uS, uMS, uNS} f)

/-- The original independent plus/Q scalar WHOLE homotopy earns its two
prescribed roots before any positive group transport. -/
public theorem originalNormalizedPlusQScalarHomotopy_ROOT :
    (((originalNormalizedPlusQScalarHomotopy.{uR, uS, uMR, uMS, uNR, uNS} f).evalAt
        (StableGL.independentBGLCellPoint R)).trans
      (originalNormalizedPlusQScalarTargetRoot.{uR, uS, uMS, uNS} f)).Homotopic
        (originalNormalizedPlusQScalarSourceRoot.{uR, uS, uMR, uMS, uNR} f) :=
  loopTargetRootCalibratedHomotopy_ROOT
    (originalNormalizedPlusQScalarUncalibratedHomotopy.{uR, uS, uMR, uMS, uNR, uNS} f)
    (originalNormalizedPlusQScalarSourceRoot.{uR, uS, uMR, uMS, uNR} f)
    (originalNormalizedPlusQScalarTargetRoot.{uR, uS, uMS, uNS} f)

/-- EVERY positive original cube index of the actual source-bearing normalized
Q comparison is natural for ORIGINAL independent P_f and both prescribed roots.
This follows only after the actual whole ROOT proof; basepoint action is kept. -/
public theorem originalNormalizedPlusQScalar_allIndices (n : ℕ) :
  letI : Group (HomotopyGroup.Pi (n + 1) (NQKSpace (FGProjectiveCat.{max uS uMS} S))
      (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uS uMS} S)) :
        NQKSpace (FGProjectiveCat.{max uS uMS} S))) :=
    HomotopyGroup.group (X := NQKSpace (FGProjectiveCat.{max uS uMS} S))
      (x := (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uS uMS} S)) :
        NQKSpace (FGProjectiveCat.{max uS uMS} S))) (Fin (n + 1));
    (TopCat.homotopyGroupBasepointChangeMulEquiv n
      (TopCat.of (NQKSpace (FGProjectiveCat.{max uS uMS} S)))
      (originalNormalizedPlusQScalarSourceRoot.{uR, uS, uMR, uMS, uNR} f)).toMonoidHom.comp
        (HomotopyGroup.mapHom
          ((mixedNQKSpaceMap (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)).comp
            ((originalNQLoopPointHomeomorph (FGProjectiveCat.{max uR uMR}
                R)).symm.toHomotopyEquiv.toFun.comp
              (originalNormalizedPlusToQLoops.{uR, uMR, uNR} R)))) =
    (TopCat.homotopyGroupBasepointChangeMulEquiv n
      (TopCat.of (NQKSpace (FGProjectiveCat.{max uS uMS} S)))
      (originalNormalizedPlusQScalarTargetRoot.{uR, uS, uMS, uNS} f)).toMonoidHom.comp
        (HomotopyGroup.mapHom
          (((originalNQLoopPointHomeomorph (FGProjectiveCat.{max uS uMS}
              S)).symm.toHomotopyEquiv.toFun.comp
            (originalNormalizedPlusToQLoops.{uS, uMS, uNS} S)).comp
                (StableGL.independentBGLScalarPlusMap f))) :=
  TopCat.homotopyGroup_rooted_map_homotopy_mixed n
    (originalNormalizedPlusQScalarHomotopy.{uR, uS, uMR, uMS, uNR, uNS} f)
    (originalNormalizedPlusQScalarSourceRoot.{uR, uS, uMR, uMS, uNR} f)
    (originalNormalizedPlusQScalarTargetRoot.{uR, uS, uMS, uNS} f)
    (originalNormalizedPlusQScalarHomotopy_ROOT.{uR, uS, uMR, uMS, uNR, uNS} f)

/-- The actual scalar Q attachment keeps all TEN original complete model,
inverse and source family values, BOTH f-chart families and BOTH original
strict BGL/plus/Q source triangles. -/
public theorem originalNormalizedQScalar_originalFamilyValues :
    (let A := StableGL.nativeProjectiveZeroPlusNormalizationOfRing.{uR, uMR, uNR} R
     let B := StableGL.nativeProjectiveZeroPlusNormalizationOfRing.{uS, uMS, uNS} S
     (A.modelLeft.toContinuousMap = A.data.modelLeft ∧
       A.modelRight.toContinuousMap = A.data.modelRight ∧
       A.leftFamily.toContinuousMap = A.data.leftFamily ∧
       A.rightFamily.toContinuousMap = A.data.rightFamily ∧
       A.sourceTriangle.toContinuousMap = A.data.sourceTriangle) ∧
     (B.modelLeft.toContinuousMap = B.data.modelLeft ∧
       B.modelRight.toContinuousMap = B.data.modelRight ∧
       B.leftFamily.toContinuousMap = B.data.leftFamily ∧
       B.rightFamily.toContinuousMap = B.data.rightFamily ∧
       B.sourceTriangle.toContinuousMap = B.data.sourceTriangle)) ∧
    ((StableGL.nativeProjectiveZeroScalarOriginalForwardSquare.{uR, uS, uMR, uMS, uNR, uNS}
        f).toContinuousMap =
      StableGL.nativeProjectiveZeroScalarOriginalForwardSquareFamily.{uR, uS, uMR, uMS, uNR, uNS} f)
          ∧
    ((StableGL.nativeProjectiveZeroScalarOriginalInverseSquare.{uR, uS, uMR, uMS, uNR, uNS}
        f).toContinuousMap =
      StableGL.nativeProjectiveZeroScalarOriginalInverseSquareFamily.{uR, uS, uMR, uMS, uNR, uNS} f)
          ∧
    ((originalNormalizedPlusToQLoops.{uR, uMR, uNR} R).comp (StableGL.independentBGLCellInclusion
        R).hom =
      originalNormalizedBGLToQLoopsSource.{uR, uMR, uNR} R) ∧
    ((originalNormalizedPlusToQLoops.{uS, uMS, uNS} S).comp (StableGL.independentBGLCellInclusion
        S).hom =
      originalNormalizedBGLToQLoopsSource.{uS, uMS, uNS} S) :=
  ⟨StableGL.nativeProjectiveZeroScalarOriginalNormalizationFamilyValues.{uR, uS, uMR, uMS, uNR, uNS}
      R S,
    StableGL.nativeProjectiveZeroScalarOriginalForwardSquare_toContinuousMap.{uR, uS, uMR, uMS, uNR,
        uNS} f,
    StableGL.nativeProjectiveZeroScalarOriginalInverseSquare_toContinuousMap.{uR, uS, uMR, uMS, uNR,
        uNS} f,
    originalNormalizedPlusToQLoops_sourceTriangle.{uR, uMR, uNR} R,
    originalNormalizedPlusToQLoops_sourceTriangle.{uS, uMS, uNS} S⟩

end AlgebraicKTheory.QuillenPlus

end


/-!
# Original raw Q forward and inverse class squares

The actual point homeomorphisms carry the whole normalized scalar family to
the original raw Q loop carriers. The canonical scalar map has its original
conjugation value at the literal Q zero vertices. Its own-unit path is the
mapped original081 path. The raw whole square earns this root, then the
original positive comparison maps and their actual inverses satisfy the
scalar square at every positive index.
-/

noncomputable section

universe uR uS uMR uMS uNR uNS

open CategoryTheory CategoryTheory.Limits
open AlgebraicKTheory.QuillenMixedUniverseTransport
open AlgebraicKTheory.OriginalQuillenUnliftedTransport
open AlgebraicKTheory.OriginalQZeroComparison
open scoped ContinuousMap Topology

attribute [local instance] AlgebraicKTheory.StableGL.nativeProjectiveZeroScalarFunctor_additive
attribute [local instance] AlgebraicKTheory.StableGL.nativeProjectiveZeroScalarFunctor_isExact

universe uRawQX uRawQY uRawQZ

namespace AlgebraicKTheory.QuillenPlus

private theorem originalScalarQBasepointEqZero.{uR', uMR'}
    (R : Type uR') [Ring R] :
    NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R) =
      zeroQVertex (C := FGProjectiveCat.{max uR' uMR'} R) := by
  let C := FGProjectiveCat.{max uR' uMR'} R
  let p := Path.refl (NQReal.basepoint C)
  let e := originalNQLoopPointHomeomorph C
  have h : e p 0 = NQReal.basepoint C :=
    (originalNQLoopPointHomeomorph_value C p 0).trans p.source
  exact h.symm.trans (e p).source

private theorem originalScalarQLoopPointForward.{uR', uMR'}
    (R : Type uR') [Ring R] :
    originalNQLoopPointHomeomorph (FGProjectiveCat.{max uR' uMR'} R)
        (Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R))) =
      BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR' uMR'} R) := by
  apply Path.ext
  funext t
  exact (originalNQLoopPointHomeomorph_value _ _ t).trans
    (originalScalarQBasepointEqZero.{uR', uMR'} R)

private theorem originalScalarQLoopPointInverse.{uR', uMR'}
    (R : Type uR') [Ring R] :
    (originalNQLoopPointHomeomorph (FGProjectiveCat.{max uR' uMR'} R)).symm
        (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR' uMR'} R)) =
      Path.refl (NQReal.basepoint (FGProjectiveCat.{max uR' uMR'} R)) := by
  let e := originalNQLoopPointHomeomorph (FGProjectiveCat.{max uR' uMR'} R)
  exact (congrArg e.symm (originalScalarQLoopPointForward.{uR', uMR'} R)).symm.trans
    (e.symm_apply_apply _)

private theorem originalScalarLoopCastConjugation
    {X : Type uRawQX} {Y : Type uRawQY} [TopologicalSpace X] [TopologicalSpace Y]
    {x x' : X} {y y' : Y} (hx : x = x') (hy : y = y') (f : C(X, Y))
    (p : Path (f x) y) (gamma : LoopSpace X x') :
    ((p.symm.trans (((gamma.cast hx hx).map f.continuous).trans p)).cast
        hy.symm hy.symm) =
      (p.cast (congrArg f hx).symm hy.symm).symm.trans
        ((gamma.map f.continuous).trans (p.cast (congrArg f hx).symm hy.symm)) := by
  cases hx
  cases hy
  rfl

private theorem originalScalarRootedPositiveStrictPrecompose
    {X : Type uRawQX} {Y : Type uRawQY} {Z : Type uRawQZ}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {x : X} {y : Y} {z : Z} (n : ℕ) (f : C(X, Y)) (g : C(Y, Z))
    (hf : f x = y) (p : Path (g y) z)
    (a : HomotopyGroup.Pi (n + 1) X x) :
    TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Z)
        (p.cast (congrArg g hf) rfl) (HomotopyGroup.map (g.comp f) a) =
      TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Z) p
        (HomotopyGroup.map g (HomotopyGroup.mapHomOfEq f hf n a)) := by
  subst y
  rw [HomotopyGroup.mapHomOfEq_apply]
  exact congrArg (TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Z) p)
    (HomotopyGroup.map_comp f g a)

private theorem originalScalarPositiveReflexiveRootValue
    {X : Type uRawQX} {Y : Type uRawQY} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (n : ℕ) (f : C(X, Y)) (hf : f x = y)
    (a : HomotopyGroup.Pi (n + 1) X x) :
    TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y)
        ((Path.refl y).cast hf rfl) (HomotopyGroup.map f a) =
      HomotopyGroup.mapHomOfEq f hf n a := by
  subst y
  rw [HomotopyGroup.mapHomOfEq_apply]
  exact congrArg (fun e => e (HomotopyGroup.map f a))
    (TopCat.homotopyGroupBasepointChangeMulEquiv_refl n (TopCat.of Y) (f x))

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
variable (f : R →+* S)

/-- The original canonical scalar loop map on the literal raw Q zero-point
carriers, through BOTH point homeomorphisms and the same scalar map. -/
public def originalCanonicalQLoopScalarMap :
    C(BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max uR uMR} R),
      BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max uS uMS} S)) :=
  (originalNQLoopPointHomeomorph (FGProjectiveCat.{max uS uMS} S)).toHomotopyEquiv.toFun.comp
    ((mixedNQKSpaceMap (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)).comp
      (originalNQLoopPointHomeomorph (FGProjectiveCat.{max uR uMR} R)).symm.toHomotopyEquiv.toFun)

/-- The WHOLE raw scalar map retains the actual original weak Q map. -/
public theorem originalCanonicalQLoopScalarMap_value :
    originalCanonicalQLoopScalarMap.{uR, uS, uMR, uMS} f =
      (originalNQLoopPointHomeomorph (FGProjectiveCat.{max uS uMS} S)).toHomotopyEquiv.toFun.comp
        ((mixedNQWeaklyPointedMap
          (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)).loopMap.comp
          (originalNQLoopPointHomeomorph (FGProjectiveCat.{max uR uMR}
              R)).symm.toHomotopyEquiv.toFun) := by
  unfold originalCanonicalQLoopScalarMap
  rw [mixedNQKSpaceMap_wholeWeak_value]
  rfl

/-- The SAME canonical Q.zeroComparisonIso root has only its actual
NQ-basepoint/zero-vertex equality casts at both original endpoints. -/
public def originalCanonicalQScalarRootPath :
    Path
      (mixedNQRealMap (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)
        (zeroQVertex (C := FGProjectiveCat.{max uR uMR} R)))
      (zeroQVertex (C := FGProjectiveCat.{max uS uMS} S)) :=
  (mixedNQRootPath (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)).cast
    (congrArg (mixedNQRealMap (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f))
      (originalScalarQBasepointEqZero.{uR, uMR} R).symm)
    (originalScalarQBasepointEqZero.{uS, uMS} S).symm

/-- Every raw Q loop keeps the original canonical conjugation and both clocks. -/
public theorem originalCanonicalQLoopScalarMap_apply
    (gamma : BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max uR uMR} R)) :
    originalCanonicalQLoopScalarMap.{uR, uS, uMR, uMS} f gamma =
      (originalCanonicalQScalarRootPath.{uR, uS, uMR, uMS} f).symm.trans
        ((gamma.map (mixedNQRealMap
          (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)).continuous).trans
            (originalCanonicalQScalarRootPath.{uR, uS, uMR, uMS} f)) := by
  let C := FGProjectiveCat.{max uR uMR} R
  let D := FGProjectiveCat.{max uS uMS} S
  let eR := originalNQLoopPointHomeomorph C
  let eS := originalNQLoopPointHomeomorph D
  let M := mixedNQRealMap (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)
  let q := mixedNQRootPath (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)
  let hx := originalScalarQBasepointEqZero.{uR, uMR} R
  let hy := originalScalarQBasepointEqZero.{uS, uMS} S
  have hIn : eR.symm gamma = gamma.cast hx hx := by
    apply Path.ext
    funext t
    exact originalNQLoopPointHomeomorph_symm_value C gamma t
  have hOut (delta : NQKSpace D) : eS delta = delta.cast hy.symm hy.symm := by
    apply Path.ext
    funext t
    exact originalNQLoopPointHomeomorph_value D delta t
  have h : originalCanonicalQLoopScalarMap.{uR, uS, uMR, uMS} f gamma =
      (q.symm.trans (((eR.symm gamma).map M.continuous).trans q)).cast hy.symm hy.symm :=
    (hOut (mixedNQKSpaceMap
      (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f) (eR.symm gamma))).trans
        (congrArg (fun delta : NQKSpace D => delta.cast hy.symm hy.symm)
          (mixedNQKSpaceMap_value
            (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f) (eR.symm gamma)))
  rw [hIn] at h
  exact h.trans (originalScalarLoopCastConjugation hx hy M q gamma)

/-- The own-unit root is EXACT original081 mapped by SAME145, with only
the actual original constant-loop point equations at its endpoints. -/
public def originalCanonicalQScalarLoopUnit :
    Path
      (originalCanonicalQLoopScalarMap.{uR, uS, uMR, uMS} f
        (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR uMR} R)))
      (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uS uMS} S)) :=
  ((originalConullScalarCanonicalLoopUnit
      (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)).map
        (originalNQLoopPointHomeomorph (FGProjectiveCat.{max uS uMS} S)).continuous_toFun).cast
    (congrArg (fun p => originalNQLoopPointHomeomorph (FGProjectiveCat.{max uS uMS} S)
      (mixedNQKSpaceMap (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f) p))
        (originalScalarQLoopPointInverse.{uR, uMR} R))
    (originalScalarQLoopPointForward.{uS, uMS} S).symm

private theorem originalCanonicalQScalarLoopUnitValueComputed (t s : unitInterval) :
    originalCanonicalQScalarLoopUnit.{uR, uS, uMR, uMS} f t s =
      ContinuousMap.WeaklyPointed.loopUnitRootPath
        (mixedNQWeaklyPointedMap
          (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)) t s := by
  have h : originalCanonicalQScalarLoopUnit.{uR, uS, uMR, uMS} f t s =
      ((originalConullScalarCanonicalLoopUnit
        (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)).toContinuousMap.toFun
            t).toContinuousMap.toFun s :=
    originalNQLoopPointHomeomorph_value _
      ((originalConullScalarCanonicalLoopUnit
        (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)).toContinuousMap.toFun t)
            s
  exact h.trans (congrArg (fun p : NQKSpace (FGProjectiveCat.{max uS uMS} S) =>
    p.toContinuousMap.toFun s)
      (originalConullScalarCanonicalLoopUnit_value
        (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f) t))

/-- Every own-unit and loop time retains the actual original081 unit value. -/
public theorem originalCanonicalQScalarLoopUnit_value (t s : unitInterval) :
    originalCanonicalQScalarLoopUnit.{uR, uS, uMR, uMS} f t s =
      ContinuousMap.WeaklyPointed.loopUnitRootPath
        (mixedNQWeaklyPointedMap
          (StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)) t s :=
  originalCanonicalQScalarLoopUnitValueComputed f t s

/-- The positive canonical scalar map on the ORIGINAL raw Q loop carriers
uses the actual continuous map and EXACT transported original081 root. -/
public def originalCanonicalQPositiveScalarMap (n : ℕ) :
    HomotopyGroup.Pi (n + 1)
      (BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max uR uMR} R))
      (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR uMR} R)) →*
    HomotopyGroup.Pi (n + 1)
      (BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max uS uMS} S))
      (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uS uMS} S)) :=
  ContinuousMap.WeaklyPointed.positiveHomotopyGroupMap n
    (⟨originalCanonicalQLoopScalarMap.{uR, uS, uMR, uMS} f,
      originalCanonicalQScalarLoopUnit.{uR, uS, uMR, uMS} f⟩ : ContinuousMap.WeaklyPointed
        (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR uMR} R))
        (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uS uMS} S)))

/-- Every positive original raw Q class keeps its complete own-root transport. -/
public theorem originalCanonicalQPositiveScalarMap_apply (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1)
      (BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max uR uMR} R))
      (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR uMR} R))) :
    originalCanonicalQPositiveScalarMap.{uR, uS, uMR, uMS} f n a =
      TopCat.homotopyGroupBasepointChangeMulEquiv n
        (TopCat.of (BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max uS uMS} S)))
        (originalCanonicalQScalarLoopUnit.{uR, uS, uMR, uMS} f)
          (HomotopyGroup.map (originalCanonicalQLoopScalarMap.{uR, uS, uMR, uMS} f) a) :=
  ContinuousMap.WeaklyPointed.positiveHomotopyGroupMap_apply n
    (⟨originalCanonicalQLoopScalarMap.{uR, uS, uMR, uMS} f,
      originalCanonicalQScalarLoopUnit.{uR, uS, uMR, uMS} f⟩ : ContinuousMap.WeaklyPointed
        (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR uMR} R))
        (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uS uMS} S))) a

private def originalNormalizedPlusRawQScalarUncalibratedHomotopy :
    ContinuousMap.Homotopy
      ((originalCanonicalQLoopScalarMap.{uR, uS, uMR, uMS} f).comp
        (originalNormalizedPlusToQLoops.{uR, uMR, uNR} R))
      ((originalNormalizedPlusToQLoops.{uS, uMS, uNS} S).comp
        (StableGL.independentBGLScalarPlusMap f)) := by
  let eS := originalNQLoopPointHomeomorph (FGProjectiveCat.{max uS uMS} S)
  let H := (ContinuousMap.Homotopy.refl eS.toHomotopyEquiv.toFun).comp
    (originalNormalizedPlusQScalarHomotopy.{uR, uS, uMR, uMS, uNR, uNS} f)
  refine H.cast ?_ ?_
  · apply ContinuousMap.ext
    intro x
    rfl
  · apply ContinuousMap.ext
    intro x
    exact eS.apply_symm_apply _

/-- The actual raw plus/Q square source root is SAME transported original081
unit, cast only by the original157 plus/Q marked-point equation. -/
public def originalNormalizedPlusRawQScalarSourceRoot.{uR', uS', uMR', uMS', uNR'}
    {R : Type uR'} {S : Type uS'} [Ring R] [Ring S] (f : R →+* S) :
    Path
      (originalCanonicalQLoopScalarMap.{uR', uS', uMR', uMS'} f
        (originalNormalizedPlusToQLoops.{uR', uMR', uNR'} R (StableGL.independentBGLCellPoint R)))
      (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uS' uMS'} S)) :=
  (originalCanonicalQScalarLoopUnit.{uR', uS', uMR', uMS'} f).cast
    (congrArg (originalCanonicalQLoopScalarMap.{uR', uS', uMR', uMS'} f)
      (originalNormalizedPlusToQLoops_point.{uR', uMR', uNR'} R)) rfl

/-- The raw target root follows the actual P_f point and original157 target
point equations, with the original constant path endpoint-cast. -/
public def originalNormalizedPlusRawQScalarTargetRoot.{uR', uS', uMS', uNS'}
    {R : Type uR'} {S : Type uS'} [Ring R] [Ring S] (f : R →+* S) :
    Path
      (originalNormalizedPlusToQLoops.{uS', uMS', uNS'} S
        (StableGL.independentBGLScalarPlusMap f (StableGL.independentBGLCellPoint R)))
      (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uS' uMS'} S)) :=
  (Path.refl (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uS' uMS'} S))).cast
    ((congrArg (originalNormalizedPlusToQLoops.{uS', uMS', uNS'} S)
      (StableGL.independentBGLScalarPlusMap_point f)).trans
        (originalNormalizedPlusToQLoops_point.{uS', uMS', uNS'} S)) rfl

/-- The whole original raw plus/Q square preserves its complete family,
both point maps and the derived original strict-point root equalities. -/
public def originalNormalizedPlusRawQScalarHomotopy :
    ContinuousMap.Homotopy
      ((originalCanonicalQLoopScalarMap.{uR, uS, uMR, uMS} f).comp
        (originalNormalizedPlusToQLoops.{uR, uMR, uNR} R))
      ((originalNormalizedPlusToQLoops.{uS, uMS, uNS} S).comp
        (StableGL.independentBGLScalarPlusMap f)) :=
  loopTargetRootCalibratedHomotopy
    (originalNormalizedPlusRawQScalarUncalibratedHomotopy.{uR, uS, uMR, uMS, uNR, uNS} f)
    (originalNormalizedPlusRawQScalarSourceRoot.{uR, uS, uMR, uMS, uNR} f)
    (originalNormalizedPlusRawQScalarTargetRoot.{uR, uS, uMS, uNS} f)

/-- The actual whole raw square earns its prescribed root in the original
raw loop target using the original translation rectangle and cancellation. -/
public theorem originalNormalizedPlusRawQScalarHomotopy_ROOT :
    (((originalNormalizedPlusRawQScalarHomotopy.{uR, uS, uMR, uMS, uNR, uNS} f).evalAt
        (StableGL.independentBGLCellPoint R)).trans
      (originalNormalizedPlusRawQScalarTargetRoot.{uR, uS, uMS, uNS} f)).Homotopic
        (originalNormalizedPlusRawQScalarSourceRoot.{uR, uS, uMR, uMS, uNR} f) :=
  loopTargetRootCalibratedHomotopy_ROOT
    (originalNormalizedPlusRawQScalarUncalibratedHomotopy.{uR, uS, uMR, uMS, uNR, uNS} f)
    (originalNormalizedPlusRawQScalarSourceRoot.{uR, uS, uMR, uMS, uNR} f)
    (originalNormalizedPlusRawQScalarTargetRoot.{uR, uS, uMS, uNS} f)

/-- Every positive ORIGINAL plus/Q class square uses the actual independent
P_f, canonical raw Q conjugation and EXACT transported original081 unit. -/
public theorem originalNormalizedPlusQPositiveScalarNaturality (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (StableGL.independentBGLCellTarget R)
      (StableGL.independentBGLCellPoint R)) :
    originalCanonicalQPositiveScalarMap.{uR, uS, uMR, uMS} f n
        (originalNormalizedPlusQPositiveMulEquiv.{uR, uMR, uNR} R n a) =
      originalNormalizedPlusQPositiveMulEquiv.{uS, uMS, uNS} S n
        (StableGL.originalIndependentPlusPositiveScalarMap f n a) := by
  let QR := originalNormalizedPlusToQLoops.{uR, uMR, uNR} R
  let QS := originalNormalizedPlusToQLoops.{uS, uMS, uNS} S
  let F := originalCanonicalQLoopScalarMap.{uR, uS, uMR, uMS} f
  let P := StableGL.independentBGLScalarPlusMap f
  let hR := originalNormalizedPlusToQLoops_point.{uR, uMR, uNR} R
  let hS := originalNormalizedPlusToQLoops_point.{uS, uMS, uNS} S
  let hP := StableGL.independentBGLScalarPlusMap_point f
  let hTarget := (congrArg QS hP).trans hS
  have hWhole := TopCat.homotopyGroup_rooted_map_homotopy_mixed n
    (originalNormalizedPlusRawQScalarHomotopy.{uR, uS, uMR, uMS, uNR, uNS} f)
    (originalNormalizedPlusRawQScalarSourceRoot.{uR, uS, uMR, uMS, uNR} f)
    (originalNormalizedPlusRawQScalarTargetRoot.{uR, uS, uMS, uNS} f)
    (originalNormalizedPlusRawQScalarHomotopy_ROOT.{uR, uS, uMR, uMS, uNR, uNS} f)
  have hValue := DFunLike.congr_fun hWhole a
  have hLeft := originalScalarRootedPositiveStrictPrecompose n QR F hR
    (originalCanonicalQScalarLoopUnit.{uR, uS, uMR, uMS} f) a
  have hRight := originalScalarPositiveReflexiveRootValue n (QS.comp P) hTarget a
  have hComp := HomotopyGroup.mapHomOfEq_comp P QS hP hS hTarget n a
  rw [originalNormalizedPlusQPositiveMulEquiv_apply, originalCanonicalQPositiveScalarMap_apply,
    originalNormalizedPlusQPositiveMulEquiv_apply,
    StableGL.originalIndependentPlusPositiveScalarMap_apply]
  exact hLeft.symm.trans (hValue.trans (hRight.trans hComp))

/-- The SAME original plus/Q inverse classes satisfy the inverse scalar
square at every positive index by their actual original inverse laws. -/
public theorem originalNormalizedPlusQPositiveScalarInverseNaturality (n : ℕ)
    (b : HomotopyGroup.Pi (n + 1)
      (BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max uR uMR} R))
      (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR uMR} R))) :
    (originalNormalizedPlusQPositiveMulEquiv.{uS, uMS, uNS} S n).symm
        (originalCanonicalQPositiveScalarMap.{uR, uS, uMR, uMS} f n b) =
      StableGL.originalIndependentPlusPositiveScalarMap f n
        ((originalNormalizedPlusQPositiveMulEquiv.{uR, uMR, uNR} R n).symm b) := by
  apply (originalNormalizedPlusQPositiveMulEquiv.{uS, uMS, uNS} S n).injective
  have h := originalNormalizedPlusQPositiveScalarNaturality.{uR, uS, uMR, uMS, uNR, uNS} f n
    ((originalNormalizedPlusQPositiveMulEquiv.{uR, uMR, uNR} R n).symm b)
  rw [MulEquiv.apply_symm_apply] at h
  exact ((originalNormalizedPlusQPositiveMulEquiv.{uS, uMS, uNS} S n).apply_symm_apply _).trans h

/-- Every inverse class follows the ORIGINAL Q/Core/native component return
and EXACT226 normalization forward map at both sides of the scalar square. -/
public theorem originalNormalizedPlusQPositiveScalarInverseClassValues (n : ℕ)
    (b : HomotopyGroup.Pi (n + 1)
      (BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max uR uMR} R))
      (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR uMR} R))) :
    StableGL.originalNativePlusPositiveMulEquiv.{uS, uMS, uNS} S n
        (originalQLoopsToNativeZeroPositiveMap.{uS, uMS, uNS} S n
          (originalCanonicalQPositiveScalarMap.{uR, uS, uMR, uMS} f n b)) =
      StableGL.originalIndependentPlusPositiveScalarMap f n
        (StableGL.originalNativePlusPositiveMulEquiv.{uR, uMR, uNR} R n
          (originalQLoopsToNativeZeroPositiveMap.{uR, uMR, uNR} R n b)) := by
  rw [← originalNormalizedPlusQPositiveMulEquiv_symm_apply,
    ← originalNormalizedPlusQPositiveMulEquiv_symm_apply]
  exact originalNormalizedPlusQPositiveScalarInverseNaturality.{uR, uS, uMR, uMS, uNR, uNS} f n b

private theorem originalNormalizedPositiveQNativeChart.{uR', uMR', uNR'}
    (R : Type uR') [Ring R] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (RingK0.projectiveZeroSpace.{uR', uMR', uNR'} R)
      (RingK0.projectiveZeroPoint.{uR', uMR', uNR'} R)) :
    originalNormalizedPlusQPositiveMulEquiv.{uR', uMR', uNR'} R n
        (StableGL.originalNativePlusPositiveMulEquiv.{uR', uMR', uNR'} R n a) =
      originalNativeZeroQPositiveMulEquiv.{uR', uMR', uNR'} R n a := by
  apply (originalNormalizedPlusQPositiveMulEquiv.{uR', uMR', uNR'} R n).symm.injective
  rw [MulEquiv.symm_apply_apply, originalNormalizedPlusQPositiveMulEquiv_symm_apply,
    ← originalNativeZeroQPositiveMulEquiv_symm_apply, MulEquiv.symm_apply_apply]

/-- Every ORIGINAL native/Q positive class square follows the complete
original normalization chart square and the actual canonical raw Q map. -/
public theorem originalNativeZeroQPositiveScalarNaturality (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (RingK0.projectiveZeroSpace.{uR, uMR, uNR} R)
      (RingK0.projectiveZeroPoint.{uR, uMR, uNR} R)) :
    originalCanonicalQPositiveScalarMap.{uR, uS, uMR, uMS} f n
        (originalNativeZeroQPositiveMulEquiv.{uR, uMR, uNR} R n a) =
      originalNativeZeroQPositiveMulEquiv.{uS, uMS, uNS} S n
        (StableGL.originalNativePositiveScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f n a) := by
  have h := originalNormalizedPlusQPositiveScalarNaturality.{uR, uS, uMR, uMS, uNR, uNS} f n
    (StableGL.originalNativePlusPositiveMulEquiv.{uR, uMR, uNR} R n a)
  have hChart := StableGL.originalNativePlusPositiveNaturality.{uR, uS, uMR, uMS, uNR, uNS} f n a
  rw [originalNormalizedPositiveQNativeChart, ← hChart] at h
  exact h.trans (originalNormalizedPositiveQNativeChart.{uS, uMS, uNS} S n
    (StableGL.originalNativePositiveScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f n a))

/-- The SAME original native/Q inverse families give the complete inverse
class scalar square in every positive degree. -/
public theorem originalNativeZeroQPositiveScalarInverseNaturality (n : ℕ)
    (b : HomotopyGroup.Pi (n + 1)
      (BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max uR uMR} R))
      (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR uMR} R))) :
    (originalNativeZeroQPositiveMulEquiv.{uS, uMS, uNS} S n).symm
        (originalCanonicalQPositiveScalarMap.{uR, uS, uMR, uMS} f n b) =
      StableGL.originalNativePositiveScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f n
        ((originalNativeZeroQPositiveMulEquiv.{uR, uMR, uNR} R n).symm b) := by
  apply (originalNativeZeroQPositiveMulEquiv.{uS, uMS, uNS} S n).injective
  have h := originalNativeZeroQPositiveScalarNaturality.{uR, uS, uMR, uMS, uNR, uNS} f n
    ((originalNativeZeroQPositiveMulEquiv.{uR, uMR, uNR} R n).symm b)
  rw [MulEquiv.apply_symm_apply] at h
  exact ((originalNativeZeroQPositiveMulEquiv.{uS, uMS, uNS} S n).apply_symm_apply _).trans h

/-- Every native inverse class uses the actual ORIGINAL Q/Core/native maps
and original component lift at both ends of the canonical scalar square. -/
public theorem originalNativeZeroQPositiveScalarInverseClassValues (n : ℕ)
    (b : HomotopyGroup.Pi (n + 1)
      (BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max uR uMR} R))
      (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR uMR} R))) :
    originalQLoopsToNativeZeroPositiveMap.{uS, uMS, uNS} S n
        (originalCanonicalQPositiveScalarMap.{uR, uS, uMR, uMS} f n b) =
      StableGL.originalNativePositiveScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f n
        (originalQLoopsToNativeZeroPositiveMap.{uR, uMR, uNR} R n b) := by
  rw [← originalNativeZeroQPositiveMulEquiv_symm_apply,
    ← originalNativeZeroQPositiveMulEquiv_symm_apply]
  exact originalNativeZeroQPositiveScalarInverseNaturality.{uR, uS, uMR, uMS, uNR, uNS} f n b

end AlgebraicKTheory.QuillenPlus

end


/-!
# Original BGL source and actual public classical K1

The original source-bearing BGL map is kept in every positive degree.
Mathlib's existing first-homotopy/fundamental-group dictionary connects the
original Q inverse classes to the actual original106 dictionaries. Their
scalar laws then use the already published canonical public K1.mapRingHom.
The original normalized op(g inverse) loop convention and both complete
normalization inverse families remain.
-/

noncomputable section

universe uR uS uMR uMS uNR uNS

universe uRawQX uRawQY

open CategoryTheory CategoryTheory.Limits
open AlgebraicKTheory.OriginalQZeroComparison
open scoped ContinuousMap Topology

namespace AlgebraicKTheory.QuillenPlus

private theorem originalScalarPiOneEquivMk
    {X : Type uRawQX} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 1) X x) :
    HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := x) (HomotopyGroup.mk p) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (genLoopEquivOfUnique (Fin 1) p)) :=
  rfl

private theorem originalScalarPiOneStrictMap
    {X : Type uRawQX} {Y : Type uRawQY} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : C(X, Y)) (hf : f x = y)
    (a : HomotopyGroup.Pi 1 X x) :
    HomotopyGroup.pi1MulEquivFundamentalGroup (X := Y) (x := y)
        (HomotopyGroup.mapHomOfEq f hf 0 a) =
      FundamentalGroup.mapOfEq f hf
        (HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := x) a) := by
  subst y
  obtain ⟨p, rfl⟩ := HomotopyGroup.mk_surjective a
  rw [HomotopyGroup.mapHomOfEq_apply, HomotopyGroup.map_mk,
    originalScalarPiOneEquivMk, originalScalarPiOneEquivMk]
  have h := FundamentalGroup.mapOfEq_apply f (rfl : f x = f x)
    (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (genLoopEquivOfUnique (Fin 1) p)))
  refine Eq.trans ?_ h.symm
  apply End.ext
  rfl

private theorem originalStrictPositiveMapCongr
    {X : Type uRawQX} {Y : Type uRawQY} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (n : ℕ) (f g : C(X, Y)) (h : f = g)
    (hf : f x = y) (hg : g x = y) (a : HomotopyGroup.Pi (n + 1) X x) :
    HomotopyGroup.mapHomOfEq f hf n a = HomotopyGroup.mapHomOfEq g hg n a := by
  cases h
  have hProof : hf = hg := Subsingleton.elim _ _
  cases hProof
  rfl

/-- In every positive degree, the genuine original BGL-source map is the
original plus/Q class comparison after its actual cell inclusion. -/
public theorem originalNormalizedPlusQPositive_sourceTriangle.{uR', uMR', uNR'}
    (R : Type uR') [Ring R] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (StableGL.ordinaryBGL R) (StableGL.ordinaryBGLBasepoint R)) :
    originalNormalizedPlusQPositiveMulEquiv.{uR', uMR', uNR'} R n
        (HomotopyGroup.mapHomOfEq (StableGL.independentBGLCellInclusion R).hom
          (StableGL.independentBGLCellInclusion_point R) n a) =
      HomotopyGroup.mapHomOfEq (originalNormalizedBGLToQLoopsSource.{uR', uMR', uNR'} R)
        (originalNormalizedBGLToQLoopsSource_point.{uR', uMR', uNR'} R) n a := by
  let I := (StableGL.independentBGLCellInclusion R).hom
  let Q := originalNormalizedPlusToQLoops.{uR', uMR', uNR'} R
  let hI := StableGL.independentBGLCellInclusion_point R
  let hQ := originalNormalizedPlusToQLoops_point.{uR', uMR', uNR'} R
  let hPoint := (congrArg Q hI).trans hQ
  have hComp := HomotopyGroup.mapHomOfEq_comp I Q hI hQ hPoint n a
  have hMaps := originalNormalizedPlusToQLoops_sourceTriangle.{uR', uMR', uNR'} R
  have hTransport := originalStrictPositiveMapCongr n (Q.comp I)
    (originalNormalizedBGLToQLoopsSource.{uR', uMR', uNR'} R) hMaps hPoint
    (originalNormalizedBGLToQLoopsSource_point.{uR', uMR', uNR'} R) a
  rw [originalNormalizedPlusQPositiveMulEquiv_apply]
  exact hComp.symm.trans hTransport

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
variable (f : R →+* S)

private theorem originalScalarPositiveBGLSourceSquare (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (StableGL.ordinaryBGL R) (StableGL.ordinaryBGLBasepoint R)) :
    StableGL.originalIndependentPlusPositiveScalarMap f n
        (HomotopyGroup.mapHomOfEq (StableGL.independentBGLCellInclusion R).hom
          (StableGL.independentBGLCellInclusion_point R) n a) =
      HomotopyGroup.mapHomOfEq (StableGL.independentBGLCellInclusion S).hom
        (StableGL.independentBGLCellInclusion_point S) n
        (HomotopyGroup.mapHomOfEq (StableGL.ordinaryBGLScalarMap f)
          (StableGL.ordinaryBGLScalarMap_point f) n a) := by
  let I := (StableGL.independentBGLCellInclusion R).hom
  let J := (StableGL.independentBGLCellInclusion S).hom
  let P := StableGL.independentBGLScalarPlusMap f
  let B := StableGL.ordinaryBGLScalarMap f
  let hI := StableGL.independentBGLCellInclusion_point R
  let hJ := StableGL.independentBGLCellInclusion_point S
  let hP := StableGL.independentBGLScalarPlusMap_point f
  let hB := StableGL.ordinaryBGLScalarMap_point f
  let hL := (congrArg P hI).trans hP
  let hR := (congrArg J hB).trans hJ
  have hFamily := HomotopyGroup.mapHomOfEq_homotopyRel n
    (P.comp I) (J.comp B) hL hR (StableGL.independentBGLScalarPlusMap_triangle f).some
  have hLeft := HomotopyGroup.mapHomOfEq_comp I P hI hP hL n a
  have hRight := HomotopyGroup.mapHomOfEq_comp B J hB hJ hR n a
  rw [StableGL.originalIndependentPlusPositiveScalarMap_apply]
  exact hLeft.symm.trans ((DFunLike.congr_fun hFamily a).trans hRight)

/-- The actual canonical raw Q scalar square retains the ORIGINAL BGL
source triangle at EVERY positive index, using the complete original17 family. -/
public theorem originalCanonicalQPositiveScalar_sourceTriangleNaturality (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (StableGL.ordinaryBGL R) (StableGL.ordinaryBGLBasepoint R)) :
    originalCanonicalQPositiveScalarMap.{uR, uS, uMR, uMS} f n
        (HomotopyGroup.mapHomOfEq (originalNormalizedBGLToQLoopsSource.{uR, uMR, uNR} R)
          (originalNormalizedBGLToQLoopsSource_point.{uR, uMR, uNR} R) n a) =
      HomotopyGroup.mapHomOfEq (originalNormalizedBGLToQLoopsSource.{uS, uMS, uNS} S)
        (originalNormalizedBGLToQLoopsSource_point.{uS, uMS, uNS} S) n
        (HomotopyGroup.mapHomOfEq (StableGL.ordinaryBGLScalarMap f)
          (StableGL.ordinaryBGLScalarMap_point f) n a) := by
  have h := originalNormalizedPlusQPositiveScalarNaturality.{uR, uS, uMR, uMS, uNR, uNS} f n
    (HomotopyGroup.mapHomOfEq (StableGL.independentBGLCellInclusion R).hom
      (StableGL.independentBGLCellInclusion_point R) n a)
  rw [originalNormalizedPlusQPositive_sourceTriangle] at h
  exact h.trans ((congrArg (originalNormalizedPlusQPositiveMulEquiv.{uS, uMS, uNS} S n)
    (originalScalarPositiveBGLSourceSquare f n a)).trans
      (originalNormalizedPlusQPositive_sourceTriangle.{uS, uMS, uNS} S n
        (HomotopyGroup.mapHomOfEq (StableGL.ordinaryBGLScalarMap f)
          (StableGL.ordinaryBGLScalarMap_point f) n a)))

/-- The ACTUAL original106 plus dictionary has its EVERY-pi1 scalar law
under the already published canonical arbitrary-universe public K1 map. -/
public theorem originalIndependentPlusPublicK1Naturality
    (p : FundamentalGroup (StableGL.independentBGLCellTarget R) (StableGL.independentBGLCellPoint
        R)) :
    StableGL.originalIndependentPlusK1Equiv S
        (Additive.ofMul (FundamentalGroup.mapOfEq (StableGL.independentBGLScalarPlusMap f)
          (StableGL.independentBGLScalarPlusMap_point f) p)) =
      K1.mapRingHom f (StableGL.originalIndependentPlusK1Equiv R (Additive.ofMul p)) :=
  StableGL.originalIndependentPlusK1Naturality f p

/-- The ACTUAL original106 native dictionary has its full scalar law under
the canonical public K1 map, with ALL SIX original universe roles retained. -/
public theorem originalNativePublicK1Naturality
    (p : FundamentalGroup (RingK0.projectiveZeroSpace.{uR, uMR, uNR} R)
      (RingK0.projectiveZeroPoint.{uR, uMR, uNR} R)) :
    StableGL.originalNativeK1Equiv.{uS, uMS, uNS} S
        (Additive.ofMul (FundamentalGroup.mapOfEq
          (StableGL.nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f)
          (StableGL.nativeProjectiveZeroScalarMap_point.{uR, uS, uMR, uMS, uNR, uNS} f) p)) =
      K1.mapRingHom f (StableGL.originalNativeK1Equiv.{uR, uMR, uNR} R (Additive.ofMul p)) :=
  StableGL.originalNativeK1Naturality.{uR, uS, uMR, uMS, uNR, uNS} f p

/-- EVERY original raw Q pi1 class specializes the exact original positive
inverse square to the native plus dictionary and public canonical K1 map. -/
public theorem originalRawQPublicK1Naturality
    (a : HomotopyGroup.Pi 1
      (BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max uR uMR} R))
      (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR uMR} R))) :
    StableGL.originalIndependentPlusK1Equiv S
        (Additive.ofMul (HomotopyGroup.pi1MulEquivFundamentalGroup
          (X := StableGL.independentBGLCellTarget S) (x := StableGL.independentBGLCellPoint S)
          ((originalNormalizedPlusQPositiveMulEquiv.{uS, uMS, uNS} S 0).symm
            (originalCanonicalQPositiveScalarMap.{uR, uS, uMR, uMS} f 0 a)))) =
      K1.mapRingHom f (StableGL.originalIndependentPlusK1Equiv R
        (Additive.ofMul (HomotopyGroup.pi1MulEquivFundamentalGroup
          (X := StableGL.independentBGLCellTarget R) (x := StableGL.independentBGLCellPoint R)
          ((originalNormalizedPlusQPositiveMulEquiv.{uR, uMR, uNR} R 0).symm a)))) := by
  let c := (originalNormalizedPlusQPositiveMulEquiv.{uR, uMR, uNR} R 0).symm a
  let ER := HomotopyGroup.pi1MulEquivFundamentalGroup
    (X := StableGL.independentBGLCellTarget R) (x := StableGL.independentBGLCellPoint R)
  let ES := HomotopyGroup.pi1MulEquivFundamentalGroup
    (X := StableGL.independentBGLCellTarget S) (x := StableGL.independentBGLCellPoint S)
  have hClass := originalNormalizedPlusQPositiveScalarInverseNaturality.{uR, uS, uMR, uMS, uNR, uNS}
    f 0 a
  have hMap := (congrArg ES (StableGL.originalIndependentPlusPositiveScalarMap_apply f 0 c)).trans
    (originalScalarPiOneStrictMap (StableGL.independentBGLScalarPlusMap f)
      (StableGL.independentBGLScalarPlusMap_point f) c)
  exact (congrArg (fun b => StableGL.originalIndependentPlusK1Equiv S (Additive.ofMul (ES b)))
    hClass).trans ((congrArg (fun p => StableGL.originalIndependentPlusK1Equiv S (Additive.ofMul p))
      hMap).trans (originalIndependentPlusPublicK1Naturality f (ER c)))

/-- EVERY raw Q pi1 class also follows the ORIGINAL164 native return and
native dictionary to the same canonical public classical K1 map. -/
public theorem originalRawQNativePublicK1Naturality
    (a : HomotopyGroup.Pi 1
      (BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max uR uMR} R))
      (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR uMR} R))) :
    StableGL.originalNativeK1Equiv.{uS, uMS, uNS} S
        (Additive.ofMul (HomotopyGroup.pi1MulEquivFundamentalGroup
          (X := RingK0.projectiveZeroSpace.{uS, uMS, uNS} S)
          (x := RingK0.projectiveZeroPoint.{uS, uMS, uNS} S)
          ((originalNativeZeroQPositiveMulEquiv.{uS, uMS, uNS} S 0).symm
            (originalCanonicalQPositiveScalarMap.{uR, uS, uMR, uMS} f 0 a)))) =
      K1.mapRingHom f (StableGL.originalNativeK1Equiv.{uR, uMR, uNR} R
        (Additive.ofMul (HomotopyGroup.pi1MulEquivFundamentalGroup
          (X := RingK0.projectiveZeroSpace.{uR, uMR, uNR} R)
          (x := RingK0.projectiveZeroPoint.{uR, uMR, uNR} R)
          ((originalNativeZeroQPositiveMulEquiv.{uR, uMR, uNR} R 0).symm a)))) := by
  let c := (originalNativeZeroQPositiveMulEquiv.{uR, uMR, uNR} R 0).symm a
  let ER := HomotopyGroup.pi1MulEquivFundamentalGroup
    (X := RingK0.projectiveZeroSpace.{uR, uMR, uNR} R)
    (x := RingK0.projectiveZeroPoint.{uR, uMR, uNR} R)
  let ES := HomotopyGroup.pi1MulEquivFundamentalGroup
    (X := RingK0.projectiveZeroSpace.{uS, uMS, uNS} S)
    (x := RingK0.projectiveZeroPoint.{uS, uMS, uNS} S)
  have hClass := originalNativeZeroQPositiveScalarInverseNaturality.{uR, uS, uMR, uMS, uNR, uNS}
    f 0 a
  have hMap := (congrArg ES
    (StableGL.originalNativePositiveScalarMap_apply.{uR, uS, uMR, uMS, uNR, uNS} f 0 c)).trans
      (originalScalarPiOneStrictMap
        (StableGL.nativeProjectiveZeroScalarMap.{uR, uS, uMR, uMS, uNR, uNS} f)
        (StableGL.nativeProjectiveZeroScalarMap_point.{uR, uS, uMR, uMS, uNR, uNS} f) c)
  exact (congrArg (fun b => StableGL.originalNativeK1Equiv.{uS, uMS, uNS} S
    (Additive.ofMul (ES b))) hClass).trans
      ((congrArg (fun p => StableGL.originalNativeK1Equiv.{uS, uMS, uNS} S (Additive.ofMul p))
        hMap).trans (originalNativePublicK1Naturality.{uR, uS, uMR, uMS, uNR, uNS} f (ER c)))

private theorem originalNormalizedBGLQPlusFundamentalValue.{uR', uMR', uNR'}
    (R : Type uR') [Ring R] (g : StableGL R) :
    HomotopyGroup.pi1MulEquivFundamentalGroup
        (X := StableGL.independentBGLCellTarget R) (x := StableGL.independentBGLCellPoint R)
        ((originalNormalizedPlusQPositiveMulEquiv.{uR', uMR', uNR'} R 0).symm
          (HomotopyGroup.mapHomOfEq (originalNormalizedBGLToQLoopsSource.{uR', uMR', uNR'} R)
            (originalNormalizedBGLToQLoopsSource_point.{uR', uMR', uNR'} R) 0
            ((HomotopyGroup.pi1MulEquivFundamentalGroup
              (X := StableGL.ordinaryBGL R) (x := StableGL.ordinaryBGLBasepoint R)).symm
                (FundamentalGroup.fromPath
                  (Path.Homotopic.Quotient.mk (StableGL.ordinaryBGLLoop g)))))) =
      FundamentalGroup.mapOfEq (StableGL.independentBGLCellInclusion R).hom
        (StableGL.independentBGLCellInclusion_point R)
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (StableGL.ordinaryBGLLoop g))) := by
  let a := (HomotopyGroup.pi1MulEquivFundamentalGroup
    (X := StableGL.ordinaryBGL R) (x := StableGL.ordinaryBGLBasepoint R)).symm
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (StableGL.ordinaryBGLLoop g)))
  let E := originalNormalizedPlusQPositiveMulEquiv.{uR', uMR', uNR'} R 0
  let P := HomotopyGroup.pi1MulEquivFundamentalGroup
    (X := StableGL.independentBGLCellTarget R) (x := StableGL.independentBGLCellPoint R)
  have hTriangle := originalNormalizedPlusQPositive_sourceTriangle.{uR', uMR', uNR'} R 0 a
  have hInverse : E.symm
      (HomotopyGroup.mapHomOfEq (originalNormalizedBGLToQLoopsSource.{uR', uMR', uNR'} R)
        (originalNormalizedBGLToQLoopsSource_point.{uR', uMR', uNR'} R) 0 a) =
      HomotopyGroup.mapHomOfEq (StableGL.independentBGLCellInclusion R).hom
        (StableGL.independentBGLCellInclusion_point R) 0 a := by
    apply E.injective
    exact (E.apply_symm_apply _).trans hTriangle.symm
  have hPi := originalScalarPiOneStrictMap (StableGL.independentBGLCellInclusion R).hom
    (StableGL.independentBGLCellInclusion_point R) a
  exact (congrArg P hInverse).trans (hPi.trans
    (congrArg (FundamentalGroup.mapOfEq (StableGL.independentBGLCellInclusion R).hom
      (StableGL.independentBGLCellInclusion_point R))
      ((HomotopyGroup.pi1MulEquivFundamentalGroup
        (X := StableGL.ordinaryBGL R) (x := StableGL.ordinaryBGLBasepoint R)).apply_symm_apply _)))

/-- The actual original BGL-source class of the normalized op(g inverse)
loop evaluates through the ORIGINAL Q inverse and106 dictionary to K1.proj g. -/
public theorem originalNormalizedBGLQPublicK1_loop.{uR', uMR', uNR'}
    (R : Type uR') [Ring R] (g : StableGL R) :
    StableGL.originalIndependentPlusK1Equiv R
        (Additive.ofMul (HomotopyGroup.pi1MulEquivFundamentalGroup
          (X := StableGL.independentBGLCellTarget R) (x := StableGL.independentBGLCellPoint R)
          ((originalNormalizedPlusQPositiveMulEquiv.{uR', uMR', uNR'} R 0).symm
            (HomotopyGroup.mapHomOfEq (originalNormalizedBGLToQLoopsSource.{uR', uMR', uNR'} R)
              (originalNormalizedBGLToQLoopsSource_point.{uR', uMR', uNR'} R) 0
              ((HomotopyGroup.pi1MulEquivFundamentalGroup
                (X := StableGL.ordinaryBGL R) (x := StableGL.ordinaryBGLBasepoint R)).symm
                  (FundamentalGroup.fromPath
                    (Path.Homotopic.Quotient.mk (StableGL.ordinaryBGLLoop g)))))))) =
      K1.proj g :=
  (congrArg (fun p => StableGL.originalIndependentPlusK1Equiv R (Additive.ofMul p))
    (originalNormalizedBGLQPlusFundamentalValue.{uR', uMR', uNR'} R g)).trans
      (StableGL.originalIndependentPlusK1Equiv_loop R g)

/-- The ACTUAL original BGL-source normalized loop specializes the raw Q
scalar square to the already published canonical public classical K1 map. -/
public theorem originalNormalizedBGLQPublicK1_scalarLoop (g : StableGL R) :
    StableGL.originalIndependentPlusK1Equiv S
        (Additive.ofMul (HomotopyGroup.pi1MulEquivFundamentalGroup
          (X := StableGL.independentBGLCellTarget S) (x := StableGL.independentBGLCellPoint S)
          ((originalNormalizedPlusQPositiveMulEquiv.{uS, uMS, uNS} S 0).symm
            (originalCanonicalQPositiveScalarMap.{uR, uS, uMR, uMS} f 0
              (HomotopyGroup.mapHomOfEq (originalNormalizedBGLToQLoopsSource.{uR, uMR, uNR} R)
                (originalNormalizedBGLToQLoopsSource_point.{uR, uMR, uNR} R) 0
                ((HomotopyGroup.pi1MulEquivFundamentalGroup
                  (X := StableGL.ordinaryBGL R) (x := StableGL.ordinaryBGLBasepoint R)).symm
                    (FundamentalGroup.fromPath
                      (Path.Homotopic.Quotient.mk (StableGL.ordinaryBGLLoop g))))))))) =
      K1.mapRingHom f (K1.proj g) :=
  (originalRawQPublicK1Naturality.{uR, uS, uMR, uMS, uNR, uNS} f
    (HomotopyGroup.mapHomOfEq (originalNormalizedBGLToQLoopsSource.{uR, uMR, uNR} R)
      (originalNormalizedBGLToQLoopsSource_point.{uR, uMR, uNR} R) 0
      ((HomotopyGroup.pi1MulEquivFundamentalGroup
        (X := StableGL.ordinaryBGL R) (x := StableGL.ordinaryBGLBasepoint R)).symm
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (StableGL.ordinaryBGLLoop
              g)))))).trans
            (congrArg (K1.mapRingHom f) (originalNormalizedBGLQPublicK1_loop.{uR, uMR, uNR} R g))

end AlgebraicKTheory.QuillenPlus

end


/-!
# Every original raw Q component and the full original universe transport

The actual quotient map of the same canonical raw Q scalar map is compared
with the complete original146 transport family. Its canonical K0 evaluator
commutes on every component with actual scalar extension. Both original raw
and NQ component inverse programs and their complete relative families are
kept with all original category and native-carrier parameters.
-/

noncomputable section

universe uR uS uMR uMS uNR uNS

open CategoryTheory CategoryTheory.Limits
open AlgebraicKTheory.QuillenMixedUniverseTransport
open AlgebraicKTheory.OriginalQuillenUnliftedTransport
open scoped ContinuousMap Topology

attribute [local instance] CategoryTheory.ExactCategory.waldhausenCategory
attribute [local instance] AlgebraicKTheory.StableGL.nativeProjectiveZeroScalarFunctor_additive
attribute [local instance] AlgebraicKTheory.StableGL.nativeProjectiveZeroScalarFunctor_isExact

universe uQComponentModule uQComponentObject uQComponentHom uQComponentNative

namespace AlgebraicKTheory.QuillenPlus

/-- BOTH actual original NQ component directions are inverse on EVERY
component through their SAME145 complete original inverse families. -/
public theorem originalScalarNQComponentInverseLaws.{uR', uQComponentModule',
    uQComponentObject', uQComponentHom', uQComponentNative'}
    (R : Type uR') [Ring R] :
    (∀ c : ZerothHomotopy (NQKSpace
      (QuillenUniverseLift.liftedCategory.{uR', uQComponentModule', uQComponentObject',
          uQComponentHom'} R)),
      originalUnliftedNQupComponents.{uR', uQComponentModule', uQComponentObject', uQComponentHom',
        uQComponentNative'} R
        (originalUnliftedNQdownComponents.{uR', uQComponentModule', uQComponentObject',
            uQComponentHom',
          uQComponentNative'} R c) = c) ∧
    (∀ c : ZerothHomotopy (NQKSpace (QuillenUniverseLift.canonicalCategory.{uR', uQComponentModule'}
        R)),
      originalUnliftedNQdownComponents.{uR', uQComponentModule', uQComponentObject',
          uQComponentHom',
        uQComponentNative'} R
        (originalUnliftedNQupComponents.{uR', uQComponentModule', uQComponentObject',
            uQComponentHom',
          uQComponentNative'} R c) = c) := by
  constructor
  · intro c
    induction c using ZerothHomotopy.rec with
    | mk p =>
      rw [originalUnliftedNQdownComponents_value, originalUnliftedNQupComponents_value]
      exact ZerothHomotopy.sound
        ((originalUnliftedNQleftFamily.{uR', uQComponentModule', uQComponentObject',
            uQComponentHom',
          uQComponentNative'} R).toHomotopy.evalAt p)
  · intro c
    induction c using ZerothHomotopy.rec with
    | mk p =>
      rw [originalUnliftedNQupComponents_value, originalUnliftedNQdownComponents_value]
      exact ZerothHomotopy.sound
        ((originalUnliftedNQrightFamily.{uR', uQComponentModule', uQComponentObject',
            uQComponentHom',
          uQComponentNative'} R).toHomotopy.evalAt p)

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
variable (f : R →+* S)

/-- The ACTUAL component map is the quotient map of SAME210 raw canonical
Q conjugation, on the entire original raw loop carrier. -/
public def originalCanonicalQScalarComponents :
    ZerothHomotopy (BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max uR uMR} R)) →
      ZerothHomotopy (BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max uS uMS} S)) :=
  ZerothHomotopy.lift
    (fun p => ZerothHomotopy.mk (originalCanonicalQLoopScalarMap.{uR, uS, uMR, uMS} f p))
    (fun {_ _} path => ZerothHomotopy.sound
      (path.map (originalCanonicalQLoopScalarMap.{uR, uS, uMR, uMS} f).continuous))

private theorem originalCanonicalQScalarComponentsMkComputed
    (p : BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max uR uMR} R)) :
    originalCanonicalQScalarComponents.{uR, uS, uMR, uMS} f (ZerothHomotopy.mk p) =
      ZerothHomotopy.mk (originalCanonicalQLoopScalarMap.{uR, uS, uMR, uMS} f p) := rfl

/-- Every original raw Q component representative uses the actual SAME map. -/
public theorem originalCanonicalQScalarComponents_mk
    (p : BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max uR uMR} R)) :
    originalCanonicalQScalarComponents.{uR, uS, uMR, uMS} f (ZerothHomotopy.mk p) =
      ZerothHomotopy.mk (originalCanonicalQLoopScalarMap.{uR, uS, uMR, uMS} f p) :=
  originalCanonicalQScalarComponentsMkComputed f p

/-- The full original146 up/working/down family is transported through
BOTH145 point charts on ALL raw loops and all SIX independent roles. -/
public def originalCanonicalQScalarRawTransportHomotopy :
    ContinuousMap.Homotopy
      (originalCanonicalQLoopScalarMap.{uR, uS, uMR, uMS} f)
      ((originalNQLoopPointHomeomorph (FGProjectiveCat.{max uS uMS} S)).toHomotopyEquiv.toFun.comp
        ((originalUnliftedNQdown.{uS, uMS,
          max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
          max (max uR uMR) (max uS uMS) uNR uNS, uNS} S).comp
          ((mixedNQKSpaceMap
            (StableGL.mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f)).comp
            ((originalUnliftedNQup.{uR, uMR,
              max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
              max (max uR uMR) (max uS uMS) uNR uNS, uNR} R).comp
              (originalNQLoopPointHomeomorph
                (FGProjectiveCat.{max uR uMR} R)).symm.toHomotopyEquiv.toFun)))) := by
  let eR := originalNQLoopPointHomeomorph (FGProjectiveCat.{max uR uMR} R)
  let eS := originalNQLoopPointHomeomorph (FGProjectiveCat.{max uS uMS} S)
  let H := (ContinuousMap.Homotopy.refl eS.toHomotopyEquiv.toFun).comp
    ((StableGL.mixedOriginalQScalarLoopTransportHomotopy.{uR, uS, uMR, uMS, uNR, uNS}
        f).compContinuousMap
      eR.symm.toHomotopyEquiv.toFun)
  refine H.cast ?_ ?_
  · apply ContinuousMap.ext
    intro p
    rfl
  · apply ContinuousMap.ext
    intro p
    rfl

/-- The original scalar map has BOTH its actual SIX-role whole transport
and canonical fixed RingK0 naturality on EVERY original raw Q component. -/
public theorem originalCanonicalQEveryComponentK0Naturality :
    Nonempty (ContinuousMap.Homotopy
      (originalCanonicalQLoopScalarMap.{uR, uS, uMR, uMS} f)
      ((originalNQLoopPointHomeomorph (FGProjectiveCat.{max uS uMS} S)).toHomotopyEquiv.toFun.comp
        ((originalUnliftedNQdown.{uS, uMS,
          max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
          max (max uR uMR) (max uS uMS) uNR uNS, uNS} S).comp
          ((mixedNQKSpaceMap
            (StableGL.mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f)).comp
            ((originalUnliftedNQup.{uR, uMR,
              max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
              max (max uR uMR) (max uS uMS) uNR uNS, uNR} R).comp
              (originalNQLoopPointHomeomorph
                (FGProjectiveCat.{max uR uMR} R)).symm.toHomotopyEquiv.toFun))))) ∧
    (∀ c : ZerothHomotopy
      (BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max uR uMR} R)),
      RingK0.projectiveUniverseEquiv.{uS, uMS} S
        (OriginalQK0Comparison.canonicalLoopComponentsK0 (C := FGProjectiveCat.{max uS uMS} S)
          (originalCanonicalQScalarComponents.{uR, uS, uMR, uMS} f c)) =
      FGProjectiveCat.scalarExtensionK0.{uR, uS} f
        (RingK0.projectiveUniverseEquiv.{uR, uMR} R
          (OriginalQK0Comparison.canonicalLoopComponentsK0 (C := FGProjectiveCat.{max uR uMR} R)
              c))) := by
  refine ⟨⟨originalCanonicalQScalarRawTransportHomotopy.{uR, uS, uMR, uMS, uNR, uNS} f⟩, ?_⟩
  intro c
  induction c using ZerothHomotopy.rec with
  | mk gamma =>
    let CR := FGProjectiveCat.{max uR uMR} R
    let CS := FGProjectiveCat.{max uS uMS} S
    let eR := originalNQLoopPointHomeomorph CR
    let p := eR.symm gamma
    let F := StableGL.nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f
    have hSource : StableGL.originalQProjectiveComponentsK0.{uR, uMR} R (ZerothHomotopy.mk p) =
        RingK0.projectiveUniverseEquiv.{uR, uMR} R
          (OriginalQK0Comparison.canonicalLoopComponentsK0 (C := CR) (ZerothHomotopy.mk gamma)) :=
      (StableGL.originalQProjectiveComponentsK0_loop.{uR, uMR} R p).trans
        (congrArg (fun q : BasedSplitExactQLoop.originalQLoops (C := CR) =>
          RingK0.projectiveUniverseEquiv.{uR, uMR} R
            (OriginalQK0Comparison.canonicalLoopComponentsK0 (C := CR) (ZerothHomotopy.mk q)))
          (eR.apply_symm_apply gamma))
    have hTarget : StableGL.originalQProjectiveComponentsK0.{uS, uMS} S
        (ZerothHomotopy.mk (mixedNQKSpaceMap F p)) =
        RingK0.projectiveUniverseEquiv.{uS, uMS} S
          (OriginalQK0Comparison.canonicalLoopComponentsK0 (C := CS)
            (ZerothHomotopy.mk (originalCanonicalQLoopScalarMap.{uR, uS, uMR, uMS} f gamma))) :=
      StableGL.originalQProjectiveComponentsK0_loop.{uS, uMS} S (mixedNQKSpaceMap F p)
    have hCanonical :=
      (StableGL.mixedOriginalQEveryComponentK0Naturality.{uR, uS, uMR, uMS, uNR, uNS} f).2.2
        (ZerothHomotopy.mk p)
    rw [mixedNQKSpacePiZeroMap_mk] at hCanonical
    rw [originalCanonicalQScalarComponents_mk]
    exact hTarget.symm.trans (hCanonical.trans
      (congrArg (FGProjectiveCat.scalarExtensionK0.{uR, uS} f) hSource))

/-- BOTH original NQ inverse component programs retain their ENTIRE
original left/right families and every-time roots in both ring worlds. -/
public theorem originalCanonicalQScalarUniverseInverseFamilies (t : unitInterval) :
    (let A := QuillenUniverseLift.liftedCategory.{uR, uMR,
        max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
        max (max uR uMR) (max uS uMS) uNR uNS} R
     let C := QuillenUniverseLift.canonicalCategory.{uR, uMR} R
     (∀ c : ZerothHomotopy (NQKSpace A),
       originalUnliftedNQupComponents.{uR, uMR,
         max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
         max (max uR uMR) (max uS uMS) uNR uNS, uNR} R
         (originalUnliftedNQdownComponents.{uR, uMR,
           max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
           max (max uR uMR) (max uS uMS) uNR uNS, uNR} R c) = c) ∧
     (∀ c : ZerothHomotopy (NQKSpace C),
       originalUnliftedNQdownComponents.{uR, uMR,
         max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
         max (max uR uMR) (max uS uMS) uNR uNS, uNR} R
         (originalUnliftedNQupComponents.{uR, uMR,
           max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
           max (max uR uMR) (max uS uMS) uNR uNS, uNR} R c) = c)) ∧
    (let A := QuillenUniverseLift.liftedCategory.{uS, uMS,
        max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
        max (max uR uMR) (max uS uMS) uNR uNS} S
     let C := QuillenUniverseLift.canonicalCategory.{uS, uMS} S
     (∀ c : ZerothHomotopy (NQKSpace A),
       originalUnliftedNQupComponents.{uS, uMS,
         max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
         max (max uR uMR) (max uS uMS) uNR uNS, uNS} S
         (originalUnliftedNQdownComponents.{uS, uMS,
           max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
           max (max uR uMR) (max uS uMS) uNR uNS, uNS} S c) = c) ∧
     (∀ c : ZerothHomotopy (NQKSpace C),
       originalUnliftedNQdownComponents.{uS, uMS,
         max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
         max (max uR uMR) (max uS uMS) uNR uNS, uNS} S
         (originalUnliftedNQupComponents.{uS, uMS,
           max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
           max (max uR uMR) (max uS uMS) uNR uNS, uNS} S c) = c)) ∧
    (originalUnliftedNQleftFamily.{uR, uMR,
      max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
      max (max uR uMR) (max uS uMS) uNR uNS, uNR} R
      (t, Path.refl (NQReal.basepoint
        (QuillenUniverseLift.liftedCategory.{uR, uMR,
          max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
          max (max uR uMR) (max uS uMS) uNR uNS} R))) =
        Path.refl (NQReal.basepoint (QuillenUniverseLift.liftedCategory.{uR, uMR,
          max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
          max (max uR uMR) (max uS uMS) uNR uNS} R))) ∧
    (originalUnliftedNQrightFamily.{uR, uMR,
      max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
      max (max uR uMR) (max uS uMS) uNR uNS, uNR} R
      (t, Path.refl (NQReal.basepoint (QuillenUniverseLift.canonicalCategory.{uR, uMR} R))) =
        Path.refl (NQReal.basepoint (QuillenUniverseLift.canonicalCategory.{uR, uMR} R))) ∧
    (originalUnliftedNQleftFamily.{uS, uMS,
      max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
      max (max uR uMR) (max uS uMS) uNR uNS, uNS} S
      (t, Path.refl (NQReal.basepoint (QuillenUniverseLift.liftedCategory.{uS, uMS,
        max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
        max (max uR uMR) (max uS uMS) uNR uNS} S))) =
        Path.refl (NQReal.basepoint (QuillenUniverseLift.liftedCategory.{uS, uMS,
          max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
          max (max uR uMR) (max uS uMS) uNR uNS} S))) ∧
    (originalUnliftedNQrightFamily.{uS, uMS,
      max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
      max (max uR uMR) (max uS uMS) uNR uNS, uNS} S
      (t, Path.refl (NQReal.basepoint (QuillenUniverseLift.canonicalCategory.{uS, uMS} S))) =
        Path.refl (NQReal.basepoint (QuillenUniverseLift.canonicalCategory.{uS, uMS} S))) :=
  ⟨originalScalarNQComponentInverseLaws.{uR, uMR,
      max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
      max (max uR uMR) (max uS uMS) uNR uNS, uNR} R,
    originalScalarNQComponentInverseLaws.{uS, uMS,
      max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
      max (max uR uMR) (max uS uMS) uNR uNS, uNS} S,
    (originalUnliftedNQfamily_roots.{uR, uMR,
      max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
      max (max uR uMR) (max uS uMS) uNR uNS, uNR} R t).1,
    (originalUnliftedNQfamily_roots.{uR, uMR,
      max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
      max (max uR uMR) (max uS uMS) uNR uNS, uNR} R t).2,
    (originalUnliftedNQfamily_roots.{uS, uMS,
      max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
      max (max uR uMR) (max uS uMS) uNR uNS, uNS} S t).1,
    (originalUnliftedNQfamily_roots.{uS, uMS,
      max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
      max (max uR uMR) (max uS uMS) uNR uNS, uNS} S t).2⟩

/-- The actual original raw Q component inverses, native and Q whole
inverse families, and BOTH literal carrier descent/inclusion charts retain
all original parameters and every-time constant-loop roots. -/
public theorem originalRawQNativeCarrierInverseFamilies.{uR', uQComponentModule',
    uQComponentObject', uQComponentHom', uQComponentNative'}
    (R : Type uR') [Ring R] (t : unitInterval) :
    (∀ c : ZerothHomotopy (QuillenUniverseLift.originalLoops.{uR', uQComponentModule',
      uQComponentObject', uQComponentHom'} R),
      originalUnliftedQupComponents.{uR', uQComponentModule', uQComponentObject', uQComponentHom',
        uQComponentNative'} R
        (originalUnliftedQdownComponents.{uR', uQComponentModule', uQComponentObject',
            uQComponentHom',
          uQComponentNative'} R c) = c) ∧
    (∀ c : ZerothHomotopy (QuillenUniverseLift.canonicalLoops.{uR', uQComponentModule'} R),
      originalUnliftedQdownComponents.{uR', uQComponentModule', uQComponentObject', uQComponentHom',
        uQComponentNative'} R
        (originalUnliftedQupComponents.{uR', uQComponentModule', uQComponentObject',
            uQComponentHom',
          uQComponentNative'} R c) = c) ∧
    (originalUnliftedQleftFamily.{uR', uQComponentModule', uQComponentObject', uQComponentHom',
      uQComponentNative'} R
      (t, QuillenUniverseLift.originalConstantLoop.{uR', uQComponentModule',
        uQComponentObject', uQComponentHom'} R) =
      QuillenUniverseLift.originalConstantLoop.{uR', uQComponentModule',
        uQComponentObject', uQComponentHom'} R) ∧
    (originalUnliftedQrightFamily.{uR', uQComponentModule', uQComponentObject', uQComponentHom',
      uQComponentNative'} R (t, QuillenUniverseLift.canonicalConstantLoop.{uR', uQComponentModule'}
          R) =
      QuillenUniverseLift.canonicalConstantLoop.{uR', uQComponentModule'} R) ∧
    (QuillenUniverseLift.nativeLoopLeftHomotopyRel.{uR', uQComponentModule',
      uQComponentObject', uQComponentHom', uQComponentNative'} R
      (t, QuillenUniverseLift.nativeConstantLoop.{uR', uQComponentModule',
        uQComponentObject', uQComponentHom', uQComponentNative'} R) =
      QuillenUniverseLift.nativeConstantLoop.{uR', uQComponentModule',
        uQComponentObject', uQComponentHom', uQComponentNative'} R) ∧
    (QuillenUniverseLift.nativeLoopRightHomotopyRel.{uR', uQComponentModule',
      uQComponentObject', uQComponentHom', uQComponentNative'} R
      (t, QuillenUniverseLift.nativeCanonicalConstantLoop.{uR', uQComponentModule',
        uQComponentObject', uQComponentHom', uQComponentNative'} R) =
      QuillenUniverseLift.nativeCanonicalConstantLoop.{uR', uQComponentModule',
        uQComponentObject', uQComponentHom', uQComponentNative'} R) ∧
    (QuillenUniverseLift.QleftHomotopyRel.{uR', uQComponentModule',
      uQComponentObject', uQComponentHom', uQComponentNative'} R
      (t, QuillenUniverseLift.nativeConstantLoop.{uR', uQComponentModule',
        uQComponentObject', uQComponentHom', uQComponentNative'} R) =
      QuillenUniverseLift.nativeConstantLoop.{uR', uQComponentModule',
        uQComponentObject', uQComponentHom', uQComponentNative'} R) ∧
    (QuillenUniverseLift.QrightHomotopyRel.{uR', uQComponentModule',
      uQComponentObject', uQComponentHom', uQComponentNative'} R
      (t, QuillenUniverseLift.canonicalConstantLoop.{uR', uQComponentModule'} R) =
      QuillenUniverseLift.canonicalConstantLoop.{uR', uQComponentModule'} R) ∧
    ((QuillenUniverseLift.rawNativeCarrierUp.{uR', uQComponentModule',
      uQComponentObject', uQComponentHom', uQComponentNative'} R).comp
      (QuillenUniverseLift.rawNativeCarrierDown.{uR', uQComponentModule',
        uQComponentObject', uQComponentHom', uQComponentNative'} R) =
      ContinuousMap.id (QuillenUniverseLift.nativeRawLoopSpace.{uR', uQComponentModule',
        uQComponentObject', uQComponentHom', uQComponentNative'} R)) ∧
    ((QuillenUniverseLift.rawNativeCarrierDown.{uR', uQComponentModule',
      uQComponentObject', uQComponentHom', uQComponentNative'} R).comp
      (QuillenUniverseLift.rawNativeCarrierUp.{uR', uQComponentModule',
        uQComponentObject', uQComponentHom', uQComponentNative'} R) =
      ContinuousMap.id (QuillenUniverseLift.originalLoops.{uR', uQComponentModule',
        uQComponentObject', uQComponentHom'} R)) ∧
    ((QuillenUniverseLift.canonicalCarrierUp.{uR', uQComponentModule',
      uQComponentObject', uQComponentHom', uQComponentNative'} R).comp
      (QuillenUniverseLift.canonicalCarrierDown.{uR', uQComponentModule',
        uQComponentObject', uQComponentHom', uQComponentNative'} R) =
      ContinuousMap.id (QuillenUniverseLift.nativeCanonicalLoopSpace.{uR', uQComponentModule',
        uQComponentObject', uQComponentHom', uQComponentNative'} R)) ∧
    ((QuillenUniverseLift.canonicalCarrierDown.{uR', uQComponentModule',
      uQComponentObject', uQComponentHom', uQComponentNative'} R).comp
      (QuillenUniverseLift.canonicalCarrierUp.{uR', uQComponentModule',
        uQComponentObject', uQComponentHom', uQComponentNative'} R) =
      ContinuousMap.id (QuillenUniverseLift.canonicalLoops.{uR', uQComponentModule'} R)) :=
  ⟨(originalUnliftedQcomponent_inverse_laws.{uR', uQComponentModule',
      uQComponentObject', uQComponentHom', uQComponentNative'} R).1,
    (originalUnliftedQcomponent_inverse_laws.{uR', uQComponentModule',
      uQComponentObject', uQComponentHom', uQComponentNative'} R).2,
    (originalUnliftedQfamily_roots.{uR', uQComponentModule',
      uQComponentObject', uQComponentHom', uQComponentNative'} R t).1,
    (originalUnliftedQfamily_roots.{uR', uQComponentModule',
      uQComponentObject', uQComponentHom', uQComponentNative'} R t).2,
    (QuillenUniverseLift.nativeLoopLeftHomotopyRel.{uR', uQComponentModule',
      uQComponentObject', uQComponentHom', uQComponentNative'} R).eq_snd t (by rfl),
    (QuillenUniverseLift.nativeLoopRightHomotopyRel.{uR', uQComponentModule',
      uQComponentObject', uQComponentHom', uQComponentNative'} R).eq_snd t (by rfl),
    (QuillenUniverseLift.QleftHomotopyRel.{uR', uQComponentModule',
      uQComponentObject', uQComponentHom', uQComponentNative'} R).eq_snd t (by rfl),
    (QuillenUniverseLift.QrightHomotopyRel.{uR', uQComponentModule',
      uQComponentObject', uQComponentHom', uQComponentNative'} R).eq_snd t (by rfl),
    QuillenUniverseLift.rawNativeCarrierUp_comp_down.{uR', uQComponentModule',
      uQComponentObject', uQComponentHom', uQComponentNative'} R,
    QuillenUniverseLift.rawNativeCarrierDown_comp_up.{uR', uQComponentModule',
      uQComponentObject', uQComponentHom', uQComponentNative'} R,
    QuillenUniverseLift.canonicalCarrierUp_comp_down.{uR', uQComponentModule',
      uQComponentObject', uQComponentHom', uQComponentNative'} R,
    QuillenUniverseLift.canonicalCarrierDown_comp_up.{uR', uQComponentModule',
      uQComponentObject', uQComponentHom', uQComponentNative'} R⟩

end AlgebraicKTheory.QuillenPlus

end
