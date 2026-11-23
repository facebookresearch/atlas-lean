/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.OriginalZeroTotalBasedContraction
public import MathlibExt.KTheory.Exact.Extension.CompletedCoreScalarUnit
public import MathlibExt.Topology.Homotopy.OriginalLoopOwnUnitCalibration
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# The actual original conull root and its original081 unit rectangle

The target's exact original selected based contraction null-homotopes the
actual stabilized map followed by the original projection. The actual
total-unit path and its original canonical Q-root comparison identify
the original selected point trace. The chosen root-path witness is kept
in the SAME original loop homotopy, and original081 units are compared by
their actual uniform rectangle.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalActionCategory
open CategoryTheory.CoreLocalizationComparison
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal
  CategoryTheory.MonoidalCategory ContinuousMap Simplicial

attribute [local instance] AlgebraicKTheory.ExtensionCategory.leftSumAction
attribute [local instance] AlgebraicKTheory.FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

universe uC vC uD vD uE vE

namespace AlgebraicKTheory.OriginalQZeroComparison

private abbrev originalConullProjection
    {E : Type uE} [Category.{vE} E] [Preadditive E]
    [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E] :=
  SSet.toTop.map (nerveMapCommonHom.{uE, max uE vE, 0}
    (ExtensionCategory.localizedTarget (C := E)))


variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

/-- The actual original total/base composite of the mixed stabilized functor. -/
public def originalMixedConullBaseMap :
    C(SSet.toTop.obj (nerve (ExtensionCategory.localizedExtensions (C := C)) : SSet.{max uC vC}),
      NQReal D) :=
  (originalConullProjection (E := D)).hom.comp
    (realizedNerveFunctorMap (ExtensionCategory.stabilizedFunctorMap F))

/-- The SAME original selected target contraction gives the whole null homotopy. -/
public def originalMixedConullNullHomotopy :
    ContinuousMap.Homotopy (originalMixedConullBaseMap F)
      (ContinuousMap.const
        (SSet.toTop.obj (nerve (ExtensionCategory.localizedExtensions (C := C)) : SSet.{max uC vC}))
        (zeroQVertex (C := D))) := by
  let T := realizedNerveFunctorMap (ExtensionCategory.stabilizedFunctorMap F)
  let p := (originalConullProjection (E := D)).hom
  let H := (originalConullContraction (E := D)).homotopy.compContinuousMap T
  have hTarget : p.comp (ContinuousMap.const
      (SSet.toTop.obj (nerve (ExtensionCategory.localizedExtensions (C := C)) : SSet.{max uC vC}))
      (zeroTotalVertex (C := D))) =
      ContinuousMap.const
        (SSet.toTop.obj (nerve (ExtensionCategory.localizedExtensions (C := C)) : SSet.{max uC vC}))
        (zeroQVertex (C := D)) := by
    apply ContinuousMap.ext
    intro x
    exact zeroTotalVertex_map (C := D)
  exact ((ContinuousMap.Homotopy.refl p).comp H).cast rfl hTarget

private theorem originalMixedConullNullHomotopyValueComputed (s : unitInterval)
    (x : SSet.toTop.obj (nerve (ExtensionCategory.localizedExtensions (C := C)) : SSet.{max uC vC}))
        :
    originalMixedConullNullHomotopy F (s, x) =
      SSet.toTop.map (nerveMapCommonHom.{uD, max uD vD, 0}
        (ExtensionCategory.localizedTarget (C := D)))
        ((SSet.basedContractionAtRealizedVertex
          (nerve (ExtensionCategory.localizedExtensions (C := D)) : SSet.{max uD vD})
          (ComposableArrows.mk₀ (zeroFiberUnit (C := D)).val)
          (originalLocalizedTotalTerminalWeak (C := D))).homotopy
            (s, realizedNerveFunctorMap (ExtensionCategory.stabilizedFunctorMap F) x)) := rfl

/-- EVERY total point/time uses the exact original selected based contraction. -/
public theorem originalMixedConullNullHomotopy_value (s : unitInterval)
    (x : SSet.toTop.obj (nerve (ExtensionCategory.localizedExtensions (C := C)) : SSet.{max uC vC}))
        :
    originalMixedConullNullHomotopy F (s, x) =
      SSet.toTop.map (nerveMapCommonHom.{uD, max uD vD, 0}
        (ExtensionCategory.localizedTarget (C := D)))
        ((SSet.basedContractionAtRealizedVertex
          (nerve (ExtensionCategory.localizedExtensions (C := D)) : SSet.{max uD vD})
          (ComposableArrows.mk₀ (zeroFiberUnit (C := D)).val)
          (originalLocalizedTotalTerminalWeak (C := D))).homotopy
            (s, realizedNerveFunctorMap (ExtensionCategory.stabilizedFunctorMap F) x)) :=
  originalMixedConullNullHomotopyValueComputed F s x

private theorem originalConullCanonicalSource :
    originalMixedConullBaseMap F (zeroTotalVertex (C := C)) =
      QuillenMixedUniverseTransport.mixedNQRealMap F (NQReal.basepoint C) :=
  (congrArg (originalConullProjection (E := D)) (originalMappedTotalUnitPath F).source.symm).trans
    ((originalMappedTotalUnitBasePath_value F 0).symm.trans
      (originalMappedTotalUnitBasePath F).source)

private def originalConullCanonicalRoot :
    Path (originalMixedConullBaseMap F (zeroTotalVertex (C := C))) (zeroQVertex (C := D)) :=
  (QuillenMixedUniverseTransport.mixedNQRootPath F).cast
    (originalConullCanonicalSource F) (NQReal.basepoint_eq_realizedVertex D).symm

private def originalConullMappedUnitRoot :
    Path (originalMixedConullBaseMap F (zeroTotalVertex (C := C))) (zeroQVertex (C := D)) :=
  (originalMappedTotalUnitBasePath F).cast
    (originalConullCanonicalSource F) (NQReal.basepoint_eq_realizedVertex D).symm

private theorem originalConullUnitTraceCanonical :
    ((originalMixedConullNullHomotopy F).evalAt (zeroTotalVertex (C := C))).Homotopic
      (originalConullCanonicalRoot F) := by
  let e := zeroTotalVertex (C := D)
  let a := realizedNerveFunctorMap (ExtensionCategory.stabilizedFunctorMap F) (zeroTotalVertex (C :=
      C))
  let HD := (originalConullContraction (E := D)).homotopy
  let p := originalConullProjection (E := D)
  let r : Path a e := originalMappedTotalUnitPath F
  have hIdentity : r.map (ContinuousMap.id _).continuous = r := by
    apply Path.ext
    rfl
  have hFixed : HD.evalAt e = Path.refl e := by
    apply Path.ext
    funext s
    exact (originalConullContraction (E := D)).fixed s
  have hConstant : r.map (ContinuousMap.const _ e).continuous = Path.refl e := by
    apply Path.ext
    rfl
  have hSquare := Path.Homotopic.map_trans_evalAt HD r
  rw [hIdentity, hFixed, hConstant] at hSquare
  have hRoot : r.Homotopic (HD.evalAt a) :=
    (Path.Homotopic.trans_refl r).symm.trans
      (hSquare.trans (Path.Homotopic.trans_refl (HD.evalAt a)))
  have hMapped := (hRoot.map p.hom).pathCast rfl (zeroTotalVertex_map (C := D)).symm
  have hL : (r.map p.hom.continuous).cast rfl (zeroTotalVertex_map (C := D)).symm =
      originalConullMappedUnitRoot F := by
    apply Path.ext
    funext s
    exact (originalMappedTotalUnitBasePath_value F s).symm
  have hR : ((HD.evalAt a).map p.hom.continuous).cast rfl (zeroTotalVertex_map (C := D)).symm =
      (originalMixedConullNullHomotopy F).evalAt (zeroTotalVertex (C := C)) := by
    apply Path.ext
    funext s
    exact (originalMixedConullNullHomotopy_value F s (zeroTotalVertex (C := C))).symm
  have hUnit : (originalConullMappedUnitRoot F).Homotopic (originalConullCanonicalRoot F) :=
    (originalMappedTotalUnitBasePath_homotopic_root F).pathCast
      (originalConullCanonicalSource F) (NQReal.basepoint_eq_realizedVertex D).symm
  exact ((hL ▸ hR ▸ hMapped).symm).trans hUnit

/-- The actual original stabilized total/base map uses the SAME canonical mixed Q root. -/
public def originalMixedConullWeakMap :
    ContinuousMap.WeaklyPointed (zeroTotalVertex (C := C)) (zeroQVertex (C := D)) where
  hom := originalMixedConullBaseMap F
  rootPath := originalConullCanonicalRoot F

omit [F.Additive] [F.IsExact] in
/-- The actual endpoint of the original total contraction is the constant weak map. -/
public def originalMixedConullConstantWeakMap :
    ContinuousMap.WeaklyPointed (zeroTotalVertex (C := C)) (zeroQVertex (C := D)) where
  hom := ContinuousMap.const
    (SSet.toTop.obj (nerve (ExtensionCategory.localizedExtensions (C := C)) : SSet.{max uC vC}))
    (zeroQVertex (C := D))
  rootPath := Path.refl (zeroQVertex (C := D))

private theorem originalMixedConullWeakMapHomValueComputed :
    (originalMixedConullWeakMap F).hom = originalMixedConullBaseMap F := rfl

private theorem originalMixedConullWeakMapRootPathValueComputed (t : unitInterval) :
    (originalMixedConullWeakMap F).rootPath t =
      QuillenMixedUniverseTransport.mixedNQRootPath F t := rfl

omit [F.Additive] [F.IsExact] in
private theorem originalMixedConullConstantWeakMapHomValueComputed :
    (originalMixedConullConstantWeakMap (C := C) (D := D)).hom =
      ContinuousMap.const
        (SSet.toTop.obj (nerve (ExtensionCategory.localizedExtensions (C := C)) : SSet.{max uC vC}))
        (zeroQVertex (C := D)) := rfl

omit [F.Additive] [F.IsExact] in
private theorem originalMixedConullConstantWeakMapAtRootComputed :
    (originalMixedConullConstantWeakMap (C := C) (D := D)).hom
        (zeroTotalVertex (C := C)) = zeroQVertex (C := D) :=
  congrArg (fun m => m (zeroTotalVertex (C := C)))
    (originalMixedConullConstantWeakMapHomValueComputed (C := C) (D := D))

omit [F.Additive] [F.IsExact] in
private theorem originalMixedConullConstantWeakMapRootPathEqComputed :
    (originalMixedConullConstantWeakMap (C := C) (D := D)).rootPath =
      (Path.refl (zeroQVertex (C := D))).cast
        (originalMixedConullConstantWeakMapAtRootComputed (C := C) (D := D)) rfl := by
  apply Path.ext
  rfl

private theorem originalMixedConullWeakMapCanonicalRootComputed :
    (originalConullCanonicalRoot F).cast
        (congrArg (fun m => m (zeroTotalVertex (C := C)))
          (originalMixedConullWeakMapHomValueComputed F)) rfl =
      (originalMixedConullWeakMap F).rootPath := by
  apply Path.ext
  rfl

private theorem originalMixedConullNullRootFamilyTargetComputed :
    ((((originalMixedConullNullHomotopy F).evalAt (zeroTotalVertex (C := C))).trans
        (Path.refl (zeroQVertex (C := D)))).cast
          (congrArg (fun m => m (zeroTotalVertex (C := C)))
            (originalMixedConullWeakMapHomValueComputed F)) rfl) =
      ((((originalMixedConullNullHomotopy F).cast
          (originalMixedConullWeakMapHomValueComputed F).symm
          (originalMixedConullConstantWeakMapHomValueComputed (C := C) (D := D)).symm).evalAt
            (zeroTotalVertex (C := C))).trans
        (originalMixedConullConstantWeakMap (C := C) (D := D)).rootPath) := by
  apply Path.ext
  rfl

/-- The whole original weak-map carrier is the actual stabilized/projection composite. -/
public theorem originalMixedConullWeakMap_hom_value :
    (originalMixedConullWeakMap F).hom = originalMixedConullBaseMap F :=
  originalMixedConullWeakMapHomValueComputed F

omit [F.Additive] [F.IsExact] in
/-- The entire original constant weak-map endpoint retains its literal constant map. -/
public theorem originalMixedConullConstantWeakMap_hom_value :
    (originalMixedConullConstantWeakMap (C := C) (D := D)).hom =
      ContinuousMap.const
        (SSet.toTop.obj (nerve (ExtensionCategory.localizedExtensions (C := C)) : SSet.{max uC vC}))
        (zeroQVertex (C := D)) :=
  originalMixedConullConstantWeakMapHomValueComputed (C := C) (D := D)

/-- The ACTUAL chosen root family is internally constructed from the original
total-unit path and contraction; no root or coherence outcome is supplied. -/
public def originalMixedConullNullRootFamily :
    (originalMixedConullWeakMap F).rootPath.Homotopy
      ((((originalMixedConullNullHomotopy F).cast
          (originalMixedConullWeakMap_hom_value F).symm
          (originalMixedConullConstantWeakMap_hom_value (C := C) (D := D)).symm).evalAt
            (zeroTotalVertex (C := C))).trans
        (originalMixedConullConstantWeakMap (C := C) (D := D)).rootPath) := by
  let K := ((originalConullUnitTraceCanonical F).symm.trans
    (Path.Homotopic.trans_refl
      ((originalMixedConullNullHomotopy F).evalAt (zeroTotalVertex (C := C)))).symm).some
  exact (K.pathCast
    (congrArg (fun m => m (zeroTotalVertex (C := C)))
      (originalMixedConullWeakMapHomValueComputed F)) rfl).cast
        (originalMixedConullWeakMapCanonicalRootComputed F)
        (originalMixedConullNullRootFamilyTargetComputed F)

/-- The SAME original full loop homotopy retains that exact chosen root family. -/
public def originalMixedConullNullLoopHomotopy :
    ContinuousMap.Homotopy (originalMixedConullWeakMap F).loopMap
      (originalMixedConullConstantWeakMap (C := C) (D := D)).loopMap :=
  ContinuousMap.WeaklyPointed.loopMapHomotopyOfMap
    (originalMixedConullWeakMap F) (originalMixedConullConstantWeakMap (C := C) (D := D))
    ((originalMixedConullNullHomotopy F).cast
      (originalMixedConullWeakMapHomValueComputed F).symm
      (originalMixedConullConstantWeakMapHomValueComputed (C := C) (D := D)).symm)
    (originalMixedConullNullRootFamily F)

/-- BOTH EXACT original081 unit paths are compatible with the actual whole
conull loop-family trace, through its internally earned original unit rectangle. -/
public theorem originalMixedConullNullLoopHomotopy_OWNunit :
    (((originalMixedConullNullLoopHomotopy F).evalAt (Path.refl (zeroTotalVertex (C := C)))).trans
      (ContinuousMap.WeaklyPointed.loopUnitRootPath
        (originalMixedConullConstantWeakMap (C := C) (D := D)))).Homotopic
        (ContinuousMap.WeaklyPointed.loopUnitRootPath (originalMixedConullWeakMap F)) :=
  ContinuousMap.WeaklyPointed.originalLoopMapHomotopy_OWNunit
    (originalMixedConullWeakMap F) (originalMixedConullConstantWeakMap (C := C) (D := D))
    ((originalMixedConullNullHomotopy F).cast
      (originalMixedConullWeakMapHomValueComputed F).symm
      (originalMixedConullConstantWeakMapHomValueComputed (C := C) (D := D)).symm)
    (originalMixedConullNullRootFamily F)

end AlgebraicKTheory.OriginalQZeroComparison

end


/-!
# Proper values of the same original conull weak maps

These characteristics preserve the exact original maps and selected root
family. They make the full return calibration independent of reducibility
of an imported definition, without changing any witness.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject ContinuousMap Simplicial

universe uC vC uD vD

namespace AlgebraicKTheory.OriginalQZeroComparison

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

/-- Every original weak-root time is the same canonical Q-zero edge time. -/
public theorem originalMixedConullWeakMap_rootPath_value (t : unitInterval) :
    (originalMixedConullWeakMap F).rootPath t =
      QuillenMixedUniverseTransport.mixedNQRootPath F t :=
  originalMixedConullWeakMapRootPathValueComputed F t

/-- The actual selected total point has the original Q-zero source image. -/
public theorem originalMixedConullBaseMap_zeroTotal :
    originalMixedConullBaseMap F (zeroTotalVertex (C := C)) =
      QuillenMixedUniverseTransport.mixedNQRealMap F (zeroQVertex (C := C)) :=
  (originalConullCanonicalSource F).trans
    (congrArg (QuillenMixedUniverseTransport.mixedNQRealMap F)
      (NQReal.basepoint_eq_realizedVertex C))

omit [F.Additive] [F.IsExact] in
/-- Every time of the original constant weak-root is its original selected Q-zero point. -/
public theorem originalMixedConullConstantWeakMap_rootPath_value (t : unitInterval) :
    (originalMixedConullConstantWeakMap (C := C) (D := D)).rootPath t =
      zeroQVertex (C := D) := by
  exact (congrArg
    (fun q : Path
        ((originalMixedConullConstantWeakMap (C := C) (D := D)).hom
          (zeroTotalVertex (C := C))) (zeroQVertex (C := D)) => q t)
    (originalMixedConullConstantWeakMapRootPathEqComputed (C := C) (D := D))).trans rfl

omit [F.Additive] [F.IsExact] in
/-- The whole original constant weak-root is the original reflexive path. -/
public theorem originalMixedConullConstantWeakMap_rootPath_eq :
    (originalMixedConullConstantWeakMap (C := C) (D := D)).rootPath =
      (Path.refl (zeroQVertex (C := D))).cast
        (congrArg (fun m => m (zeroTotalVertex (C := C)))
          (originalMixedConullConstantWeakMap_hom_value (C := C) (D := D))) rfl :=
  originalMixedConullConstantWeakMapRootPathEqComputed (C := C) (D := D)

end AlgebraicKTheory.OriginalQZeroComparison

end
