/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.OriginalConullScalarLoopFormula
public import MathlibExt.KTheory.Ring.StableGeneralLinear.OriginalUnliftedQEvaluatorTransport

/-!
# Whole return calibration for the original full scalar homotopy-fiber map

The actual original conull return after the actual mixed full-fiber map and
original selected-loop inclusion is compared on every loop to the canonical
mixed Q loop map. The original chosen conull root family supplies the left
prefix homotopy. Both original point homeomorphisms and all loop components
are retained. Unit compatibility with the completed-Core fiber family is a
separate construction.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicKTheory.QuillenMixedUniverseTransport
open AlgebraicKTheory.OriginalQuillenUnliftedTransport
open scoped ZeroObject ContinuousMap Simplicial

universe uA uB uC vC uD vD

namespace AlgebraicKTheory.OriginalQZeroComparison

private def originalLeftPrefixMap
    {A : Type uA} {B : Type uB} [TopologicalSpace A] [TopologicalSpace B]
    {a b : B} (p : Path a b) (r : C(A, Path a b)) : C(A, LoopSpace B b) where
  toFun x := p.symm.trans (r x)
  continuous_toFun := Continuous.path_trans continuous_const r.continuous

private def originalLeftPrefixFamily
    {A : Type uA} {B : Type uB} [TopologicalSpace A] [TopologicalSpace B]
    {a b : B} {p q : Path a b} (H : p.Homotopy q) (r : C(A, Path a b)) :
    ContinuousMap.Homotopy (originalLeftPrefixMap p r) (originalLeftPrefixMap q r) where
  toFun z := (H.eval z.1).symm.trans (r z.2)
  continuous_toFun := by
    let E : C(unitInterval, Path a b) :=
      ⟨H.eval, Path.continuous_uncurry_iff.mp H.continuous_toFun⟩
    exact Continuous.path_trans
      (Path.continuous_symm.comp (E.continuous.comp continuous_fst))
      (r.continuous.comp continuous_snd)
  map_zero_left x := by
    rw [Path.Homotopy.eval_zero]
    rfl
  map_one_left x := by
    rw [Path.Homotopy.eval_one]
    rfl

private theorem originalPathTransValueCongr
    {B : Type uB} [TopologicalSpace B]
    {a b c a' b' c' : B}
    (p : Path a b) (q : Path b c) (p' : Path a' b') (q' : Path b' c')
    (hp : ∀ s : unitInterval, p s = p' s) (hq : ∀ s : unitInterval, q s = q' s)
    (t : unitInterval) :
    (p.trans q) t = (p'.trans q') t := by
  refine Eq.trans (Path.trans_apply p q t)
    (Eq.trans ?_ (Path.trans_apply p' q' t).symm)
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · simp only [dif_pos ht]
    exact hp _
  · simp only [dif_neg ht]
    exact hq _

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

private abbrev originalReturnTrace :=
  (originalMixedConullNullHomotopy F).evalAt (zeroTotalVertex (C := C))

private def originalReturnCanonicalRoot :
    Path (originalMixedConullBaseMap F (zeroTotalVertex (C := C))) (zeroQVertex (C := D)) :=
  (mixedNQRootPath F).cast
    ((originalMixedConullBaseMap_zeroTotal F).trans
      (congrArg (mixedNQRealMap F) (NQReal.basepoint_eq_realizedVertex C).symm))
    (NQReal.basepoint_eq_realizedVertex D).symm

private theorem originalReturnCanonicalRootValueComputed (t : unitInterval) :
    originalReturnCanonicalRoot F t = mixedNQRootPath F t := rfl

/-- The prefix family keeps the EXACT original chosen conull root witness,
then removes its appended reflexive path by the original continuous correction. -/
public def originalConullScalarReturnPrefixHomotopy :
    ((originalMixedConullNullHomotopy F).evalAt (zeroTotalVertex (C := C))).Homotopy
      ((mixedNQRootPath F).cast
        ((originalMixedConullBaseMap_zeroTotal F).trans
          (congrArg (mixedNQRealMap F) (NQReal.basepoint_eq_realizedVertex C).symm))
        (NQReal.basepoint_eq_realizedVertex D).symm) := by
  let p := originalReturnTrace F
  let q := originalReturnCanonicalRoot F
  have hMap := congrArg
    (fun m => m (zeroTotalVertex (C := C))) (originalMixedConullWeakMap_hom_value F)
  let H := (originalMixedConullNullRootFamily F).pathCast hMap.symm rfl
  have H' : q.Homotopy (p.trans (Path.refl (zeroQVertex (C := D)))) := by
    refine H.cast ?_ ?_
    · apply Path.ext
      funext t
      exact originalMixedConullWeakMap_rootPath_value F t
    · apply Path.ext
      funext t
      rw [originalMixedConullConstantWeakMap_rootPath_eq]
      rfl
  exact (H'.trans (Path.Homotopy.transRefl p)).symm

private def originalReturnMappedLoop
    (gamma : LoopSpace (SSet.toTop.obj (nerve (QuillenQ C) : SSet.{max uC vC}))
      (zeroQVertex (C := C))) :
    Path (originalMixedConullBaseMap F (zeroTotalVertex (C := C)))
      (originalMixedConullBaseMap F (zeroTotalVertex (C := C))) :=
  (gamma.map (mixedNQRealMap F).continuous).cast
    (originalMixedConullBaseMap_zeroTotal F) (originalMixedConullBaseMap_zeroTotal F)

private theorem originalReturnMappedLoopValueComputed
    (gamma : LoopSpace (SSet.toTop.obj (nerve (QuillenQ C) : SSet.{max uC vC}))
      (zeroQVertex (C := C))) (t : unitInterval) :
    originalReturnMappedLoop F gamma t = mixedNQRealMap F (gamma t) := rfl

private def originalReturnRightPath :
    C(LoopSpace (SSet.toTop.obj (nerve (QuillenQ C) : SSet.{max uC vC}))
        (zeroQVertex (C := C)),
      Path (originalMixedConullBaseMap F (zeroTotalVertex (C := C))) (zeroQVertex (C := D))) where
  toFun gamma := (originalReturnMappedLoop F gamma).trans (originalReturnCanonicalRoot F)
  continuous_toFun := Continuous.path_trans
    (Path.continuous_uncurry_iff.mp ((mixedNQRealMap F).continuous.comp continuous_eval))
    continuous_const

private theorem originalReturnLiteralRecipeValue
    (gamma : LoopSpace (SSet.toTop.obj (nerve (QuillenQ C) : SSet.{max uC vC}))
      (zeroQVertex (C := C))) (t : unitInterval) :
    zeroOriginalHomotopyFiberToLoops (C := D)
        (mixedOriginalZeroFiberMap F (zeroLoopToOriginalHomotopyFiber (C := C) gamma)) t =
      (originalLeftPrefixMap (originalReturnTrace F) (originalReturnRightPath F) gamma) t := by
  rw [originalConullScalar_selectedLoop_value]
  change _ = ((originalReturnTrace F).symm.trans
    ((originalReturnMappedLoop F gamma).trans (originalReturnCanonicalRoot F))) t
  rw [Path.trans_apply]
  split
  · rfl
  · rename_i ht
    rw [Path.trans_apply]
    split
    · rename_i hs
      let s : unitInterval := ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2
        ⟨(not_le.1 ht).le, unitInterval.le_one t⟩⟩
      let r : unitInterval := ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2
        ⟨(not_le.1 ht).le, t.2.2⟩⟩
      have hClock : r = s := by
        apply Subtype.ext
        rfl
      have hReadout := congrArg
        (fun v : unitInterval =>
          if hv : (v : ℝ) ≤ 1 / 2 then
            mixedNQRealMap F
              (gamma ⟨2 * v, (unitInterval.mul_pos_mem_iff zero_lt_two).2
                ⟨unitInterval.nonneg v, hv⟩⟩)
          else
            mixedNQRootPath F
              ⟨2 * v - 1, unitInterval.two_mul_sub_one_mem_iff.2
                ⟨(not_le.1 hv).le, unitInterval.le_one v⟩⟩) hClock
      exact (hReadout.trans (dif_pos hs)).trans
        (originalReturnMappedLoopValueComputed F gamma
          (⟨2 * s, (unitInterval.mul_pos_mem_iff zero_lt_two).2
            ⟨unitInterval.nonneg s, hs⟩⟩ : unitInterval)).symm
    · rename_i hs
      let s : unitInterval := ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2
        ⟨(not_le.1 ht).le, unitInterval.le_one t⟩⟩
      let r : unitInterval := ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2
        ⟨(not_le.1 ht).le, t.2.2⟩⟩
      have hClock : r = s := by
        apply Subtype.ext
        rfl
      have hReadout := congrArg
        (fun v : unitInterval =>
          if hv : (v : ℝ) ≤ 1 / 2 then
            mixedNQRealMap F
              (gamma ⟨2 * v, (unitInterval.mul_pos_mem_iff zero_lt_two).2
                ⟨unitInterval.nonneg v, hv⟩⟩)
          else
            mixedNQRootPath F
              ⟨2 * v - 1, unitInterval.two_mul_sub_one_mem_iff.2
                ⟨(not_le.1 hv).le, unitInterval.le_one v⟩⟩) hClock
      exact (hReadout.trans (dif_neg hs)).trans
        (originalReturnCanonicalRootValueComputed F
          (⟨2 * s - 1, unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 hs).le, unitInterval.le_one s⟩⟩ : unitInterval)).symm

private theorem originalReturnCanonicalRecipeValue
    (gamma : LoopSpace (SSet.toTop.obj (nerve (QuillenQ C) : SSet.{max uC vC}))
      (zeroQVertex (C := C))) :
    originalNQLoopPointHomeomorph D
        (mixedNQKSpaceMap F ((originalNQLoopPointHomeomorph C).symm gamma)) =
      originalLeftPrefixMap (originalReturnCanonicalRoot F) (originalReturnRightPath F) gamma := by
  apply Path.ext
  funext t
  let p : NQKSpace C := (originalNQLoopPointHomeomorph C).symm gamma
  have hMapped : ∀ s : unitInterval,
      (p.map (mixedNQRealMap F).continuous) s = originalReturnMappedLoop F gamma s := by
    intro s
    exact (congrArg (mixedNQRealMap F)
      (originalNQLoopPointHomeomorph_symm_value C gamma s)).trans
        (originalReturnMappedLoopValueComputed F gamma s).symm
  have hRoot : ∀ s : unitInterval,
      mixedNQRootPath F s = originalReturnCanonicalRoot F s :=
    fun s => (originalReturnCanonicalRootValueComputed F s).symm
  have hRight : ∀ s : unitInterval,
      ((p.map (mixedNQRealMap F).continuous).trans (mixedNQRootPath F)) s =
        ((originalReturnMappedLoop F gamma).trans (originalReturnCanonicalRoot F)) s :=
    fun s => originalPathTransValueCongr (B := NQReal D)
      (p.map (mixedNQRealMap F).continuous) (mixedNQRootPath F)
      (originalReturnMappedLoop F gamma) (originalReturnCanonicalRoot F) hMapped hRoot s
  have hPrefix : ∀ s : unitInterval,
      (mixedNQRootPath F).symm s = (originalReturnCanonicalRoot F).symm s :=
    fun s => hRoot (unitInterval.symm s)
  have hConjugate := originalPathTransValueCongr (B := NQReal D)
    (mixedNQRootPath F).symm
    ((p.map (mixedNQRealMap F).continuous).trans (mixedNQRootPath F))
    (originalReturnCanonicalRoot F).symm
    ((originalReturnMappedLoop F gamma).trans (originalReturnCanonicalRoot F))
    hPrefix hRight t
  have hMap := congrArg (fun q : NQKSpace D => q t) (mixedNQKSpaceMap_value F p)
  exact (originalNQLoopPointHomeomorph_value D (mixedNQKSpaceMap F p) t).trans
    (hMap.trans hConjugate)

/-- The WHOLE literal original conull/selected-loop route is homotopic to
SAME canonical Q loop map through the original point homeomorphisms at both ends. -/
public def originalConullScalarReturnHomotopyAtOriginalPoints :
    ContinuousMap.Homotopy
      (((zeroOriginalHomotopyFiberToLoops (C := D)).hom.comp (mixedOriginalZeroFiberMap F)).comp
        (zeroLoopToOriginalHomotopyFiber (C := C)).hom)
      ((originalNQLoopPointHomeomorph D).toHomotopyEquiv.toFun.comp
        ((mixedNQKSpaceMap F).comp (originalNQLoopPointHomeomorph C).symm.toHomotopyEquiv.toFun)) :=
            by
  let H := originalLeftPrefixFamily (originalConullScalarReturnPrefixHomotopy F)
    (originalReturnRightPath F)
  refine H.cast ?_ ?_
  · apply ContinuousMap.ext
    intro gamma
    apply Path.ext
    funext t
    exact (originalReturnLiteralRecipeValue F gamma t).symm
  · apply ContinuousMap.ext
    intro gamma
    exact (originalReturnCanonicalRecipeValue F gamma).symm

/-- On the original NQKSpace carriers, the full original conull return,
actual mixed fiber map and original selected-loop inclusion calibrate to the
actual canonical mixed NQKSpaceMap on EVERY component. -/
public def originalConullScalarReturnHomotopy :
    ContinuousMap.Homotopy
      ((originalNQLoopPointHomeomorph D).symm.toHomotopyEquiv.toFun.comp
        ((((zeroOriginalHomotopyFiberToLoops (C := D)).hom.comp (mixedOriginalZeroFiberMap F)).comp
          (zeroLoopToOriginalHomotopyFiber (C := C)).hom).comp
            (originalNQLoopPointHomeomorph C).toHomotopyEquiv.toFun))
      (mixedNQKSpaceMap F) := by
  let A := (originalNQLoopPointHomeomorph C).toHomotopyEquiv.toFun
  let B := (originalNQLoopPointHomeomorph D).symm.toHomotopyEquiv.toFun
  let H := (ContinuousMap.Homotopy.refl B).comp
    ((originalConullScalarReturnHomotopyAtOriginalPoints F).compContinuousMap A)
  refine H.cast rfl ?_
  apply ContinuousMap.ext
  intro gamma
  change (originalNQLoopPointHomeomorph D).symm
    (originalNQLoopPointHomeomorph D
      (mixedNQKSpaceMap F ((originalNQLoopPointHomeomorph C).symm
        (originalNQLoopPointHomeomorph C gamma)))) = mixedNQKSpaceMap F gamma
  rw [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]

end AlgebraicKTheory.OriginalQZeroComparison

end


/-!
# The literal completed-unit fiber path and its actual conull trace

The path uses the exact original completed-Core fiber homotopy at the
original unit, followed by the original fiber comparison applied to the
actual completed-Core mapped-unit root. Both endpoint identifications are
proved from the original independent selected fiber point. Its conull trace
is the actual trace used for the subsequent unit-root calibration.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CoreLocalizationComparison
open CategoryTheory.MonoidalActionCategory
open AlgebraicKTheory.QuillenMixedUniverseTransport
open AlgebraicKTheory.OriginalQuillenUnliftedTransport
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal
  CategoryTheory.MonoidalCategory ContinuousMap Simplicial

attribute [local instance] AlgebraicKTheory.ExtensionCategory.leftSumAction
attribute [local instance] AlgebraicKTheory.FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

universe uE vE uC vC uD vD

namespace AlgebraicKTheory.OriginalQZeroComparison

private abbrev originalScalarCompletedUnit
    (E : Type uE) [Category.{vE} E] [Preadditive E]
    [HasZeroObject E] [HasBinaryBiproducts E] :=
  SSet.realizedVertex
    (X := (nerve (SInverse (Core E) (Core E)) : SSet.{max uE vE}))
    (ComposableArrows.mk₀
      ((SInverse.inclusion (Core E) (Core E)).obj (𝟙_ (Core E))))

private abbrev originalScalarSelectedFiberPoint
    (E : Type uE) [Category.{vE} E] [Preadditive E]
    [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E] :=
  TopCat.homotopyFiberSelectedPointMap
    (SSet.toTop.map (nerveMapCommonHom.{uE, max uE vE, 0}
      (ExtensionCategory.localizedTarget (C := E))))
    (zeroTotalVertex (C := E)) (zeroQVertex (C := E)) (zeroTotalVertex_map (C := E))
    (PUnit.unit : PUnit.{(max uE vE) + 1})

private theorem originalScalarCompletedUnitFiber
    (E : Type uE) [Category.{vE} E] [Preadditive E]
    [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E] :
    completedCoreToOriginalHomotopyFiber (C := E) (originalScalarCompletedUnit E) =
      originalScalarSelectedFiberPoint E := by
  let c : TopCat.of PUnit.{(max uE vE) + 1} ⟶
      SSet.toTop.obj (nerve (SInverse (Core E) (Core E)) : SSet.{max uE vE}) :=
    TopCat.const (originalScalarCompletedUnit E)
  exact (TopCat.comp_app c (completedCoreToOriginalHomotopyFiber (C := E))
    (PUnit.unit : PUnit.{(max uE vE) + 1})).symm.trans
      (ConcreteCategory.congr_hom
        (completedCoreToOriginalHomotopyFiber_unit_selectedPoint (C := E))
        (PUnit.unit : PUnit.{(max uE vE) + 1}))

private theorem originalScalarSelectedLoopFiber
    (E : Type uE) [Category.{vE} E] [Preadditive E]
    [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E] :
    zeroLoopToOriginalHomotopyFiber (C := E) (Path.refl (zeroQVertex (C := E))) =
      originalScalarSelectedFiberPoint E := by
  let c : TopCat.of PUnit.{(max uE vE) + 1} ⟶
      TopCat.of (LoopSpace (SSet.toTop.obj (nerve (QuillenQ E) : SSet.{max uE vE}))
        (zeroQVertex (C := E))) :=
    TopCat.const (Path.refl (zeroQVertex (C := E)))
  exact (TopCat.comp_app c (zeroLoopToOriginalHomotopyFiber (C := E))
    (PUnit.unit : PUnit.{(max uE vE) + 1})).symm.trans
      (ConcreteCategory.congr_hom
        (zeroLoopToOriginalHomotopyFiber_constant_point (C := E))
        (PUnit.unit : PUnit.{(max uE vE) + 1}))

private theorem originalScalarSelectedReturnPoint
    (E : Type uE) [Category.{vE} E] [Preadditive E]
    [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E] :
    zeroOriginalHomotopyFiberToLoops (C := E) (originalScalarSelectedFiberPoint E) =
      Path.refl (zeroQVertex (C := E)) := by
  let p : SSet.toTop.obj
      (nerve (ExtensionCategory.localizedExtensions (C := E)) : SSet.{max uE vE}) ⟶
      SSet.toTop.obj (nerve (QuillenQ E) : SSet.{max uE vE}) :=
    SSet.toTop.map (nerveMapCommonHom.{uE, max uE vE, 0}
      (ExtensionCategory.localizedTarget (C := E)))
  let c : TopCat.of PUnit.{(max uE vE) + 1} ⟶
      TopCat.homotopyFiber p (zeroQVertex (C := E)) :=
    TopCat.homotopyFiberSelectedPointMap p (zeroTotalVertex (C := E))
      (zeroQVertex (C := E)) (zeroTotalVertex_map (C := E))
  exact (TopCat.comp_app c (zeroOriginalHomotopyFiberToLoops (C := E))
    (PUnit.unit : PUnit.{(max uE vE) + 1})).symm.trans
      (ConcreteCategory.congr_hom
        (zeroOriginalHomotopyFiberToLoops_selectedPoint (C := E))
        (PUnit.unit : PUnit.{(max uE vE) + 1}))

private theorem originalScalarNQPointHomeomorphUnit
    (E : Type uE) [Category.{vE} E] [Preadditive E]
    [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E] :
    originalNQLoopPointHomeomorph E (Path.refl (NQReal.basepoint E)) =
      Path.refl (zeroQVertex (C := E)) := by
  apply Path.ext
  funext t
  exact (originalNQLoopPointHomeomorph_value E (Path.refl (NQReal.basepoint E)) t).trans
    (NQReal.basepoint_eq_realizedVertex E)

private theorem originalScalarNQPointHomeomorphInverseUnit
    (E : Type uE) [Category.{vE} E] [Preadditive E]
    [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E] :
    (originalNQLoopPointHomeomorph E).symm (Path.refl (zeroQVertex (C := E))) =
      Path.refl (NQReal.basepoint E) := by
  apply Path.ext
  funext t
  exact (originalNQLoopPointHomeomorph_symm_value E (Path.refl (zeroQVertex (C := E))) t).trans
    (NQReal.basepoint_eq_realizedVertex E).symm

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

/-- The literal fiber root uses the SAME189 homotopy at the actual completed
unit, then kappaD applied to the completed-unit root, with the original
independent selected-point equations as its only endpoint transports. -/
public def originalConullScalarBetaFiber :
    Path
      (mixedOriginalZeroFiberMap F
        (zeroLoopToOriginalHomotopyFiber (C := C) (Path.refl (zeroQVertex (C := C)))))
      (TopCat.homotopyFiberSelectedPointMap
        (SSet.toTop.map (nerveMapCommonHom.{uD, max uD vD, 0}
          (ExtensionCategory.localizedTarget (C := D))))
        (zeroTotalVertex (C := D)) (zeroQVertex (C := D)) (zeroTotalVertex_map (C := D)) PUnit.unit)
            := by
  let H := (completedCoreOriginalFiberNaturalityHomotopy F).evalAt (originalScalarCompletedUnit C)
  let r := (completedCoreOriginalUnitRootPath F).map
    (completedCoreToOriginalHomotopyFiber (C := D)).hom.continuous
  have hSource :
      mixedOriginalZeroFiberMap F
          (zeroLoopToOriginalHomotopyFiber (C := C) (Path.refl (zeroQVertex (C := C)))) =
        mixedOriginalZeroFiberMap F
          (completedCoreToOriginalHomotopyFiber (C := C) (originalScalarCompletedUnit C)) :=
    congrArg (mixedOriginalZeroFiberMap F)
      ((originalScalarSelectedLoopFiber C).trans (originalScalarCompletedUnitFiber C).symm)
  exact (H.trans r).cast hSource (originalScalarCompletedUnitFiber D).symm

private theorem originalConullScalarBetaFiberValueComputed (s : unitInterval) :
    (originalConullScalarBetaFiber F).toContinuousMap.toFun s =
      if hs : (s : ℝ) ≤ 1 / 2 then
        completedCoreOriginalFiberNaturalityHomotopy F
          (⟨2 * s, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩,
            SSet.realizedVertex (ComposableArrows.mk₀
              ((SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C)))))
      else
        completedCoreToOriginalHomotopyFiber (C := D)
          (completedCoreOriginalUnitRootPath F
            ⟨2 * s - 1, unitInterval.two_mul_sub_one_mem_iff.2
              ⟨(not_le.1 hs).le, s.2.2⟩⟩) := by
  let H := (completedCoreOriginalFiberNaturalityHomotopy F).evalAt
    (originalScalarCompletedUnit C)
  let r := (completedCoreOriginalUnitRootPath F).map
    (completedCoreToOriginalHomotopyFiber (C := D)).hom.continuous
  change (H.trans r).toContinuousMap.toFun s = _
  have hTrans := Path.trans_apply H r s
  refine hTrans.trans ?_
  split <;> rfl

/-- EVERY original fiber-root time keeps the conull scalar return family followed by
kappaD of the completed-unit root, on the original half-interval concatenation clock. -/
public theorem originalConullScalarBetaFiber_value (s : unitInterval) :
    (originalConullScalarBetaFiber F).toContinuousMap.toFun s =
      if hs : (s : ℝ) ≤ 1 / 2 then
        completedCoreOriginalFiberNaturalityHomotopy F
          (⟨2 * s, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩,
            SSet.realizedVertex (ComposableArrows.mk₀
              ((SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C)))))
      else
        completedCoreToOriginalHomotopyFiber (C := D)
          (completedCoreOriginalUnitRootPath F
            ⟨2 * s - 1, unitInterval.two_mul_sub_one_mem_iff.2
              ⟨(not_le.1 hs).le, s.2.2⟩⟩) := by
  exact originalConullScalarBetaFiberValueComputed F s

/-- The original conull return maps the entire literal betaFiber into the
original Q-loop space, ending at its literal constant loop. -/
public def originalConullScalarBetaReturnTraceAtOriginalPoints :
    Path
      (zeroOriginalHomotopyFiberToLoops (C := D)
        (mixedOriginalZeroFiberMap F
          (zeroLoopToOriginalHomotopyFiber (C := C) (Path.refl (zeroQVertex (C := C))))))
      (Path.refl (zeroQVertex (C := D))) :=
  ((originalConullScalarBetaFiber F).map
    (zeroOriginalHomotopyFiberToLoops (C := D)).hom.continuous).cast rfl
      (originalScalarSelectedReturnPoint D).symm

private theorem originalConullScalarBetaReturnTraceAtOriginalPointsValueComputed (s t :
    unitInterval) :
    originalConullScalarBetaReturnTraceAtOriginalPoints F s t =
      if ht : (t : ℝ) ≤ 1 / 2 then
        SSet.toTop.map (nerveMapCommonHom.{uD, max uD vD, 0}
          (ExtensionCategory.localizedTarget (C := D)))
          ((SSet.basedContractionAtRealizedVertex
            (nerve (ExtensionCategory.localizedExtensions (C := D)) : SSet.{max uD vD})
            (ComposableArrows.mk₀ (zeroFiberUnit (C := D)).val)
            (originalLocalizedTotalTerminalWeak (C := D))).homotopy.symm.toContinuousMap
              (⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩,
                TopCat.homotopyFiberToTotal
                  (SSet.toTop.map (nerveMapCommonHom.{uD, max uD vD, 0}
                    (ExtensionCategory.localizedTarget (C := D))))
                  (zeroQVertex (C := D)) ((originalConullScalarBetaFiber F).toContinuousMap.toFun
                      s)))
      else
        TopCat.homotopyFiberPath
          (SSet.toTop.map (nerveMapCommonHom.{uD, max uD vD, 0}
            (ExtensionCategory.localizedTarget (C := D))))
          (zeroQVertex (C := D)) ((originalConullScalarBetaFiber F).toContinuousMap.toFun s)
          (TopCat.I.homeomorph.{max uD vD}.symm
            ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2
              ⟨(not_le.1 ht).le, t.2.2⟩⟩) := by
  let K : SSet.{max uD vD} := nerve (ExtensionCategory.localizedExtensions (C := D))
  let x : K _⦋0⦌ := ComposableArrows.mk₀ (zeroFiberUnit (C := D)).val
  let p : SSet.toTop.obj K ⟶
      SSet.toTop.obj (nerve (QuillenQ D) : SSet.{max uD vD}) :=
    SSet.toTop.map (nerveMapCommonHom.{uD, max uD vD, 0}
      (ExtensionCategory.localizedTarget (C := D)))
  let z : TopCat.homotopyFiber p (zeroQVertex (C := D)) := (originalConullScalarBetaFiber
      F).toContinuousMap.toFun s
  have hOwn : originalConullScalarBetaReturnTraceAtOriginalPoints F s t =
      ((zeroOriginalHomotopyFiberToLoops (C := D)).hom.toFun z).toContinuousMap.toFun t := rfl
  have hReturnMap := congrArg
    (fun m : TopCat.homotopyFiber p (zeroQVertex (C := D)) ⟶
        TopCat.of (LoopSpace
          (SSet.toTop.obj (nerve (QuillenQ D) : SSet.{max uD vD}))
          (zeroQVertex (C := D))) => (m.hom.toFun z).toContinuousMap.toFun t)
    (zeroOriginalHomotopyFiberToLoops_eq_realizedConull (C := D))
  have hReturnValue := TopCat.homotopyFiberToLoopsOfRealizedConull_apply K x p
    (zeroQVertex (C := D)) (zeroTotalVertex_map (C := D))
    (originalLocalizedTotalTerminalWeak (C := D)) z t
  exact hOwn.trans (hReturnMap.trans hReturnValue)

/-- EVERY fiber-root time and loop time retain the literal original conull
contraction at the actual betaFiber total and its full carried-path coordinate. -/
public theorem originalConullScalarBetaReturnTraceAtOriginalPoints_value (s t : unitInterval) :
    originalConullScalarBetaReturnTraceAtOriginalPoints F s t =
      if ht : (t : ℝ) ≤ 1 / 2 then
        SSet.toTop.map (nerveMapCommonHom.{uD, max uD vD, 0}
          (ExtensionCategory.localizedTarget (C := D)))
          ((SSet.basedContractionAtRealizedVertex
            (nerve (ExtensionCategory.localizedExtensions (C := D)) : SSet.{max uD vD})
            (ComposableArrows.mk₀ (zeroFiberUnit (C := D)).val)
            (originalLocalizedTotalTerminalWeak (C := D))).homotopy.symm.toContinuousMap
              (⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩,
                TopCat.homotopyFiberToTotal
                  (SSet.toTop.map (nerveMapCommonHom.{uD, max uD vD, 0}
                    (ExtensionCategory.localizedTarget (C := D))))
                  (zeroQVertex (C := D)) ((originalConullScalarBetaFiber F).toContinuousMap.toFun
                      s)))
      else
        TopCat.homotopyFiberPath
          (SSet.toTop.map (nerveMapCommonHom.{uD, max uD vD, 0}
            (ExtensionCategory.localizedTarget (C := D))))
          (zeroQVertex (C := D)) ((originalConullScalarBetaFiber F).toContinuousMap.toFun s)
          (TopCat.I.homeomorph.{max uD vD}.symm
            ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2
              ⟨(not_le.1 ht).le, t.2.2⟩⟩) := by
  exact originalConullScalarBetaReturnTraceAtOriginalPointsValueComputed F s t

private abbrev originalScalarNativeReturnMap : C(NQKSpace C, NQKSpace D) :=
  (originalNQLoopPointHomeomorph D).symm.toHomotopyEquiv.toFun.comp
    ((((zeroOriginalHomotopyFiberToLoops (C := D)).hom.comp (mixedOriginalZeroFiberMap F)).comp
      (zeroLoopToOriginalHomotopyFiber (C := C)).hom).comp
        (originalNQLoopPointHomeomorph C).toHomotopyEquiv.toFun)

/-- The SAME original point inverse transports the literal full betaFiber
return trace to the original NQKSpace carriers and their actual constant loops. -/
public def originalConullScalarBetaReturnTrace :
    Path
      (((originalNQLoopPointHomeomorph D).symm.toHomotopyEquiv.toFun.comp
        ((((zeroOriginalHomotopyFiberToLoops (C := D)).hom.comp (mixedOriginalZeroFiberMap F)).comp
          (zeroLoopToOriginalHomotopyFiber (C := C)).hom).comp
            (originalNQLoopPointHomeomorph C).toHomotopyEquiv.toFun))
        (Path.refl (NQReal.basepoint C)))
      (Path.refl (NQReal.basepoint D)) := by
  let A := (originalNQLoopPointHomeomorph D).symm.toHomotopyEquiv.toFun
  have hSource : originalScalarNativeReturnMap F (Path.refl (NQReal.basepoint C)) =
      A (zeroOriginalHomotopyFiberToLoops (C := D)
        (mixedOriginalZeroFiberMap F
          (zeroLoopToOriginalHomotopyFiber (C := C) (Path.refl (zeroQVertex (C := C)))))) := by
    change A
      (zeroOriginalHomotopyFiberToLoops (C := D)
        (mixedOriginalZeroFiberMap F
          (zeroLoopToOriginalHomotopyFiber (C := C)
            (originalNQLoopPointHomeomorph C (Path.refl (NQReal.basepoint C)))))) =
      A (zeroOriginalHomotopyFiberToLoops (C := D)
        (mixedOriginalZeroFiberMap F
          (zeroLoopToOriginalHomotopyFiber (C := C) (Path.refl (zeroQVertex (C := C))))))
    exact congrArg
      (fun gamma : LoopSpace
          (SSet.toTop.obj (nerve (QuillenQ C) : SSet.{max uC vC}))
          (zeroQVertex (C := C)) =>
        A (zeroOriginalHomotopyFiberToLoops (C := D)
          (mixedOriginalZeroFiberMap F (zeroLoopToOriginalHomotopyFiber (C := C) gamma))))
      (originalScalarNQPointHomeomorphUnit C)
  exact ((originalConullScalarBetaReturnTraceAtOriginalPoints F).map A.continuous).cast
    hSource (originalScalarNQPointHomeomorphInverseUnit D).symm

end AlgebraicKTheory.OriginalQZeroComparison

end


/-!
# Actual unit-root calibration by a whole loop-translation family

The original return homotopy is retained. Its actual constant-loop trace
and the original081 canonical weak-map unit determine a literal difference
loop with the actual betaFiber return trace. Left multiplication by that
loop gives an auxiliary whole self-map homotopy. The original prepend and
append unit rectangles prove its unit law. Genuine path cancellation then
calibrates the complete return homotopy to the original betaFiber root.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open ContinuousMap
open AlgebraicKTheory.QuillenMixedUniverseTransport
open AlgebraicKTheory.OriginalQuillenUnliftedTransport
open scoped ZeroObject ContinuousMap Simplicial

universe uB uC vC uD vD

namespace AlgebraicKTheory.OriginalQZeroComparison

private def originalLoopTranslationFamily
    {B : Type uB} [TopologicalSpace B] {b : B}
    (d : LoopSpace (LoopSpace B b) (Path.refl b)) :
    ContinuousMap.Homotopy (pathPrependRefl b b) (pathPrependRefl b b) where
  toFun z := (d z.1).trans z.2
  continuous_toFun := Continuous.path_trans
    (d.continuous.comp continuous_fst) continuous_snd
  map_zero_left gamma :=
    congrArg (fun p : LoopSpace B b => p.trans gamma) d.source
  map_one_left gamma :=
    congrArg (fun p : LoopSpace B b => p.trans gamma) d.target

private def originalLoopTranslationSelfHomotopy
    {B : Type uB} [TopologicalSpace B] {b : B}
    (d : LoopSpace (LoopSpace B b) (Path.refl b)) :
    ContinuousMap.Homotopy (ContinuousMap.id (LoopSpace B b)) (ContinuousMap.id (LoopSpace B b)) :=
  (pathPrependReflHomotopy b b).symm.trans
    ((originalLoopTranslationFamily d).trans (pathPrependReflHomotopy b b))

private theorem originalLoopTranslationUnitRectangle
    {B : Type uB} [TopologicalSpace B] {b : B}
    (d : LoopSpace (LoopSpace B b) (Path.refl b))
    (v : LoopSpace B b) (U : Path v (Path.refl b)) :
    (((originalLoopTranslationSelfHomotopy d).evalAt v).trans U).Homotopic (U.trans d) := by
  let P := pathPrependReflHomotopy b b
  let R := pathAppendReflHomotopy b b
  let K := originalLoopTranslationFamily d
  let a := P.evalAt v
  let k := K.evalAt v
  let M := U.map (pathPrependRefl b b).continuous
  let p0 := P.evalAt (Path.refl b)
  let k0 := K.evalAt (Path.refl b)
  have hUId : U.map (ContinuousMap.id (LoopSpace B b)).continuous = U := Path.map_id U
  have hDId : d.map (ContinuousMap.id (LoopSpace B b)).continuous = d := Path.map_id d
  have hP := Path.Homotopic.map_trans_evalAt P U
  rw [hUId] at hP
  have hK := Path.Homotopic.map_trans_evalAt K U
  have hR := Path.Homotopic.map_trans_evalAt R d
  rw [hDId] at hR
  have hK0 : k0 = d.map (pathAppendRefl b b).continuous := by
    apply Path.ext
    funext s
    rfl
  have hP0 : p0 = R.evalAt (Path.refl b) := by
    apply Path.ext
    funext s
    exact (pathPrependReflHomotopy_refl b s).trans
      (pathAppendReflHomotopy_refl b s).symm
  have hUnit : (k0.trans p0).Homotopic (p0.trans d) := by
    rw [hK0, hP0]
    exact hR
  have hTrace : (originalLoopTranslationSelfHomotopy d).evalAt v =
      a.symm.trans (k.trans a) := by
    apply Path.ext
    funext s
    change (P.symm.trans (K.trans P)) (s, v) = (a.symm.trans (k.trans a)) s
    rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
    split
    · rfl
    · rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
      split <;> rfl
  rw [hTrace]
  have h1 : ((a.symm.trans (k.trans a)).trans U).Homotopic
      (a.symm.trans ((k.trans a).trans U)) :=
    Path.Homotopic.trans_assoc a.symm (k.trans a) U
  have h2 : (a.symm.trans ((k.trans a).trans U)).Homotopic
      (a.symm.trans (k.trans (a.trans U))) :=
    (Path.Homotopic.refl a.symm).hcomp (Path.Homotopic.trans_assoc k a U)
  have h3 : (a.symm.trans (k.trans (a.trans U))).Homotopic
      (a.symm.trans (k.trans (M.trans p0))) :=
    (Path.Homotopic.refl a.symm).hcomp ((Path.Homotopic.refl k).hcomp hP.symm)
  have h4 : (a.symm.trans (k.trans (M.trans p0))).Homotopic
      (a.symm.trans ((k.trans M).trans p0)) :=
    (Path.Homotopic.refl a.symm).hcomp (Path.Homotopic.trans_assoc k M p0).symm
  have h5 : (a.symm.trans ((k.trans M).trans p0)).Homotopic
      (a.symm.trans ((M.trans k0).trans p0)) :=
    (Path.Homotopic.refl a.symm).hcomp (hK.symm.hcomp (Path.Homotopic.refl p0))
  have h6 : (a.symm.trans ((M.trans k0).trans p0)).Homotopic
      (a.symm.trans (M.trans (k0.trans p0))) :=
    (Path.Homotopic.refl a.symm).hcomp (Path.Homotopic.trans_assoc M k0 p0)
  have h7 : (a.symm.trans (M.trans (k0.trans p0))).Homotopic
      (a.symm.trans (M.trans (p0.trans d))) :=
    (Path.Homotopic.refl a.symm).hcomp ((Path.Homotopic.refl M).hcomp hUnit)
  have h8 : (a.symm.trans (M.trans (p0.trans d))).Homotopic
      (a.symm.trans ((M.trans p0).trans d)) :=
    (Path.Homotopic.refl a.symm).hcomp (Path.Homotopic.trans_assoc M p0 d).symm
  have h9 : (a.symm.trans ((M.trans p0).trans d)).Homotopic
      (a.symm.trans ((a.trans U).trans d)) :=
    (Path.Homotopic.refl a.symm).hcomp (hP.hcomp (Path.Homotopic.refl d))
  have h10 : (a.symm.trans ((a.trans U).trans d)).Homotopic
      (a.symm.trans (a.trans (U.trans d))) :=
    (Path.Homotopic.refl a.symm).hcomp (Path.Homotopic.trans_assoc a U d)
  have h11 : (a.symm.trans (a.trans (U.trans d))).Homotopic
      ((a.symm.trans a).trans (U.trans d)) :=
    (Path.Homotopic.trans_assoc a.symm a (U.trans d)).symm
  have h12 : ((a.symm.trans a).trans (U.trans d)).Homotopic
      ((Path.refl v).trans (U.trans d)) :=
    (Path.Homotopic.symm_trans a).hcomp (Path.Homotopic.refl (U.trans d))
  have h13 : ((Path.refl v).trans (U.trans d)).Homotopic (U.trans d) :=
    Path.Homotopic.refl_trans (U.trans d)
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans
    (h7.trans (h8.trans (h9.trans (h10.trans (h11.trans (h12.trans h13)))))))))))

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

/-- The canonical loop unit is the EXACT original081 unit of the SAME139
weak Q map, with only the proved whole loop-map source equality as its cast. -/
public def originalConullScalarCanonicalLoopUnit :
    Path (mixedNQKSpaceMap F (Path.refl (NQReal.basepoint C))) (Path.refl (NQReal.basepoint D)) :=
  (ContinuousMap.WeaklyPointed.loopUnitRootPath (mixedNQWeaklyPointedMap F)).cast
    (congrArg (fun m => m (Path.refl (NQReal.basepoint C)))
      (mixedNQKSpaceMap_wholeWeak_value F)) rfl

private theorem originalConullScalarCanonicalLoopUnitValueComputed (s : unitInterval) :
    (originalConullScalarCanonicalLoopUnit F).toContinuousMap.toFun s =
      ContinuousMap.WeaklyPointed.loopUnitRootPath (mixedNQWeaklyPointedMap F) s := rfl

/-- Every canonical unit time is the SAME original081 weak Q-map unit time. -/
public theorem originalConullScalarCanonicalLoopUnit_value (s : unitInterval) :
    (originalConullScalarCanonicalLoopUnit F).toContinuousMap.toFun s =
      ContinuousMap.WeaklyPointed.loopUnitRootPath (mixedNQWeaklyPointedMap F) s := by
  exact originalConullScalarCanonicalLoopUnitValueComputed F s

private def originalScalarReturnUnitDefect :
    LoopSpace (NQKSpace D) (Path.refl (NQReal.basepoint D)) :=
  ((((originalConullScalarReturnHomotopy F).evalAt (Path.refl (NQReal.basepoint C))).trans
    (originalConullScalarCanonicalLoopUnit F)).symm.trans (originalConullScalarBetaReturnTrace F))

/-- The calibrated WHOLE return keeps original195 as its first family and
adds only an internally determined whole loop-translation self-homotopy. Both
original endpoint maps and every original loop component remain the same. -/
public def originalConullScalarCalibratedReturnHomotopy :
    ContinuousMap.Homotopy
      ((originalNQLoopPointHomeomorph D).symm.toHomotopyEquiv.toFun.comp
        ((((zeroOriginalHomotopyFiberToLoops (C := D)).hom.comp (mixedOriginalZeroFiberMap F)).comp
          (zeroLoopToOriginalHomotopyFiber (C := C)).hom).comp
            (originalNQLoopPointHomeomorph C).toHomotopyEquiv.toFun))
      (mixedNQKSpaceMap F) := by
  let J := (originalLoopTranslationSelfHomotopy (originalScalarReturnUnitDefect
      F)).compContinuousMap
    (mixedNQKSpaceMap F)
  have hEndpoint : (ContinuousMap.id (NQKSpace D)).comp (mixedNQKSpaceMap F) =
      mixedNQKSpaceMap F := by
    apply ContinuousMap.ext
    intro gamma
    rfl
  exact (originalConullScalarReturnHomotopy F).trans (J.cast hEndpoint hEndpoint)

private theorem originalConullScalarCalibratedReturnTraceValueComputed
    (x : NQKSpace C) :
    (originalConullScalarCalibratedReturnHomotopy F).evalAt x =
      ((originalConullScalarReturnHomotopy F).evalAt x).trans
        ((originalLoopTranslationSelfHomotopy (originalScalarReturnUnitDefect F)).evalAt
          (mixedNQKSpaceMap F x)) := by
  let t := (originalConullScalarReturnHomotopy F).evalAt x
  let d := originalScalarReturnUnitDefect F
  let J := originalLoopTranslationSelfHomotopy d
  have hEndpoint : (ContinuousMap.id (NQKSpace D)).comp (mixedNQKSpaceMap F) =
      mixedNQKSpaceMap F := by
    apply ContinuousMap.ext
    intro gamma
    rfl
  let K := (J.compContinuousMap (mixedNQKSpaceMap F)).cast hEndpoint hEndpoint
  apply Path.ext
  funext s
  change ((originalConullScalarReturnHomotopy F).trans K).toContinuousMap.toFun (s, x) =
    (t.trans (J.evalAt (mixedNQKSpaceMap F x))).toContinuousMap.toFun s
  have hLeft := ContinuousMap.Homotopy.trans_apply
    (X := NQKSpace C) (Y := NQKSpace D) (originalConullScalarReturnHomotopy F) K (s, x)
  have hRight := Path.trans_apply (X := NQKSpace D) t
    (J.evalAt (mixedNQKSpaceMap F x)) s
  refine hLeft.trans (Eq.trans ?_ hRight.symm)
  rfl

/-- The ACTUAL calibrated whole return trace followed by the EXACT original081
canonical Q-loop unit is endpoint-fixed homotopic to the literal189/188 betaFiber
conull trace. This is earned by the original unit rectangles and actual path
cancellation, with no stationarity or fundamental-group action assumption. -/
public theorem originalConullScalarCalibratedReturnHomotopy_OWNunit :
    (((originalConullScalarCalibratedReturnHomotopy F).evalAt
        (Path.refl (NQReal.basepoint C))).trans
      (originalConullScalarCanonicalLoopUnit F)).Homotopic
        (originalConullScalarBetaReturnTrace F) := by
  let x := Path.refl (NQReal.basepoint C)
  let v := mixedNQKSpaceMap F x
  let U := originalConullScalarCanonicalLoopUnit F
  let t := (originalConullScalarReturnHomotopy F).evalAt x
  let alpha := originalConullScalarBetaReturnTrace F
  let d := originalScalarReturnUnitDefect F
  let J := originalLoopTranslationSelfHomotopy d
  have hTrace : (originalConullScalarCalibratedReturnHomotopy F).evalAt x =
      t.trans (J.evalAt v) :=
    originalConullScalarCalibratedReturnTraceValueComputed F x
  have hUnit : ((J.evalAt v).trans U).Homotopic (U.trans d) :=
    originalLoopTranslationUnitRectangle d v U
  have hCancel : ((t.trans U).trans d).Homotopic alpha := by
    change ((t.trans U).trans ((t.trans U).symm.trans alpha)).Homotopic alpha
    exact (Path.Homotopic.trans_assoc (t.trans U) (t.trans U).symm alpha).symm.trans
      (((Path.Homotopic.trans_symm (t.trans U)).hcomp (Path.Homotopic.refl alpha)).trans
        (Path.Homotopic.refl_trans alpha))
  rw [hTrace]
  exact (Path.Homotopic.trans_assoc t (J.evalAt v) U).trans
    (((Path.Homotopic.refl t).hcomp hUnit).trans
      ((Path.Homotopic.trans_assoc t U d).symm.trans hCancel))

end AlgebraicKTheory.OriginalQZeroComparison

end


/-!
# Proper every-time values of the actual calibrated return

The full map and betaFiber getters retain the exact original195/189/191
families and the literal internally determined correction loop. They make
those actual values available to the completed-Core square without unfolding
an imported opaque construction.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits ContinuousMap
open AlgebraicKTheory.QuillenMixedUniverseTransport
open AlgebraicKTheory.OriginalQuillenUnliftedTransport
open scoped ZeroObject ContinuousMap Simplicial

universe uC vC uD vD

namespace AlgebraicKTheory.OriginalQZeroComparison

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

private theorem originalConullScalarBetaReturnTraceValueComputed (s : unitInterval) :
    (originalConullScalarBetaReturnTrace F).toContinuousMap.toFun s =
      (originalNQLoopPointHomeomorph D).symm
        (zeroOriginalHomotopyFiberToLoops (C := D) ((originalConullScalarBetaFiber
            F).toContinuousMap.toFun s)) := rfl

/-- Every actual beta-root time is the original conull return of the entire
literal fiber-root point, transported by the SAME original point inverse. -/
public theorem originalConullScalarBetaReturnTrace_value (s : unitInterval) :
    (originalConullScalarBetaReturnTrace F).toContinuousMap.toFun s =
      (originalNQLoopPointHomeomorph D).symm
        (zeroOriginalHomotopyFiberToLoops (C := D) ((originalConullScalarBetaFiber
            F).toContinuousMap.toFun s)) := by
  exact originalConullScalarBetaReturnTraceValueComputed F s

private theorem originalConullScalarCalibratedReturnHomotopyValueComputed
    (s : unitInterval) (gamma : NQKSpace C) :
    originalConullScalarCalibratedReturnHomotopy F (s, gamma) =
      if hs : (s : ℝ) ≤ 1 / 2 then
        originalConullScalarReturnHomotopy F
          (⟨2 * s, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩, gamma)
      else
        let t : unitInterval := ⟨2 * s - 1, unitInterval.two_mul_sub_one_mem_iff.2
          ⟨(not_le.1 hs).le, s.2.2⟩⟩
        let d := ((((originalConullScalarReturnHomotopy F).evalAt
            (Path.refl (NQReal.basepoint C))).trans
          (originalConullScalarCanonicalLoopUnit F)).symm.trans
            (originalConullScalarBetaReturnTrace F))
        if ht : (t : ℝ) ≤ 1 / 2 then
          pathPrependReflHomotopy (NQReal.basepoint D) (NQReal.basepoint D)
            (unitInterval.symm
              ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩,
                mixedNQKSpaceMap F gamma)
        else
          let u : unitInterval := ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 ht).le, t.2.2⟩⟩
          if hu : (u : ℝ) ≤ 1 / 2 then
            (d.toContinuousMap.toFun
              ⟨2 * u, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨u.2.1, hu⟩⟩).trans
              (mixedNQKSpaceMap F gamma)
          else
            pathPrependReflHomotopy (NQReal.basepoint D) (NQReal.basepoint D)
              (⟨2 * u - 1, unitInterval.two_mul_sub_one_mem_iff.2
                ⟨(not_le.1 hu).le, u.2.2⟩⟩, mixedNQKSpaceMap F gamma) := by
  let d := originalScalarReturnUnitDefect F
  have hEndpoint : (ContinuousMap.id (NQKSpace D)).comp (mixedNQKSpaceMap F) =
      mixedNQKSpaceMap F := by
    apply ContinuousMap.ext
    intro p
    rfl
  change ((originalConullScalarReturnHomotopy F).trans
    (((originalLoopTranslationSelfHomotopy d).compContinuousMap (mixedNQKSpaceMap F)).cast
      hEndpoint hEndpoint)) (s, gamma) = _
  rw [ContinuousMap.Homotopy.trans_apply]
  split
  · rfl
  · rename_i hs
    let t : unitInterval := ⟨2 * s - 1, unitInterval.two_mul_sub_one_mem_iff.2
      ⟨(not_le.1 hs).le, s.2.2⟩⟩
    let P : ContinuousMap.Homotopy
        (pathPrependRefl (NQReal.basepoint D) (NQReal.basepoint D))
        (ContinuousMap.id (NQKSpace D)) :=
      pathPrependReflHomotopy (NQReal.basepoint D) (NQReal.basepoint D)
    let K : ContinuousMap.Homotopy
        (pathPrependRefl (NQReal.basepoint D) (NQReal.basepoint D))
        (pathPrependRefl (NQReal.basepoint D) (NQReal.basepoint D)) :=
      originalLoopTranslationFamily d
    change (P.symm.trans (K.trans P)).toContinuousMap.toFun
      (t, mixedNQKSpaceMap F gamma) = _
    have hFirst := ContinuousMap.Homotopy.trans_apply
      (X := NQKSpace D) (Y := NQKSpace D) P.symm (K.trans P)
      (t, mixedNQKSpaceMap F gamma)
    refine hFirst.trans ?_
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · refine Eq.trans (dite_eq_left ht) (Eq.trans ?_ (dite_eq_left ht).symm)
      rfl
    · refine Eq.trans (dite_eq_right ht) (Eq.trans ?_ (dite_eq_right ht).symm)
      let u : unitInterval := ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2
        ⟨(not_le.1 ht).le, t.2.2⟩⟩
      change (K.trans P).toContinuousMap.toFun (u, mixedNQKSpaceMap F gamma) = _
      have hTail := ContinuousMap.Homotopy.trans_apply
        (X := NQKSpace D) (Y := NQKSpace D) K P (u, mixedNQKSpaceMap F gamma)
      refine hTail.trans ?_
      by_cases hu : (u : ℝ) ≤ 1 / 2
      · refine Eq.trans (dite_eq_left hu) (Eq.trans ?_ (dite_eq_left hu).symm)
        rfl
      · refine Eq.trans (dite_eq_right hu) (Eq.trans ?_ (dite_eq_right hu).symm)
        rfl

/-- EVERY original source loop and return-homotopy time keeps195 as its first
family and the literal difference-loop translation with the original prepend
unit framing as its second family, on the actual nested half clocks. -/
public theorem originalConullScalarCalibratedReturnHomotopy_value
    (s : unitInterval) (gamma : NQKSpace C) :
    originalConullScalarCalibratedReturnHomotopy F (s, gamma) =
      if hs : (s : ℝ) ≤ 1 / 2 then
        originalConullScalarReturnHomotopy F
          (⟨2 * s, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩, gamma)
      else
        let t : unitInterval := ⟨2 * s - 1, unitInterval.two_mul_sub_one_mem_iff.2
          ⟨(not_le.1 hs).le, s.2.2⟩⟩
        let d := ((((originalConullScalarReturnHomotopy F).evalAt
            (Path.refl (NQReal.basepoint C))).trans
          (originalConullScalarCanonicalLoopUnit F)).symm.trans
            (originalConullScalarBetaReturnTrace F))
        if ht : (t : ℝ) ≤ 1 / 2 then
          pathPrependReflHomotopy (NQReal.basepoint D) (NQReal.basepoint D)
            (unitInterval.symm
              ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩,
                mixedNQKSpaceMap F gamma)
        else
          let u : unitInterval := ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 ht).le, t.2.2⟩⟩
          if hu : (u : ℝ) ≤ 1 / 2 then
            (d.toContinuousMap.toFun
              ⟨2 * u, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨u.2.1, hu⟩⟩).trans
              (mixedNQKSpaceMap F gamma)
          else
            pathPrependReflHomotopy (NQReal.basepoint D) (NQReal.basepoint D)
              (⟨2 * u - 1, unitInterval.two_mul_sub_one_mem_iff.2
                ⟨(not_le.1 hu).le, u.2.2⟩⟩, mixedNQKSpaceMap F gamma) := by
  exact originalConullScalarCalibratedReturnHomotopyValueComputed F s gamma

end AlgebraicKTheory.OriginalQZeroComparison

end


/-!
# Calibrate designated roots in a genuine loop-space target

The starting whole homotopy is kept. Its actual selected-point trace and
both independently designated roots determine the literal correction
loop. The already constructed original prepend/append translation rectangle
and path cancellation earn the designated root law. The target is an actual
raw loop space; no property of a general target or root action is assumed.
-/

noncomputable section

open ContinuousMap
open scoped ContinuousMap

universe uLoopCalSource uLoopCalTarget

namespace AlgebraicKTheory.OriginalQZeroComparison

variable {X : Type uLoopCalSource} {Y : Type uLoopCalTarget}
  [TopologicalSpace X] [TopologicalSpace Y]
  {y : Y} {x : X} {f g : C(X, LoopSpace Y y)}

/-- Keep the actual whole homotopy and calibrate its two prescribed roots
in the original LOOP target by the literal unit-translation family. -/
public def loopTargetRootCalibratedHomotopy (H : ContinuousMap.Homotopy f g)
    (p : Path (f x) (Path.refl y)) (q : Path (g x) (Path.refl y)) :
    ContinuousMap.Homotopy f g := by
  let d := ((H.evalAt x).trans q).symm.trans p
  let J := (originalLoopTranslationSelfHomotopy d).compContinuousMap g
  have hEndpoint : (ContinuousMap.id (LoopSpace Y y)).comp g = g := by
    apply ContinuousMap.ext
    intro z
    rfl
  exact H.trans (J.cast hEndpoint hEndpoint)

private theorem loopTargetRootCalibratedHomotopyTraceValueComputed
    (H : ContinuousMap.Homotopy f g)
    (p : Path (f x) (Path.refl y)) (q : Path (g x) (Path.refl y)) :
    (loopTargetRootCalibratedHomotopy H p q).evalAt x =
      (H.evalAt x).trans
        ((originalLoopTranslationSelfHomotopy (((H.evalAt x).trans q).symm.trans p)).evalAt
          (g x)) := by
  let t := H.evalAt x
  let d := (t.trans q).symm.trans p
  let J := originalLoopTranslationSelfHomotopy d
  have hEndpoint : (ContinuousMap.id (LoopSpace Y y)).comp g = g := by
    apply ContinuousMap.ext
    intro z
    rfl
  let K := (J.compContinuousMap g).cast hEndpoint hEndpoint
  apply Path.ext
  funext s
  change (H.trans K).toContinuousMap.toFun (s, x) =
    (t.trans (J.evalAt (g x))).toContinuousMap.toFun s
  have hLeft := ContinuousMap.Homotopy.trans_apply
    (X := X) (Y := LoopSpace Y y) H K (s, x)
  have hRight := Path.trans_apply (X := LoopSpace Y y) t (J.evalAt (g x)) s
  refine hLeft.trans (Eq.trans ?_ hRight.symm)
  rfl

/-- The calibrated actual homotopy earns its prescribed ROOT relation from
original loop unit rectangles and genuine cancellation. No caller hRoot,
nullity of its correction loop, or fundamental-group action law is an input. -/
public theorem loopTargetRootCalibratedHomotopy_ROOT (H : ContinuousMap.Homotopy f g)
    (p : Path (f x) (Path.refl y)) (q : Path (g x) (Path.refl y)) :
    (((loopTargetRootCalibratedHomotopy H p q).evalAt x).trans q).Homotopic p := by
  let t := H.evalAt x
  let d := (t.trans q).symm.trans p
  let J := originalLoopTranslationSelfHomotopy d
  have hTrace : (loopTargetRootCalibratedHomotopy H p q).evalAt x =
      t.trans (J.evalAt (g x)) :=
    loopTargetRootCalibratedHomotopyTraceValueComputed H p q
  have hUnit : ((J.evalAt (g x)).trans q).Homotopic (q.trans d) :=
    originalLoopTranslationUnitRectangle d (g x) q
  have hCancel : ((t.trans q).trans d).Homotopic p :=
    (Path.Homotopic.trans_assoc (t.trans q) (t.trans q).symm p).symm.trans
      (((Path.Homotopic.trans_symm (t.trans q)).hcomp (Path.Homotopic.refl p)).trans
        (Path.Homotopic.refl_trans p))
  rw [hTrace]
  exact (Path.Homotopic.trans_assoc t (J.evalAt (g x)) q).trans
    (((Path.Homotopic.refl t).hcomp hUnit).trans
      ((Path.Homotopic.trans_assoc t q d).symm.trans hCancel))

end AlgebraicKTheory.OriginalQZeroComparison

end
