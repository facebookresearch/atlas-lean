/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.CompletedZeroConullRootHomotopy

/-!
# Every-time formula for the actual original conull scalar selected-loop route

The original selected-loop inclusion, full mixed fiber map, and original
conull return retain their actual full maps. Their entire value is the
reverse original selected contraction, the mapped original loop and the
SAME canonical Q-zero root, with the original nested concatenation clocks.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalActionCategory
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal
  CategoryTheory.MonoidalCategory ContinuousMap Simplicial

attribute [local instance] AlgebraicKTheory.ExtensionCategory.leftSumAction
attribute [local instance] AlgebraicKTheory.FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

universe uC vC uD vD

namespace AlgebraicKTheory.OriginalQZeroComparison

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

omit [F.Additive] [F.IsExact] in
private theorem originalSelectedLoopTotal
    (gamma : LoopSpace (SSet.toTop.obj (nerve (QuillenQ C) : SSet.{max uC vC}))
      (zeroQVertex (C := C))) :
    TopCat.homotopyFiberToTotal
        (SSet.toTop.map (nerveMapCommonHom.{uC, max uC vC, 0}
          (ExtensionCategory.localizedTarget (C := C))))
        (zeroQVertex (C := C)) (zeroLoopToOriginalHomotopyFiber (C := C) gamma) =
      zeroTotalVertex (C := C) :=
  (TopCat.comp_app (zeroLoopToOriginalHomotopyFiber (C := C))
    (TopCat.homotopyFiberToTotal
      (SSet.toTop.map (nerveMapCommonHom.{uC, max uC vC, 0}
        (ExtensionCategory.localizedTarget (C := C)))) (zeroQVertex (C := C))) gamma).symm.trans
      (ConcreteCategory.congr_hom (zeroLoopToOriginalHomotopyFiber_toTotal (C := C)) gamma)

omit [F.Additive] [F.IsExact] in
private theorem originalSelectedLoopPath
    (gamma : LoopSpace (SSet.toTop.obj (nerve (QuillenQ C) : SSet.{max uC vC}))
      (zeroQVertex (C := C))) (s : unitInterval) :
    TopCat.homotopyFiberPath
        (SSet.toTop.map (nerveMapCommonHom.{uC, max uC vC, 0}
          (ExtensionCategory.localizedTarget (C := C))))
        (zeroQVertex (C := C)) (zeroLoopToOriginalHomotopyFiber (C := C) gamma)
        (TopCat.I.homeomorph.{max uC vC}.symm s) = gamma s := by
  have h := ConcreteCategory.congr_hom (zeroLoopToOriginalHomotopyFiber_path (C := C)) gamma
  have hs := congrArg (fun p => p (TopCat.I.homeomorph.{max uC vC}.symm s)) h
  change TopCat.homotopyFiberPath
      (SSet.toTop.map (nerveMapCommonHom.{uC, max uC vC, 0}
        (ExtensionCategory.localizedTarget (C := C))))
      (zeroQVertex (C := C)) (zeroLoopToOriginalHomotopyFiber (C := C) gamma)
      (TopCat.I.homeomorph.{max uC vC}.symm s) =
        gamma (TopCat.I.homeomorph.{max uC vC} (TopCat.I.homeomorph.{max uC vC}.symm s)) at hs
  exact hs.trans (congrArg gamma ((TopCat.I.homeomorph.{max uC vC}).apply_symm_apply s))

/-- EVERY original loop and EVERY time retain the literal original conull
return, mixed full-fiber map, mapped loop and canonical Q-root clocks. -/
public theorem originalConullScalar_selectedLoop_value
    (gamma : LoopSpace (SSet.toTop.obj (nerve (QuillenQ C) : SSet.{max uC vC}))
      (zeroQVertex (C := C))) (t : unitInterval) :
    zeroOriginalHomotopyFiberToLoops (C := D)
        (mixedOriginalZeroFiberMap F (zeroLoopToOriginalHomotopyFiber (C := C) gamma)) t =
      if ht : (t : ℝ) ≤ 1 / 2 then
        originalMixedConullNullHomotopy F
          (unitInterval.symm
            ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩,
              zeroTotalVertex (C := C))
      else
        let s : unitInterval := ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2
          ⟨(not_le.1 ht).le, t.2.2⟩⟩
        if hs : (s : ℝ) ≤ 1 / 2 then
          QuillenMixedUniverseTransport.mixedNQRealMap F
            (gamma ⟨2 * s, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩)
        else
          QuillenMixedUniverseTransport.mixedNQRootPath F
            ⟨2 * s - 1, unitInterval.two_mul_sub_one_mem_iff.2
              ⟨(not_le.1 hs).le, s.2.2⟩⟩ := by
  let K : SSet.{max uD vD} := nerve (ExtensionCategory.localizedExtensions (C := D))
  let x : K _⦋0⦌ := ComposableArrows.mk₀ (zeroFiberUnit (C := D)).val
  let p : SSet.toTop.obj K ⟶
      SSet.toTop.obj (nerve (QuillenQ D) : SSet.{max uD vD}) :=
    SSet.toTop.map (nerveMapCommonHom.{uD, max uD vD, 0}
      (ExtensionCategory.localizedTarget (C := D)))
  let z : TopCat.homotopyFiber p (zeroQVertex (C := D)) :=
    mixedOriginalZeroFiberMap F (zeroLoopToOriginalHomotopyFiber (C := C) gamma)
  have hReturnMap := congrArg
    (fun m : TopCat.homotopyFiber p (zeroQVertex (C := D)) ⟶
        TopCat.of (LoopSpace
          (SSet.toTop.obj (nerve (QuillenQ D) : SSet.{max uD vD}))
          (zeroQVertex (C := D))) => m z t)
    (zeroOriginalHomotopyFiberToLoops_eq_realizedConull (C := D))
  have hReturnValue := TopCat.homotopyFiberToLoopsOfRealizedConull_apply K x p
    (zeroQVertex (C := D)) (zeroTotalVertex_map (C := D))
    (originalLocalizedTotalTerminalWeak (C := D)) z t
  refine hReturnMap.trans (hReturnValue.trans ?_)
  split
  · rename_i ht
    have hTotal : TopCat.homotopyFiberToTotal p (zeroQVertex (C := D)) z =
        realizedNerveFunctorMap (ExtensionCategory.stabilizedFunctorMap F)
          (zeroTotalVertex (C := C)) :=
      (mixedOriginalZeroFiberMap_toTotal F
        (zeroLoopToOriginalHomotopyFiber (C := C) gamma)).trans
          (congrArg (realizedNerveFunctorMap (ExtensionCategory.stabilizedFunctorMap F))
            (originalSelectedLoopTotal gamma))
    have hCoordinate := congrArg
      (fun e : SSet.toTop.obj K => p
        ((SSet.basedContractionAtRealizedVertex K x
          (originalLocalizedTotalTerminalWeak (C := D))).homotopy.symm.toContinuousMap
          (⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩, e))) hTotal
    exact hCoordinate.trans (originalMixedConullNullHomotopy_value F
      (unitInterval.symm
        ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩)
      (zeroTotalVertex (C := C))).symm
  · rename_i ht
    let s : unitInterval := ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2
      ⟨(not_le.1 ht).le, unitInterval.le_one t⟩⟩
    have hPath :
        TopCat.homotopyFiberPath p (zeroQVertex (C := D)) z
            (TopCat.I.homeomorph.{max uD vD}.symm s) =
          if hs : (s : ℝ) ≤ 1 / 2 then
            QuillenMixedUniverseTransport.mixedNQRealMap F
              (TopCat.homotopyFiberPath
                (SSet.toTop.map (nerveMapCommonHom.{uC, max uC vC, 0}
                  (ExtensionCategory.localizedTarget (C := C))))
                (zeroQVertex (C := C)) (zeroLoopToOriginalHomotopyFiber (C := C) gamma)
                (TopCat.I.homeomorph.{max uC vC}.symm
                  ⟨2 * s, (unitInterval.mul_pos_mem_iff zero_lt_two).2
                    ⟨unitInterval.nonneg s, hs⟩⟩))
          else
            QuillenMixedUniverseTransport.mixedNQRootPath F
              ⟨2 * s - 1, unitInterval.two_mul_sub_one_mem_iff.2
                ⟨(not_le.1 hs).le, unitInterval.le_one s⟩⟩ := by
      have hActual := mixedOriginalZeroFiberMap_path F
        (zeroLoopToOriginalHomotopyFiber (C := C) gamma)
        (TopCat.I.homeomorph.{max uD vD}.symm s)
      rw [(TopCat.I.homeomorph.{max uD vD}).apply_symm_apply] at hActual
      exact hActual
    refine hPath.trans ?_
    split
    · rename_i hs
      let r : unitInterval := ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2
        ⟨(not_le.1 ht).le, t.2.2⟩⟩
      have hClock : r = s := by
        apply Subtype.ext
        rfl
      have hReadout := congrArg
        (fun v : unitInterval =>
          if hv : (v : ℝ) ≤ 1 / 2 then
            QuillenMixedUniverseTransport.mixedNQRealMap F
              (gamma ⟨2 * v, (unitInterval.mul_pos_mem_iff zero_lt_two).2
                ⟨unitInterval.nonneg v, hv⟩⟩)
          else
            QuillenMixedUniverseTransport.mixedNQRootPath F
              ⟨2 * v - 1, unitInterval.two_mul_sub_one_mem_iff.2
                ⟨(not_le.1 hv).le, unitInterval.le_one v⟩⟩) hClock
      have hMapped := congrArg (QuillenMixedUniverseTransport.mixedNQRealMap F)
        (originalSelectedLoopPath gamma
          (⟨2 * s, (unitInterval.mul_pos_mem_iff zero_lt_two).2
            ⟨unitInterval.nonneg s, hs⟩⟩ : unitInterval))
      exact hMapped.trans (hReadout.trans (dif_pos hs)).symm
    · rename_i hs
      let r : unitInterval := ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2
        ⟨(not_le.1 ht).le, t.2.2⟩⟩
      have hClock : r = s := by
        apply Subtype.ext
        rfl
      have hReadout := congrArg
        (fun v : unitInterval =>
          if hv : (v : ℝ) ≤ 1 / 2 then
            QuillenMixedUniverseTransport.mixedNQRealMap F
              (gamma ⟨2 * v, (unitInterval.mul_pos_mem_iff zero_lt_two).2
                ⟨unitInterval.nonneg v, hv⟩⟩)
          else
            QuillenMixedUniverseTransport.mixedNQRootPath F
              ⟨2 * v - 1, unitInterval.two_mul_sub_one_mem_iff.2
                ⟨(not_le.1 hv).le, unitInterval.le_one v⟩⟩) hClock
      exact (hReadout.trans (dif_neg hs)).symm

end AlgebraicKTheory.OriginalQZeroComparison

end
