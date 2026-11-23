/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.OriginalZeroHomotopyFiberSelectedPoint
public import MathlibExt.KTheory.Exact.Extension.OriginalZeroLoopHomotopyFiber

/-!
# The original completed-unit homotopy-fiber comparison is based

The actual K comparison sends the original positive image of the Core unit
to the independently constructed full homotopy-fiber point. Its original total
coordinate and its entire carried path determine this equality. The selected
point constructor is reused; no contraction or path-lifting data is supplied.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ZeroObject Simplicial

universe u v

namespace AlgebraicKTheory.OriginalQZeroComparison

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] ExtensionCategory.leftSumAction
attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction
attribute [local instance] ExtensionCategory.localizedTarget_isFibered

/-- The original unit maps to the independent actual selected total-and-constant-path point. -/
theorem completedCoreToOriginalHomotopyFiber_unit_selectedPoint :
    (TopCat.const
      (SSet.realizedVertex (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
        (ComposableArrows.mk₀
          ((SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C))))) :
      TopCat.of PUnit.{(max u v) + 1} ⟶
        SSet.toTop.obj (nerve (SInverse (Core C) (Core C)) : SSet.{max u v})) ≫
        completedCoreToOriginalHomotopyFiber (C := C) =
      TopCat.homotopyFiberSelectedPointMap
        (SSet.toTop.map
          (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
        (zeroTotalVertex (C := C)) (zeroQVertex (C := C)) (zeroTotalVertex_map (C := C)) := by
  apply TopCat.homotopyPullback_hom_ext
  · change ((TopCat.const
        (SSet.realizedVertex
          (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
          (ComposableArrows.mk₀
            ((SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C))))) :
        TopCat.of PUnit.{(max u v) + 1} ⟶ _) ≫
          completedCoreToOriginalHomotopyFiber (C := C)) ≫
        TopCat.homotopyFiberToTotal
          (SSet.toTop.map (nerveMapCommonHom.{u, max u v, 0}
            (ExtensionCategory.localizedTarget (C := C)))) (zeroQVertex (C := C)) =
      TopCat.homotopyFiberSelectedPointMap
          (SSet.toTop.map (nerveMapCommonHom.{u, max u v, 0}
            (ExtensionCategory.localizedTarget (C := C))))
          (zeroTotalVertex (C := C)) (zeroQVertex (C := C))
          (zeroTotalVertex_map (C := C)) ≫
        TopCat.homotopyFiberToTotal
          (SSet.toTop.map (nerveMapCommonHom.{u, max u v, 0}
            (ExtensionCategory.localizedTarget (C := C)))) (zeroQVertex (C := C))
    rw [TopCat.homotopyFiberSelectedPointMap_toTotal]
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    let a : SInverse (Core C) (Core C) :=
      (SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C))
    have hForget : (zeroFiberUnit (C := C)).val =
        (FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
          FixedTargetExtension.localizedForget (C := C) (0 : C)).obj a := by
      change (FixedTargetExtension.localizedFiberForget (C := C) (0 : C)).obj
          ((FixedTargetExtension.localizedFiberFunctor (C := C) (0 : C)).obj
            ((FixedTargetExtension.zeroLocalizedFunctor (C := C)).obj a)) =
        (FixedTargetExtension.localizedForget (C := C) (0 : C)).obj
          ((FixedTargetExtension.zeroLocalizedFunctor (C := C)).obj a)
      exact congrArg
        (fun T : FixedTargetExtension.localizedRows (C := C) (0 : C) ⥤
            ExtensionCategory.localizedExtensions (C := C) =>
          T.obj ((FixedTargetExtension.zeroLocalizedFunctor (C := C)).obj a))
        (FixedTargetExtension.localizedFiberFunctor_forget (C := C) (X := (0 : C)))
    have hTotal := completedCoreToOriginalHomotopyFiber_unit_toTotal (C := C)
    change TopCat.homotopyFiberToTotal
        (SSet.toTop.map (nerveMapCommonHom.{u, max u v, 0}
          (ExtensionCategory.localizedTarget (C := C)))) (zeroQVertex (C := C))
        (completedCoreToOriginalHomotopyFiber (C := C)
          (SSet.realizedVertex
            (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
            (ComposableArrows.mk₀ a))) =
      SSet.realizedVertex
        (X := (nerve (ExtensionCategory.localizedExtensions (C := C)) : SSet.{max u v}))
        (ComposableArrows.mk₀ (zeroFiberUnit (C := C)).val)
    exact hTotal.trans (congrArg
      (fun y : ExtensionCategory.localizedExtensions (C := C) =>
        SSet.realizedVertex
          (X := (nerve (ExtensionCategory.localizedExtensions (C := C)) : SSet.{max u v}))
          (ComposableArrows.mk₀ y)) hForget.symm)
  · exact TopCat.isTerminalPUnit.hom_ext _ _
  · change ((TopCat.const
        (SSet.realizedVertex
          (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
          (ComposableArrows.mk₀
            ((SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C))))) :
        TopCat.of PUnit.{(max u v) + 1} ⟶ _) ≫
          completedCoreToOriginalHomotopyFiber (C := C)) ≫
        TopCat.homotopyFiberPath
          (SSet.toTop.map (nerveMapCommonHom.{u, max u v, 0}
            (ExtensionCategory.localizedTarget (C := C)))) (zeroQVertex (C := C)) =
      TopCat.homotopyFiberSelectedPointMap
          (SSet.toTop.map (nerveMapCommonHom.{u, max u v, 0}
            (ExtensionCategory.localizedTarget (C := C))))
          (zeroTotalVertex (C := C)) (zeroQVertex (C := C))
          (zeroTotalVertex_map (C := C)) ≫
        TopCat.homotopyFiberPath
          (SSet.toTop.map (nerveMapCommonHom.{u, max u v, 0}
            (ExtensionCategory.localizedTarget (C := C)))) (zeroQVertex (C := C))
    rw [TopCat.homotopyFiberSelectedPointMap_path]
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    change TopCat.homotopyFiberPath
        (SSet.toTop.map (nerveMapCommonHom.{u, max u v, 0}
          (ExtensionCategory.localizedTarget (C := C)))) (zeroQVertex (C := C))
        (completedCoreToOriginalHomotopyFiber (C := C)
          (SSet.realizedVertex
            (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
            (ComposableArrows.mk₀
              ((SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C)))))) =
      ContinuousMap.const TopCat.I.{max u v} (zeroQVertex (C := C))
    exact completedCoreToOriginalHomotopyFiber_unit_path_eq_const (C := C)

end AlgebraicKTheory.OriginalQZeroComparison

end
