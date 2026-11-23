/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.KTheory.Exact.Extension.OriginalZeroHomotopyFiberBasedComparison
import MathlibExt.KTheory.Exact.Extension.OriginalZeroHomotopyFiberLoopEquivalence

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory Opposite
open AlgebraicKTheory
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ZeroObject Simplicial

universe u v uRing vModule

section
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] ExtensionCategory.leftSumAction
attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction
attribute [local instance] ExtensionCategory.localizedTarget_isFibered

open AlgebraicKTheory.OriginalQZeroComparison
#check AlgebraicKTheory.OriginalQZeroComparison.completedCoreToOriginalHomotopyFiber_unit_selectedPoint
#print axioms AlgebraicKTheory.OriginalQZeroComparison.completedCoreToOriginalHomotopyFiber_unit_selectedPoint


example :
    completedCoreToOriginalHomotopyFiber (C := C)
        (SSet.realizedVertex (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
          (ComposableArrows.mk₀
            ((SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C))))) =
      TopCat.homotopyFiberSelectedPointMap
        (SSet.toTop.map (nerveMapCommonHom.{u, max u v, 0}
          (ExtensionCategory.localizedTarget (C := C))))
        (zeroTotalVertex (C := C)) (zeroQVertex (C := C))
        (zeroTotalVertex_map (C := C)) PUnit.unit :=
  ConcreteCategory.congr_hom
    (completedCoreToOriginalHomotopyFiber_unit_selectedPoint (C := C)) PUnit.unit

example :
    TopCat.homotopyFiberPath
      (SSet.toTop.map (nerveMapCommonHom.{u, max u v, 0}
        (ExtensionCategory.localizedTarget (C := C)))) (zeroQVertex (C := C))
      (completedCoreToOriginalHomotopyFiber (C := C)
        (SSet.realizedVertex (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
          (ComposableArrows.mk₀
            ((SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C)))))) =
      ContinuousMap.const TopCat.I.{max u v} (zeroQVertex (C := C)) :=
  completedCoreToOriginalHomotopyFiber_unit_path_eq_const (C := C)

example (t : TopCat.I.{max u v}) :
    TopCat.homotopyFiberPath
      (SSet.toTop.map (nerveMapCommonHom.{u, max u v, 0}
        (ExtensionCategory.localizedTarget (C := C)))) (zeroQVertex (C := C))
      (completedCoreToOriginalHomotopyFiber (C := C)
        (SSet.realizedVertex (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
          (ComposableArrows.mk₀
            ((SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C)))))) t =
      zeroQVertex (C := C) :=
  completedCoreToOriginalHomotopyFiber_unit_path_apply (C := C) t

example :
    (TopCat.const
      (SSet.realizedVertex (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
        (ComposableArrows.mk₀
          ((SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C))))) :
      TopCat.of PUnit.{(max u v) + 1} ⟶
        SSet.toTop.obj (nerve (SInverse (Core C) (Core C)) : SSet.{max u v})) ≫
        (completedCoreToOriginalHomotopyFiber (C := C) ≫
          zeroOriginalHomotopyFiberToLoops (C := C)) =
      TopCat.const (Path.refl (zeroQVertex (C := C))) := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g => g ≫ zeroOriginalHomotopyFiberToLoops (C := C))
      (completedCoreToOriginalHomotopyFiber_unit_selectedPoint (C := C))).trans
      (zeroOriginalHomotopyFiberToLoops_selectedPoint (C := C)))

example {R : Type uRing} [Ring R] : TopCat.weakHomotopyEquivalences
    (completedCoreToOriginalHomotopyFiber (C := FGProjectiveCat.{vModule} R) ≫
      zeroOriginalHomotopyFiberToLoops (C := FGProjectiveCat.{vModule} R)) := by
  have hBase : ∀ X : FGProjectiveCat.{vModule} R, TopCat.weakHomotopyEquivalences
      (terminal.from (SSet.toTop.obj
        (nerve (MonoidalActionCategory (Core (FGProjectiveCat.{vModule} R))
          (FixedTargetExtension (FGProjectiveCat.{vModule} R) X)) :
            SSet.{max uRing (vModule + 1)}))) := by
    intro X
    exact AuxiliaryExtension.projectiveAuxiliary_realization_conull X
  have hκ : TopCat.weakHomotopyEquivalences
      (completedCoreToOriginalHomotopyFiber (C := FGProjectiveCat.{vModule} R)) :=
    completedCoreToOriginalHomotopyFiber_mem_of_originalBases_conull
      (C := FGProjectiveCat.{vModule} R) hBase
  exact TopCat.weakHomotopyEquivalences.comp_mem _ _ hκ
    (projectiveOriginalHomotopyFiberToLoops_mem (R := R))

end
