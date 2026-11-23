/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.Monoidal.CoreAdditivePairBasedRealization
import MathlibExt.Algebra.Category.FGProjectiveCat.Basic

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CoreLocalizationComparison
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped ContinuousMap CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ZeroObject

attribute [local instance] MonoidalActionCategory.diagonalAction

universe u v

example {C : Type u} [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] :
    let X := SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))
    let Y := SSet.toTop.obj (nerve (SInverseS.Pair C))
    let x := SSet.realizedVertex (X := nerve (SInverse (Core C) (Core C)))
      (ComposableArrows.mk₀ ((SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C))))
    let y := SSet.realizedVertex (X := nerve (SInverseS.Pair C))
      (ComposableArrows.mk₀ (⟨0, 0⟩ : SInverseS.Pair C))
    let f := SSet.toTop.map (nerveMap (coreAdditivePairEquivalence (C := C)).functor)
    ∃ e : X ≃ₕ Y, e.toFun = f.hom ∧ e.toFun x = y ∧ e.invFun y = x ∧
      Nonempty (ContinuousMap.HomotopyRel (e.invFun.comp e.toFun) (ContinuousMap.id X) {x}) ∧
      Nonempty (ContinuousMap.HomotopyRel (e.toFun.comp e.invFun) (ContinuousMap.id Y) {y}) :=
  coreAdditivePairRealizationBasedEquivalence_exists (C := C)

example (R : Type u) [Ring R] :
    (SSet.toTop.map (nerveMap
      (coreAdditivePairEquivalence (C := FGProjectiveCat.{max u v} R)).functor))
      (SSet.realizedVertex (X := nerve (SInverse (Core (FGProjectiveCat.{max u v} R))
        (Core (FGProjectiveCat.{max u v} R)))) (ComposableArrows.mk₀
        ((SInverse.inclusion (Core (FGProjectiveCat.{max u v} R))
          (Core (FGProjectiveCat.{max u v} R))).obj
            (𝟙_ (Core (FGProjectiveCat.{max u v} R)))))) =
      SSet.realizedVertex (X := nerve (SInverseS.Pair (FGProjectiveCat.{max u v} R)))
        (ComposableArrows.mk₀
        (⟨0, 0⟩ : SInverseS.Pair (FGProjectiveCat.{max u v} R))) :=
  coreAdditivePairRealization_unit (C := FGProjectiveCat.{max u v} R)

end
