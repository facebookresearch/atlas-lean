/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.LocalizedMiddleWeakEquivalence

/-!
# Whole-space consumers of the original middle comparison

The constructed homotopy equivalences have the literal middle projection and
split-middle composite as their forward maps. The original quotient and all
components are retained, at independent ring and module universes.
-/

universe uRing vModule

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open AlgebraicKTheory.FixedTargetExtension AlgebraicKTheory.FixedTargetExtension.SplitInclusion
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory

namespace MathlibExtTest.CompletedMiddleWeakEquivalence

attribute [local instance] AlgebraicKTheory.FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

/-- The realized equivalence keeps the actual whole middle projection as its forward map. -/
theorem actual_middle_forward_has_whole_space_inverse
    {R : Type uRing} [Ring R] (X : FGProjectiveCat.{vModule} R) :
    ∃ e : ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj (nerve (localizedRows (C := FGProjectiveCat.{vModule} R) X)))
      (SSet.toTop.obj (nerve (SInverse (Core (FGProjectiveCat.{vModule} R))
        (Core (FGProjectiveCat.{vModule} R))))),
      e.toFun = (SSet.toTop.map (nerveMapCommonHom.{max uRing (vModule + 1), max uRing (vModule +
        1), 0} (localizedMiddleFunctor X))).hom := by
  let beta := nerveMapCommonHom.{max uRing (vModule + 1), max uRing (vModule + 1), 0}
    (localizedMiddleFunctor X)
  have hBeta := projectiveLocalizedMiddleNerveMap_mem_realizationWeakEquivalences X
  refine ⟨SSet.RealizationCWUpgrade.realizationHomotopyEquiv beta hBeta, ?_⟩
  exact SSet.RealizationCWUpgrade.realizationHomotopyEquiv_toFun beta hBeta

/-- The realized equivalence uses the actual positive-shift composite on every component. -/
theorem actual_split_middle_forward_has_whole_space_inverse
    {R : Type uRing} [Ring R] (X : FGProjectiveCat.{vModule} R) :
    ∃ e : ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj (nerve (SInverse (Core (FGProjectiveCat.{vModule} R))
        (Core (FGProjectiveCat.{vModule} R)))))
      (SSet.toTop.obj (nerve (SInverse (Core (FGProjectiveCat.{vModule} R))
        (Core (FGProjectiveCat.{vModule} R))))),
      e.toFun = (SSet.toTop.map
        (nerveMapCommonHomUp.{max uRing (vModule + 1), max uRing (vModule + 1), 0}
          (splitLocalizedFunctor X) ≫
          nerveMapCommonHom.{max uRing (vModule + 1), max uRing (vModule + 1), 0}
            (localizedMiddleFunctor X))).hom := by
  let q := nerveMapCommonHomUp.{max uRing (vModule + 1), max uRing (vModule + 1), 0}
    (splitLocalizedFunctor X) ≫
    nerveMapCommonHom.{max uRing (vModule + 1), max uRing (vModule + 1), 0} (localizedMiddleFunctor
      X)
  have hQ := splitMiddleCompositeNerveMap_mem_realizationWeakEquivalences X
  refine ⟨SSet.RealizationCWUpgrade.realizationHomotopyEquiv q hQ, ?_⟩
  exact SSet.RealizationCWUpgrade.realizationHomotopyEquiv_toFun q hQ

end MathlibExtTest.CompletedMiddleWeakEquivalence

end
