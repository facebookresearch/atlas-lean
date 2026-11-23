/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.ZeroFiberLocalization
public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveEquivalenceWeakEquivalence

/-!
# The completed core and the literal localized zero fiber

The zero-row equivalence followed by the given-target fiber equivalence identifies the
completed core with the strict fiber of the original localized target over the zero object.
Its native up-nerve map is weak, with every denominator and independent Hom universe retained.
This map is the common target comparison in the two original zero-span pullback diagrams.
-/

universe u v

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ZeroObject

namespace AlgebraicKTheory.FixedTargetExtension

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] AlgebraicKTheory.ExtensionCategory.leftSumAction
attribute [local instance] AlgebraicKTheory.FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

/-- The original zero-row and strict-fiber equivalences give a weak native up map on all pairs. -/
theorem completedCoreToZeroFiberNerveMap_mem_realizationWeakEquivalences :
    SSet.realizationWeakEquivalences
      (nerveMapCommonHomUp.{u, max u v, 0}
        (zeroLocalizedFunctor (C := C) ⋙ localizedFiberFunctor (C := C) (0 : C))) := by
  let e : SInverse (Core C) (Core C) ≌ localizedFiber (C := C) (0 : C) :=
    (coreZeroLocalizedEquivalence (C := C)).trans
      (localizedFiberEquivalence (C := C) (0 : C))
  exact
    nerveMapCommonHomUp_mem_realizationWeakEquivalences_of_isEquivalence.{u, max u v, 0}
      e.functor

end AlgebraicKTheory.FixedTargetExtension

end
