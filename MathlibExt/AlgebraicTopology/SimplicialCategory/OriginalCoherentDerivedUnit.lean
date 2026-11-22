/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentQuillenAllSources
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentReplacementUnit

/-!
# The SAME original functorial coherent replacement unit is weak

The existing full original Bergner native functorial replacement and
its SAME inclusion give the already defined replacementUnit. The
proved all-source adjunct criterion proves that SAME entire natural
unit weak at every input. All original source maps and coefficient
maps stay fixed. No new replacement factory is introduced.
-/

noncomputable section

universe u

open CategoryTheory HomotopicalAlgebra

namespace CategoryTheory.CoherentRealization.OriginalQuillenComparison

open SimplicialEnrichment

attribute [local instance] JoyalSSet.modelCategory Bergner.modelCategory

/-- The SAME already defined full original natural replacement unit is genuinely categorical weak at EVERY original
simplicial set. -/
theorem replacementUnit_weak (K : SSet.{u}) : SSet.categoricalEquivalences (replacementUnit.app K) :=
  (allOriginalSource_unitNerve_weak_iff K (replacedRealization.obj K)
    (OriginalBergnerFibrantReplacement.homKan (realization K))
    (OriginalBergnerFibrantReplacement.inclusion.app (realization K))).mp
      (OriginalBergnerFibrantReplacement.inclusion_original_classes (realization K)).2

/-- The SAME original natural replacement unit is precisely the actual original coherent Hom adjunct of the SAME native
inclusion. -/
theorem replacementUnit_homEquiv (K : SSet.{u}) :
    coherentHomEquiv K (replacedRealization.obj K)
      (OriginalBergnerFibrantReplacement.inclusion.app (realization K)) = replacementUnit.app K := rfl

/-- The SAME full original replacement unit satisfies its exact original left-adjoint/counit factorization by the SAME
native inclusion. -/
theorem replacementUnit_counit (K : SSet.{u}) :
    realizationMap (replacementUnit.app K) ≫ counit (replacedRealization.obj K) =
      OriginalBergnerFibrantReplacement.inclusion.app (realization K) := by
  rw [← replacementUnit_homEquiv]
  exact (realizationAdjunction.homEquiv_counit (g := coherentHomEquiv K (replacedRealization.obj K)
    (OriginalBergnerFibrantReplacement.inclusion.app (realization K)))).symm.trans
      ((coherentHomEquiv K (replacedRealization.obj K)).symm_apply_apply
        (OriginalBergnerFibrantReplacement.inclusion.app (realization K)))

end CategoryTheory.CoherentRealization.OriginalQuillenComparison
