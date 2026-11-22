/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightMappingReedyComparison

/-!
# The same original right-mapping replacement is weak

The actual Kan trivial fibration and the full original pointed Hom
isomorphism give the same generated replacement map to the original
right-mapping space. Every complete successor simplex is the literal
restriction along the generated pointed map.
-/

noncomputable section

universe u

open CategoryTheory Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace CategoryTheory.CoherentRealization.OriginalRawRightMapping

open OriginalFixedFrontContraction

variable {K : SSet.{u}} (a b : (Δ[0] : SSet.{u}) ⟶ K)

/-- The original generated replacement map to the same right-mapping space is a genuine Kan trivial fibration. -/
theorem reedyRightMappingComparison_trivialFibration [SSet.Quasicategory K] :
    trivialFibrations SSet.{u} (reedyRightMappingComparison a b) :=
  (trivialFibrations SSet.{u}).comp_mem _ _ (reedyHomComparison_trivialFibration a b)
    ((trivialFibrations SSet.{u}).of_isIso (pointedJoyalHomSpaceIso a b).inv)

/-- The same actual original replacement map is weak for its full quasicategory input. -/
theorem reedyRightMappingComparison_weak [SSet.Quasicategory K] :
    SSet.realizationWeakEquivalences (reedyRightMappingComparison a b) :=
  (reedyRightMappingComparison_trivialFibration a b).2

/-- Every full original successor readback restricts the same original quotient projection and generated Reedy map. -/
theorem reedyRightMappingComparison_successor (n : ℕ)
    (g : reedyReplacement.obj ⦋n⦌ ⟶ pointedCopyFunctor.obj (pointedInput a b)) :
    successor a b ((reedyRightMappingComparison a b).app (op ⦋n⦌) g) =
      FixedFrontCollapse.projection n ≫
        JoyalSSet.forget.map ((reedyReplacementMap.app ⦋n⦌ ≫ g).right) := by
  exact fromPointedMap_successor a b
    (pointedRawFunctor.map (reedyReplacementMap.app ⦋n⦌ ≫ g))

end CategoryTheory.CoherentRealization.OriginalRawRightMapping
