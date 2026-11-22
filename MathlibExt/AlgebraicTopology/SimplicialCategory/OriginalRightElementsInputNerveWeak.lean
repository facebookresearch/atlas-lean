/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightElementsInputEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSet.NerveULiftToTargetWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceHomotopyInvariance

/-!
# The SAME original right-elements input nerve map is weak

Both original full inverse input dictionaries and their actual
forward natural isomorphism retain every quotient map and operator.
Their nerve homotopy proves weakness of the SAME literal original
right-elements input functor, with no fibrancy or mapping outcome input.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalRawRightMapping

variable {K : SSet.{u}} (a b : (Δ[0] : SSet.{u}) ⟶ K)

/-- The SAME entire original right-elements input nerve map is weak by its actual complete inverse dictionaries. -/
theorem rightElementsInputFunctor_nerve_weak :
    SSet.realizationWeakEquivalences (nerveMap (rightElementsInputFunctor a b)) := by
  have hE := nerveMap_mem_realizationWeakEquivalences_of_isEquivalence (rightElementsInputEquivalence a b).functor
  have hN := NatTrans.nerveHomotopy (rightElementsInputEquivalenceReadback a b).hom
  exact (SSet.realizationWeakEquivalences_iff_of_homotopy hN).mp hE

/-- The SAME original right-elements input map is weak with its exact original contained coefficient lift. -/
theorem rightElementsInputFunctor_liftedNerve_weak :
    SSet.realizationWeakEquivalences (SSet.nerveMapULiftToTarget.{u,0,0,0} (rightElementsInputFunctor a b)) :=
  (SSet.nerveMapULiftToTarget_weak_iff (rightElementsInputFunctor a b)).mpr (rightElementsInputFunctor_nerve_weak a b)

end CategoryTheory.CoherentRealization.OriginalRawRightMapping
