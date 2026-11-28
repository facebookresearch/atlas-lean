/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ProjectedShuffleBidegree

/-! # Tests for the projected shuffle sum at distinguished and off-diagonal cuts -/

open CategoryTheory MonoidalCategory Simplicial
open scoped BigOperators

namespace AlgebraicTopology.EilenbergZilber

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [(curriedTensor C).Additive] [∀ Z : C, ((curriedTensor C).obj Z).Additive]
  (X Y : SimplicialObject C)
  [HomologicalComplex.HasTensor
    ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
    ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)]

-- The interior cut retains exactly the block-shuffle value.
example : (∑ s : Shuffle 1 2, projectedShuffleAlexanderWhitneyTerm X Y 1 2 s 1) =
    projectedShuffleAlexanderWhitneyTerm X Y 1 2 (Shuffle.blockShuffle 1 2) 1 := by
  have h := ProjectedShuffleAlexanderWhitneyBidegreeIdentity X Y 1 2 1
  rw [ite_eq_left (show (1 : Fin 4) = ⟨1, by decide⟩ from rfl)] at h
  exact h.trans (ProjectedDistinguishedTermIdentity X Y 1 2).symm

-- With zero left degree, the cut at 1 is strictly after the distinguished cut.
example : (∑ s : Shuffle 0 2, projectedShuffleAlexanderWhitneyTerm X Y 0 2 s 1) = 0 := by
  simpa only [ite_eq_right (show (1 : Fin 3) ≠ ⟨0, by decide⟩ by decide)] using
    ProjectedShuffleAlexanderWhitneyBidegreeIdentity X Y 0 2 1

-- With zero right degree, the cut at 1 is strictly before the distinguished cut.
example : (∑ s : Shuffle 2 0, projectedShuffleAlexanderWhitneyTerm X Y 2 0 s 1) = 0 := by
  simpa only [ite_eq_right (show (1 : Fin 3) ≠ ⟨2, by decide⟩ by decide)] using
    ProjectedShuffleAlexanderWhitneyBidegreeIdentity X Y 2 0 1

end AlgebraicTopology.EilenbergZilber
