/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ProjectedDistinguishedTerm

/-! # Tests for the projected block shuffle at the distinguished cut -/

open CategoryTheory MonoidalCategory Simplicial

namespace AlgebraicTopology.EilenbergZilber

open AlgebraicTopology.DoldKan (PInfty)

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [(curriedTensor C).Additive] [∀ Z : C, ((curriedTensor C).obj Z).Additive]
  (X Y : SimplicialObject C)
  [HomologicalComplex.HasTensor
    ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
    ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)]

private noncomputable abbrev normalizedInclusion (p q : ℕ) :=
  let K := (AlgebraicTopology.alternatingFaceMapComplex C).obj X
  let L := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y
  let P : K ⟶ K := PInfty
  let Q : L ⟶ L := PInfty
  HomologicalComplex.ιTensorObj K L p q (p + q) rfl ≫
    (HomologicalComplex.tensorHom (K₁ := K) (K₂ := L) (L₁ := K) (L₂ := L) P Q).f (p + q)

-- The distinguished cut is the first vertex when the left degree is zero.
example : projectedShuffleAlexanderWhitneyTerm X Y 0 2 (Shuffle.blockShuffle 0 2) 0 =
    normalizedInclusion X Y 0 2 :=
  ProjectedDistinguishedTermIdentity X Y 0 2

-- The distinguished cut is the last vertex when the right degree is zero.
example : projectedShuffleAlexanderWhitneyTerm X Y 2 0 (Shuffle.blockShuffle 2 0) 2 =
    normalizedInclusion X Y 2 0 :=
  ProjectedDistinguishedTermIdentity X Y 2 0

-- At an interior cut, the coproduct inclusion keeps the order of the two degrees.
example : projectedShuffleAlexanderWhitneyTerm X Y 1 2 (Shuffle.blockShuffle 1 2) 1 =
    normalizedInclusion X Y 1 2 :=
  ProjectedDistinguishedTermIdentity X Y 1 2

end AlgebraicTopology.EilenbergZilber
