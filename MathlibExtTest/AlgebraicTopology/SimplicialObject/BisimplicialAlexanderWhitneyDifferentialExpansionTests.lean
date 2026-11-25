/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialAlexanderWhitney.DifferentialExpansion

/-! # Tests for bisimplicial Alexander--Whitney differential expansions -/

@[expose] public section

open CategoryTheory Limits Simplicial
open scoped Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology.BisimplicialAlexanderWhitneyDifferentialExpansionTests

variable {A : Type u} [Category.{v} A] [Preadditive A]
  [Limits.HasCountableCoproducts A]

example (B : SimplicialObject (SimplicialObject A))
    (n : ℕ) (i : Fin (n + 2)) :
    ((SimplicialObject.diagonalFunctor A).obj B).δ i =
      (B.obj (Opposite.op ⦋n + 1⦌)).δ i ≫
        (B.δ i).app (Opposite.op ⦋n⦌) :=
  BisimplicialAlexanderWhitney.diagonal_δ B n i

#check BisimplicialAlexanderWhitney.totalιOfEq_comp_d
#check BisimplicialAlexanderWhitney.component_comp_total_d_eq_bidegree_sum
#check BisimplicialAlexanderWhitney.diagonal_d_comp_component_eq_double_sum

end AlgebraicTopology.BisimplicialAlexanderWhitneyDifferentialExpansionTests

end
