/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialAlexanderWhitney.Crossover

/-! # Tests for the bisimplicial Alexander--Whitney crossover -/

@[expose] public section

open CategoryTheory Simplicial
open scoped Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology.BisimplicialAlexanderWhitneyCrossoverTests

variable {A : Type u} [Category.{v} A] [Preadditive A]

example (B : SimplicialObject (SimplicialObject A))
    (p q n : ℕ) (h : p + q = n) :
    BisimplicialAlexanderWhitney.faceToBidegreeOfEq B
        (p + 1) q (n + 1) (by omega) ≫
      (B.δ (⟨p + 1, by omega⟩ : Fin (p + 2))).app
        (Opposite.op ⦋q⦌) =
    BisimplicialAlexanderWhitney.faceToBidegreeOfEq B
        p (q + 1) (n + 1) (by omega) ≫
      (B.obj (Opposite.op ⦋p⦌)).δ
        (⟨0, by omega⟩ : Fin (q + 2)) :=
  BisimplicialAlexanderWhitney.crossover_face_eq B p q n h

end AlgebraicTopology.BisimplicialAlexanderWhitneyCrossoverTests

end
