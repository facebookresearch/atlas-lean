/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialAlexanderWhitney

/-! # Tests for the degreewise bisimplicial Alexander--Whitney map -/

@[expose] public section

open CategoryTheory Limits Simplicial
open scoped Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology.BisimplicialAlexanderWhitneyTests

variable {A : Type u} [Category.{v} A] [Preadditive A]
  [Limits.HasCountableCoproducts A]

example (n : ℕ) (p : Fin (n + 1)) :
    (p : ℕ) + BisimplicialAlexanderWhitney.cutComplement n p = n :=
  BisimplicialAlexanderWhitney.cut_add n p

example {p q n : ℕ} (h : p + q = n) :
    BisimplicialAlexanderWhitney.cutComplement n
      (⟨p, by omega⟩ : Fin (n + 1)) = q :=
  BisimplicialAlexanderWhitney.cutComplement_of_add_eq h

example (B : SimplicialObject (SimplicialObject A))
    (n : ℕ) (p : Fin (n + 1)) :
    (BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X n ⟶
      (B.obj (Opposite.op ⦋(p : ℕ)⦌)).obj
        (Opposite.op ⦋BisimplicialAlexanderWhitney.cutComplement n p⦌) :=
  BisimplicialAlexanderWhitney.faceToBidegree B n p

example (B : SimplicialObject (SimplicialObject A))
    (p q n : ℕ) (h : p + q = n) :
    (BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X n ⟶
      (B.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) :=
  BisimplicialAlexanderWhitney.faceToBidegreeOfEq B p q n h

example (B : SimplicialObject (SimplicialObject A))
    (n : ℕ) (p : Fin (n + 1)) :
    (BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X n ⟶
      (bisimplicialAlternatingTotalComplex A B).X n :=
  BisimplicialAlexanderWhitney.summand B n p

example (B : SimplicialObject (SimplicialObject A)) (n : ℕ) :
    (BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X n ⟶
      (bisimplicialAlternatingTotalComplex A B).X n :=
  BisimplicialAlexanderWhitney.component B n

example {B B' : SimplicialObject (SimplicialObject A)} (f : B ⟶ B')
    (n : ℕ) :
    ((alternatingFaceMapComplex A).map
      ((SimplicialObject.diagonalFunctor A).map f)).f n ≫
        BisimplicialAlexanderWhitney.component B' n =
      BisimplicialAlexanderWhitney.component B n ≫
        ((bisimplicialAlternatingTotalComplexFunctor A).map f).f n :=
  BisimplicialAlexanderWhitney.component_naturality f n

end AlgebraicTopology.BisimplicialAlexanderWhitneyTests

end
