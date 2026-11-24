/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.Join

/-!
# Tests for the join of simplicial sets

Consumer checks for `SSet.join`: bifunctoriality and the `⋆` notation,
the computation on standard simplices (including a vertex count), and the
two-sided empty unit isomorphisms.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.JoinTest

/-- The join as an object, through the `⋆` notation. -/
example (X Y : SSet.{u}) : SSet.{u} := X ⋆ Y

example (X Y : SSet.{u}) : (SSet.join.obj X).obj Y = X ⋆ Y := rfl

/-- Functoriality in the right variable. -/
example {X Y Z : SSet.{u}} (f : Y ⟶ Z) : X ⋆ Y ⟶ X ⋆ Z :=
  (SSet.join.obj X).map f

/-- Functoriality in the left variable. -/
example {X Y Z : SSet.{u}} (f : X ⟶ Y) : X ⋆ Z ⟶ Y ⋆ Z :=
  (SSet.join.map f).app Z

/-- Joins of standard simplices. -/
example : Δ[0] ⋆ Δ[0] ≅ Δ[1] := SSet.joinStdSimplexIso 0 0

example : Δ[1] ⋆ Δ[2] ≅ Δ[4] := SSet.joinStdSimplexIso 1 2

example (m n : ℕ) : Δ[m] ⋆ Δ[n] ≅ Δ[m + n + 1] :=
  SSet.joinStdSimplexIso m n

/-- Vertex sanity check: `Δ[1] ⋆ Δ[1] ≅ Δ[3]` has four vertices. -/
def verticesEquivOneOne : (Δ[1] ⋆ Δ[1] : SSet.{u}) _⦋0⦌ ≃ Fin 4 :=
  (((CategoryTheory.evaluation SimplexCategoryᵒᵖ (Type u)).obj
    (Opposite.op ⦋0⦌)).mapIso (SSet.joinStdSimplexIso.{u} 1 1)).toEquiv.trans
    (SSet.stdSimplex.obj₀Equiv.{u} (n := 3))

/-- The empty simplicial set is a two-sided unit. -/
example (X : SSet.{u}) : (⊥_ SSet.{u}) ⋆ X ≅ X := SSet.botJoinIso X

example (X : SSet.{u}) : X ⋆ (⊥_ SSet.{u}) ≅ X := SSet.joinBotIso X

example : (⊥_ SSet.{u}) ⋆ Δ[2] ≅ Δ[2] := SSet.botJoinIso _

example : Δ[2] ⋆ (⊥_ SSet.{u}) ≅ Δ[2] := SSet.joinBotIso _

end MathlibExtTest.AlgebraicTopology.SimplicialSet.JoinTest
