/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.IhomPrism

/-! # The prism dictionary for internal homs: tests

These tests exercise the public API of
`MathlibExt.AlgebraicTopology.SimplicialSet.IhomPrism`: the prism
dictionary (`ihomSimplexOfPrism`, `ihomPrismOfSimplex`,
`ihomSimplexEquiv`), faces, degeneracies, precomposition, degree-`0`
and endpoint formulas through the prism sections, composite-prism
endpoint restrictions, and edges determined by prisms.
-/

@[expose] public section

open CategoryTheory MonoidalClosed MonoidalCategory Limits Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet
namespace IhomPrismTest


variable {X C : SSet.{u}} {n : ℕ}

/-- The prism dictionary is a bijection, in both directions. -/
example (F : X ⊗ Δ[n] ⟶ C) :
    SSet.ihomPrismOfSimplex (SSet.ihomSimplexOfPrism F) = F :=
  SSet.ihomPrismOfSimplex_ihomSimplexOfPrism F

example (s : ((ihom X).obj C) _⦋n⦌) :
    SSet.ihomSimplexOfPrism (SSet.ihomPrismOfSimplex s) = s :=
  SSet.ihomSimplexOfPrism_ihomPrismOfSimplex s

example (F : X ⊗ Δ[n] ⟶ C) :
    (SSet.ihomSimplexEquiv X C n).symm (SSet.ihomSimplexEquiv X C n F) = F :=
  Equiv.symm_apply_apply _ _

example (s : ((ihom X).obj C) _⦋n⦌) :
    SSet.ihomSimplexEquiv X C n ((SSet.ihomSimplexEquiv X C n).symm s) = s :=
  Equiv.apply_symm_apply _ _

/-- Prism simplices are currying read through Yoneda. -/
example (F : X ⊗ Δ[n] ⟶ C) :
    SSet.ihomSimplexOfPrism F =
      SSet.yonedaEquiv (MonoidalClosed.curry F) :=
  rfl

/-- Faces and degeneracies of prism simplices are face and
degeneracy prisms. -/
example (F : X ⊗ Δ[n + 1] ⟶ C) (i : Fin (n + 2)) :
    ((ihom X).obj C).δ i (SSet.ihomSimplexOfPrism F) =
      SSet.ihomSimplexOfPrism ((X ◁ SSet.stdSimplex.δ i) ≫ F) :=
  SSet.δ_ihomSimplexOfPrism F i

example (F : X ⊗ Δ[n] ⟶ C) (i : Fin (n + 1)) :
    ((ihom X).obj C).σ i (SSet.ihomSimplexOfPrism F) =
      SSet.ihomSimplexOfPrism ((X ◁ SSet.stdSimplex.σ i) ≫ F) :=
  SSet.σ_ihomSimplexOfPrism F i

/-- Precomposition in the source variable is whiskering of prisms. -/
example {B : SSet.{u}} (f : B ⟶ X) (F : X ⊗ Δ[n] ⟶ C) :
    ((pre f).app C).app (op ⦋n⦌) (SSet.ihomSimplexOfPrism F) =
      SSet.ihomSimplexOfPrism ((f ▷ Δ[n]) ≫ F) :=
  SSet.ihomSimplexOfPrism_pre_app f F

/-- In degree `0` the prism dictionary is the vertex dictionary,
and the endpoints of a `Δ[1]` prism are its vertex restrictions. -/
example (F : X ⊗ Δ[0] ⟶ C) :
    SSet.ihomSimplexOfPrism F =
      SSet.ihomVertexEquiv X C (SSet.prismSectionZero X ≫ F) :=
  SSet.ihomSimplexOfPrism_zero F

example (F : X ⊗ Δ[1] ⟶ C) :
    ((ihom X).obj C).δ 1 (SSet.ihomSimplexOfPrism F) =
      SSet.ihomVertexEquiv X C
        (SSet.prismSectionZero X ≫ (X ◁ SSet.stdSimplex.δ 1) ≫ F) :=
  SSet.δ_one_ihomSimplexOfPrism F

example (F : X ⊗ Δ[1] ⟶ C) :
    ((ihom X).obj C).δ 0 (SSet.ihomSimplexOfPrism F) =
      SSet.ihomVertexEquiv X C
        (SSet.prismSectionZero X ≫ (X ◁ SSet.stdSimplex.δ 0) ≫ F) :=
  SSet.δ_zero_ihomSimplexOfPrism F

/-- Composite prisms have endpoint restrictions through the sections
at the vertices of `Δ[1]`. -/
example {Y : SSet.{u}} (Ψ : X ⊗ Δ[1] ⟶ Y) (P : Y ⟶ C) :
    ((ihom X).obj C).δ 1 (SSet.ihomSimplexOfPrism (Ψ ≫ P)) =
      SSet.ihomVertexEquiv X C ((SSet.prismSectionAt X 0 ≫ Ψ) ≫ P) :=
  SSet.δ_one_ihomSimplexOfPrism_comp Ψ P

example {Y : SSet.{u}} (Ψ : X ⊗ Δ[1] ⟶ Y) (P : Y ⟶ C) :
    ((ihom X).obj C).δ 0 (SSet.ihomSimplexOfPrism (Ψ ≫ P)) =
      SSet.ihomVertexEquiv X C ((SSet.prismSectionAt X 1 ≫ Ψ) ≫ P) :=
  SSet.δ_zero_ihomSimplexOfPrism_comp Ψ P

/-- The first-projection prism is the degenerate simplex at a vertex. -/
example (g : X ⟶ C) :
    SSet.ihomSimplexOfPrism
        (CartesianMonoidalCategory.fst X Δ[1] ≫ g) =
      ((ihom X).obj C).σ 0 (SSet.ihomVertexEquiv X C g) :=
  SSet.ihomSimplexOfPrism_fst g

/-- Edges from prisms have the prism simplex as underlying simplex. -/
example (F : X ⊗ Δ[1] ⟶ C) {x₀ x₁ : ((ihom X).obj C) _⦋0⦌}
    (h₀ : ((ihom X).obj C).δ 1 (SSet.ihomSimplexOfPrism F) = x₀)
    (h₁ : ((ihom X).obj C).δ 0 (SSet.ihomSimplexOfPrism F) = x₁) :
    (SSet.edgeOfPrism F h₀ h₁).edge = SSet.ihomSimplexOfPrism F :=
  rfl


/-- The second-component whiskering simp lemma, exercised through
`simp`. -/
example {X Y L : SSet.{u}} (f : X ⟶ Y) {Δ : SimplexCategoryᵒᵖ}
    (z : (X ⊗ L).obj Δ) : ((f ▷ L).app Δ z).2 = z.2 := by
  simp

/-- The edge of a prism edge is the prism simplex, exercised through
`SSet.edgeOfPrism_edge`. -/
example {X C : SSet.{u}} (F : X ⊗ Δ[1] ⟶ C)
    {x₀ x₁ : ((ihom X).obj C) _⦋0⦌}
    (h₀ : ((ihom X).obj C).δ 1 (SSet.ihomSimplexOfPrism F) = x₀)
    (h₁ : ((ihom X).obj C).δ 0 (SSet.ihomSimplexOfPrism F) = x₁) :
    (SSet.edgeOfPrism F h₀ h₁).edge = SSet.ihomSimplexOfPrism F := by
  simp

/-- The section at vertex `0` is `prismSectionZero`. -/
example (X : SSet.{u}) :
    SSet.prismSectionAt X (0 : Fin 1) = SSet.prismSectionZero X :=
  SSet.prismSectionAt_zero X

end IhomPrismTest
end MathlibExtTest.AlgebraicTopology.SimplicialSet
