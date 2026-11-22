/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.MappingSpaceKanW

/-!
# Right mapping spaces of a quasicategory are Kan: tests

These tests exercise the public API of
`MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.MappingSpaceKanW`:
naturality of `SSet.joinStdSimplexIso` in the left variable; the
transported endpoint identifications (`SSet.frontInclusion` is
the last face map; the right-vertex face relation
`SSet.rightVertex_comp_δ_castSucc`); the simplex-category
computations for `inl'`/`inr'`/`tensorHomOf` at `⦋0⦌`; the face
transport `SSet.mappingSpaceRight.simplexEquivSucc_δ`; and the
main theorem `SSet.kanComplex_mappingSpaceRight` (with its
instance form), at an arbitrary universe and at universe `0`,
including nerves of categories.

The unconditional target `SSet.KanComplex.W
(SSet.mappingSpaceRight.map X a b f)` for a categorical
equivalence between quasicategories is not tested here: it
remains blocked on step (3) of the additional comparison obligation
(the positive-`πₙ` identification; steps (1) and (2) — the
right-vertex and `π₀` identifications — are closed), as
recorded in the main file.
the additional comparison obligation itself is closed and is exercised below.
-/

@[expose] public section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace SSet

/-- Definitive name, signature, and statement of naturality of
`joinStdSimplexIso` in the left variable. -/
example {m m' n : ℕ} (φ : ⦋m⦌ ⟶ ⦋m'⦌) :
    (join.{u}.map (SSet.stdSimplex.map φ)).app (Δ[n] : SSet.{u}) ≫
        (joinStdSimplexIso.{u} m' n).hom =
      (joinStdSimplexIso.{u} m n).hom ≫
        SSet.stdSimplex.map
          (AugmentedSimplexCategory.tensorHomOf φ (𝟙 ⦋n⦌)) :=
  joinStdSimplexIso_natural_left φ

/-- The simplex-category computation `inl' ⦋n⦌ ⦋0⦌ = δ_last`. -/
example (n : ℕ) :
    AugmentedSimplexCategory.inl' ⦋n⦌ ⦋0⦌ =
      SimplexCategory.δ (Fin.last (n + 1)) :=
  inl'_eq_δ_last n

/-- Tensoring a face map with the identity on `⦋0⦌`. -/
example {n : ℕ} (j : Fin (n + 2)) :
    AugmentedSimplexCategory.tensorHomOf (SimplexCategory.δ j)
        (𝟙 ⦋0⦌) =
      SimplexCategory.δ j.castSucc :=
  tensorHomOf_δ_id j

/-- The transported left endpoint inclusion on standard
simplices is `SSet.stdSimplex.map` of `inl'`. -/
example (m n : ℕ) :
    joinInl (Δ[m] : SSet.{u}) (Δ[n] : SSet.{u}) ≫
        (joinStdSimplexIso.{u} m n).hom =
      SSet.stdSimplex.map (AugmentedSimplexCategory.inl' ⦋m⦌ ⦋n⦌) :=
  joinInl_comp_joinStdSimplexIso_hom m n

/-- `frontInclusion` is the last face map. -/
example (n : ℕ) :
    frontInclusion.{u} n = stdSimplex.δ (Fin.last (n + 1)) :=
  frontInclusion_eq n

/-- The right-vertex face relation. -/
example {n : ℕ} (j : Fin (n + 2)) :
    rightVertex.{u} n ≫ stdSimplex.δ j.castSucc =
      rightVertex.{u} (n + 1) :=
  rightVertex_comp_δ_castSucc j

/-- Face transport for simplices of the right mapping space. -/
example {X : SSet.{u}} (x y : (Δ[0] : SSet.{u}) ⟶ X) {k : ℕ}
    (σ : (mappingSpaceRight X x y).obj (op ⦋k + 1⦌))
    (a : Fin (k + 2)) :
    ((mappingSpaceRight.simplexEquivSucc X x y k)
        ((mappingSpaceRight X x y).δ a σ)).1 =
      stdSimplex.δ a.castSucc ≫
        ((mappingSpaceRight.simplexEquivSucc X x y (k + 1)) σ).1 :=
  mappingSpaceRight.simplexEquivSucc_δ x y σ a

/-- The `${(0,1)}$`-edge of `Δ[n + 2]` factors through the
front face. -/
example (n : ℕ) :
    (stdSimplex.edge.{u} (n + 1) 0 ⟨1, by omega⟩ (by simp)).down ≫
        SimplexCategory.δ (Fin.last (n + 2)) =
      (stdSimplex.edge.{u} (n + 2) 0 ⟨1, by omega⟩ (by simp)).down :=
  mappingSpaceRight.edge01_comp_δ_last n

/-- Headline theorem (the additional comparison obligation): right mapping spaces of a
quasicategory are Kan complexes. -/
example (X : SSet.{u}) [Quasicategory X]
    (x y : (Δ[0] : SSet.{u}) ⟶ X) :
    KanComplex (mappingSpaceRight X x y) :=
  kanComplex_mappingSpaceRight X x y

/-- The instance form is found by typeclass search. -/
example (X : SSet.{u}) [Quasicategory X]
    (x y : (Δ[0] : SSet.{u}) ⟶ X) :
    KanComplex (mappingSpaceRight X x y) := inferInstance

/-- At universe `0`. -/
example (X : SSet.{0}) [Quasicategory X]
    (x y : (Δ[0] : SSet.{0}) ⟶ X) :
    KanComplex (mappingSpaceRight X x y) :=
  kanComplex_mappingSpaceRight X x y

/-- For nerves of categories: right mapping spaces between any
two vertices are Kan (in fact discrete). -/
example (C : Type) [Category C]
    (x y : (Δ[0] : SSet.{0}) ⟶ nerve.{0, 0} C) :
    KanComplex (mappingSpaceRight (nerve.{0, 0} C) x y) :=
  kanComplex_mappingSpaceRight _ _ _

end SSet
