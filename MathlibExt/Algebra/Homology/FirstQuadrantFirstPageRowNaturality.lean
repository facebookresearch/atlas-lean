/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import
  MathlibExt.Algebra.Homology.Embedding.RestrictionHomology
public import MathlibExt.Algebra.Homology.FirstQuadrantSecondPageMap

/-!
# Naturality of fixed first-page rows

Let `f : K → L` be a map of first-quadrant bicomplexes in an abelian category. Its first-page
map restricts to the row with fixed vertical degree `q`, whose displayed degree `p` is
bidegree `(p,q)`.

The restricted maps preserve identity and composition. The homology comparison from a row to
the full first-page complex is natural for these maps.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- The fixed-row first-page map of a bicomplex morphism.

Restrict the first-page map along the embedding `p ↦ (p,q)` for a fixed vertical degree `q`. -/
noncomputable def horizontalFirstPageRowMapOfBicomplex
    (f : K ⟶ L) (q : ℕ) :
    horizontalFirstPageRowComplex K q ⟶
      horizontalFirstPageRowComplex L q :=
  HomologicalComplex.restrictionMap
    (horizontalPageMapOfBicomplex f 1 (le_refl 1))
    (horizontalFirstPageRowEmbedding q)

/-- The components of a restricted first-page row map.

The displayed degree-`p` component is the first-page map component at `(p,q)`. -/
@[simp]
theorem horizontalFirstPageRowMapOfBicomplex_f
    (f : K ⟶ L) (p q : ℕ) :
    (horizontalFirstPageRowMapOfBicomplex f q).f p =
      (horizontalPageMapOfBicomplex f 1 (le_refl 1)).f (p, q) :=
  rfl

/-- The identity map of a fixed first-page row.

The identity bicomplex map induces the identity on each restricted first-page row. -/
@[simp]
theorem horizontalFirstPageRowMapOfBicomplex_id
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (q : ℕ) :
    horizontalFirstPageRowMapOfBicomplex (𝟙 K) q = 𝟙 _ := by
  unfold horizontalFirstPageRowMapOfBicomplex
  rw [horizontalPageMapOfBicomplex_id]
  exact HomologicalComplex.restrictionMap_id _ _

/-- Composition of restricted first-page row maps.

The row map of a composite bicomplex morphism equals the composite of the row maps. -/
@[reassoc, simp]
theorem horizontalFirstPageRowMapOfBicomplex_comp
    (f : K ⟶ L) (g : L ⟶ M) (q : ℕ) :
    horizontalFirstPageRowMapOfBicomplex (f ≫ g) q =
      horizontalFirstPageRowMapOfBicomplex f q ≫
        horizontalFirstPageRowMapOfBicomplex g q := by
  unfold horizontalFirstPageRowMapOfBicomplex
  rw [horizontalPageMapOfBicomplex_comp]
  exact HomologicalComplex.restrictionMap_comp
    (φ := horizontalPageMapOfBicomplex f 1 (le_refl 1))
    (φ' := horizontalPageMapOfBicomplex g 1 (le_refl 1))
    (e := horizontalFirstPageRowEmbedding q)

/-- Naturality of the inverse first-page row-homology comparison.

The full first-page homology map at `(p,q)` commutes with the inverse comparison to row
homology and the degree-`p` row homology map. -/
@[reassoc]
theorem horizontalFirstPageRowHomologyIso_inv_naturality_of_bicomplex
    (f : K ⟶ L) (p q : ℕ) :
    HomologicalComplex.homologyMap
          (horizontalPageMapOfBicomplex f 1 (le_refl 1)) (p, q) ≫
        (horizontalFirstPageRowHomologyIso L p q).inv =
      (horizontalFirstPageRowHomologyIso K p q).inv ≫
        HomologicalComplex.homologyMap
          (horizontalFirstPageRowMapOfBicomplex f q) p := by
  let E := horizontalFirstPageRowEmbedding q
  let Pₖ := (horizontalFirstQuadrantSpectralSequence K).page 1
  let Pₗ := (horizontalFirstQuadrantSpectralSequence L).page 1
  let α := horizontalPageMapOfBicomplex f 1 (le_refl 1)
  have h := HomologicalComplex.restrictionHomologyIsoAt_inv_naturality
    (K := Pₖ) (L := Pₗ) E α p (E.prev_f rfl) (E.next_f rfl)
  change HomologicalComplex.homologyMap α (p, q) ≫
      (Pₗ.restrictionHomologyIsoAt E p
        (E.prev_f rfl) (E.next_f rfl)).inv =
    (Pₖ.restrictionHomologyIsoAt E p
      (E.prev_f rfl) (E.next_f rfl)).inv ≫
      HomologicalComplex.homologyMap
        (HomologicalComplex.restrictionMap α E) p
  simpa only [E, horizontalFirstPageRowEmbedding_f] using h

end HomologicalComplex₂

end
