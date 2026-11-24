/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.Algebra.Homology.Embedding.RestrictionHomology
public import MathlibExt.Algebra.Homology.FirstQuadrantSecondPageMap

/-!
# Naturality of restricted first-page rows

A bicomplex map on the first page restricts to every fixed vertical-degree
row.  The canonical comparison between row homology and full first-page
homology is natural for this restricted map.

This file contains no normalized-row, vertical-homology, successor-page,
second-page, or Bousfield--Kan comparison.
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

/-- The map between fixed first-page rows induced by a bicomplex map. -/
noncomputable def horizontalFirstPageRowMapOfBicomplex
    (f : K ⟶ L) (q : ℕ) :
    horizontalFirstPageRowComplex K q ⟶
      horizontalFirstPageRowComplex L q :=
  HomologicalComplex.restrictionMap
    (horizontalPageMapOfBicomplex f 1 (le_refl 1))
    (horizontalFirstPageRowEmbedding q)

/-- Components of the restricted row map are the corresponding page-one map
components. -/
@[simp]
theorem horizontalFirstPageRowMapOfBicomplex_f
    (f : K ⟶ L) (p q : ℕ) :
    (horizontalFirstPageRowMapOfBicomplex f q).f p =
      (horizontalPageMapOfBicomplex f 1 (le_refl 1)).f (p, q) :=
  rfl

@[simp]
theorem horizontalFirstPageRowMapOfBicomplex_id
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (q : ℕ) :
    horizontalFirstPageRowMapOfBicomplex (𝟙 K) q = 𝟙 _ := by
  unfold horizontalFirstPageRowMapOfBicomplex
  rw [horizontalPageMapOfBicomplex_id]
  exact HomologicalComplex.restrictionMap_id _ _

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

/-- Homology of a restricted first-page row is naturally identified with
homology of the full first page at the corresponding bidegree. -/
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
