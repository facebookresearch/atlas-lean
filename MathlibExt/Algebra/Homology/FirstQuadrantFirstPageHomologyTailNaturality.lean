/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantFirstPageComparisonNaturality
public import
  MathlibExt.Algebra.Homology.FirstQuadrantFirstPageRowNaturality

/-!
# First-page homology and horizontal homology of vertical columns

Let `K` be a first-quadrant bicomplex in an abelian category. Restrict the first page to the
row of vertical degree `q`. The row homology comparison and normalized row-complex isomorphism
identify homology of the first page at `(p,q)` with `H_p(H_q^{vertical}(K))`.

The comparison is natural in bicomplex maps, using the restricted first-page row map and the
horizontal complex of column vertical-homology maps.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- The horizontal-of-vertical comparison for first-page homology.

Compose the inverse row-restriction homology comparison with homology of the normalized row-
complex isomorphism to identify first-page homology at `(p,q)` with
`H_p(K.verticalHomologyComplex q)`. -/
noncomputable def horizontalFirstPageHomologyVerticalHorizontalHomologyIso
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page 1
      (le_refl 1)).homology (p, q) ≅
      (K.verticalHomologyComplex q).homology p :=
  (horizontalFirstPageRowHomologyIso K p q).symm ≪≫
    HomologicalComplex.homologyMapIso
      (horizontalFirstPageRowComplexIsoVerticalHomologyComplex K q) p

/-- Naturality of the horizontal-of-vertical first-page homology comparison.

The homology map of a bicomplex-induced first-page map commutes with the comparison and with
homology of the induced vertical-homology row map. -/
@[reassoc]
theorem
    horizontalFirstPageHomologyVerticalHorizontalHomologyIso_hom_naturality_of_bicomplex
    (f : K ⟶ L) (p q : ℕ) :
    HomologicalComplex.homologyMap
          (horizontalPageMapOfBicomplex f 1 (le_refl 1)) (p, q) ≫
        (horizontalFirstPageHomologyVerticalHorizontalHomologyIso
          L p q).hom =
      (horizontalFirstPageHomologyVerticalHorizontalHomologyIso
        K p q).hom ≫
        HomologicalComplex.homologyMap
          (verticalHomologyComplexMap f q) p := by
  have hRow :=
    horizontalFirstPageRowHomologyIso_inv_naturality_of_bicomplex
      f p q
  have hNormalized :=
    horizontalFirstPageRowComplexIsoVerticalHomologyComplex_homology_naturality
      f p q
  simp only [horizontalFirstPageHomologyVerticalHorizontalHomologyIso,
    Iso.trans_hom, Iso.symm_hom]
  calc
    _ = (HomologicalComplex.homologyMap
          (horizontalPageMapOfBicomplex f 1 (le_refl 1)) (p, q) ≫
        (horizontalFirstPageRowHomologyIso L p q).inv) ≫
          (HomologicalComplex.homologyMapIso
            (horizontalFirstPageRowComplexIsoVerticalHomologyComplex L q)
            p).hom :=
      (Category.assoc _ _ _).symm
    _ = ((horizontalFirstPageRowHomologyIso K p q).inv ≫
        HomologicalComplex.homologyMap
          (horizontalFirstPageRowMapOfBicomplex f q) p) ≫
          (HomologicalComplex.homologyMapIso
            (horizontalFirstPageRowComplexIsoVerticalHomologyComplex L q)
            p).hom := by
      rw [hRow]
    _ = (horizontalFirstPageRowHomologyIso K p q).inv ≫
        (HomologicalComplex.homologyMap
            (horizontalFirstPageRowMapOfBicomplex f q) p ≫
          (HomologicalComplex.homologyMapIso
            (horizontalFirstPageRowComplexIsoVerticalHomologyComplex L q)
            p).hom) :=
      Category.assoc _ _ _
    _ = (horizontalFirstPageRowHomologyIso K p q).inv ≫
        ((HomologicalComplex.homologyMapIso
            (horizontalFirstPageRowComplexIsoVerticalHomologyComplex K q)
            p).hom ≫
          HomologicalComplex.homologyMap
            (verticalHomologyComplexMap f q) p) := by
      rw [hNormalized]
    _ = ((horizontalFirstPageRowHomologyIso K p q).inv ≫
        (HomologicalComplex.homologyMapIso
          (horizontalFirstPageRowComplexIsoVerticalHomologyComplex K q)
          p).hom) ≫
        HomologicalComplex.homologyMap
          (verticalHomologyComplexMap f q) p :=
      (Category.assoc _ _ _).symm

end HomologicalComplex₂

end
