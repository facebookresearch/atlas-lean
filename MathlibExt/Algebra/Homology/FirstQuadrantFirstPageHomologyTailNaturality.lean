/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantFirstPageComparisonNaturality
public import
  MathlibExt.Algebra.Homology.FirstQuadrantFirstPageRowNaturality

/-!
# Naturality of the first-page homology tail comparison

The inverse row-homology comparison followed by homology of the normalized
row comparison identifies homology of the first page with horizontal
homology of vertical homology.  This two-factor comparison is natural under
bicomplex maps.

No successor-page or page-two comparison is asserted here.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- Homology of the first page is naturally identified with horizontal
homology of the vertical-homology complex, before any successor-page
comparison. -/
noncomputable def horizontalFirstPageHomologyVerticalHorizontalHomologyIso
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page 1
      (le_refl 1)).homology (p, q) ≅
      (K.verticalHomologyComplex q).homology p :=
  (horizontalFirstPageRowHomologyIso K p q).symm ≪≫
    HomologicalComplex.homologyMapIso
      (horizontalFirstPageRowComplexIsoVerticalHomologyComplex K q) p

/-- The first-page homology tail comparison is natural under bicomplex
maps, in map-first orientation. -/
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
