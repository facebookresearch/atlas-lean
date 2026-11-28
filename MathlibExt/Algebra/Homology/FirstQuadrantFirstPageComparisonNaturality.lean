/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantFirstPageCoherentXNaturality
public import
  MathlibExt.Algebra.Homology.FirstQuadrantFirstPageMappingConeNaturality
public import
  MathlibExt.Algebra.Homology.FirstQuadrantFirstPageColumnNaturality
public import
  MathlibExt.Algebra.Homology.FirstQuadrantFirstPageRowNaturality

/-!
# Naturality of first-page comparisons with vertical homology

Let `K → L` be a morphism of first-quadrant bicomplexes in an abelian category. At bidegree
`(p,q)`, the coherent comparison from the horizontal-filtration first page to `H_q(K_p)`
commutes with the induced page map and column homology map.

The sign-normalized comparison is also natural, since its sign unit depends only on `(p,q)`.
For fixed `q`, these component equations give naturality of the isomorphism from the first-
page row complex to the vertical-homology complex and of its induced homology comparison.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- Naturality of the coherent first-page vertical-homology comparison.

For a bicomplex map `f : K → L`, the first-page map at `(p,q)` followed by the target
comparison equals the source comparison followed by `H_q(f_p)`. -/
@[reassoc]
theorem horizontalFirstPageCoherentVerticalHomologyIso_hom_naturality
    (f : K ⟶ L) (p q : ℕ) :
    (horizontalPageMapOfBicomplex f 1 (by omega)).f (p, q) ≫
        (horizontalFirstPageCoherentVerticalHomologyIso L p q).hom =
      (horizontalFirstPageCoherentVerticalHomologyIso K p q).hom ≫
        HomologicalComplex.homologyMap (f.f p) q := by
  have hX :=
    horizontalFirstPageCoherentXIso_hom_naturality_of_bicomplex f p q
  have hRelative :=
    horizontalFirstPageCoherentRelativeHomologyDirectColumnIso_hom_naturality_of_bicomplex
      f p q
  have hColumn :=
    horizontalDirectColumnHomologyIso_hom_naturality f p q
  simp only [horizontalFirstPageCoherentVerticalHomologyIso,
    horizontalFirstPageCoherentDirectColumnIso, Iso.trans_hom]
  calc
    _ = ((horizontalFirstPageCoherentXIso K p q).hom ≫
          ((horizontalCompleteFiltrationSpectralObjectMap f).hom
            (-(p : ℤ) - q)).app
              (ComposableArrows.mk₁ (homOfLE
                (horizontalFirstPageCoherentIndex_le p)))) ≫
        (horizontalFirstPageCoherentRelativeHomologyDirectColumnIso
          L p q).hom ≫
        (horizontalDirectColumnHomologyIso L p q).hom := by
      simpa only [Category.assoc] using hX =≫
        ((horizontalFirstPageCoherentRelativeHomologyDirectColumnIso
          L p q).hom ≫ (horizontalDirectColumnHomologyIso L p q).hom)
    _ = (horizontalFirstPageCoherentXIso K p q).hom ≫
        ((horizontalFirstPageCoherentRelativeHomologyDirectColumnIso
          K p q).hom ≫
          HomologicalComplex.homologyMap
            (horizontalDirectColumnCochainMap f p) (-(p : ℤ) - q)) ≫
        (horizontalDirectColumnHomologyIso L p q).hom := by
      simpa only [Category.assoc] using
        (horizontalFirstPageCoherentXIso K p q).hom ≫=
          hRelative =≫ (horizontalDirectColumnHomologyIso L p q).hom
    _ = ((horizontalFirstPageCoherentXIso K p q).hom ≫
          (horizontalFirstPageCoherentRelativeHomologyDirectColumnIso
            K p q).hom) ≫
        ((horizontalDirectColumnHomologyIso K p q).hom ≫
          HomologicalComplex.homologyMap (f.f p) q) := by
      simpa only [Category.assoc] using
        ((horizontalFirstPageCoherentXIso K p q).hom ≫
          (horizontalFirstPageCoherentRelativeHomologyDirectColumnIso
            K p q).hom) ≫= hColumn
    _ = _ := by simp only [Category.assoc]

/-- Naturality of the sign-normalized first-page comparison.

The normalized isomorphisms from first-page objects to column vertical homology commute with
every bicomplex map at the fixed bidegree. -/
@[reassoc]
theorem horizontalFirstPageNormalizedVerticalHomologyIso_hom_naturality
    (f : K ⟶ L) (p q : ℕ) :
    (horizontalPageMapOfBicomplex f 1 (by omega)).f (p, q) ≫
        (horizontalFirstPageNormalizedVerticalHomologyIso L p q).hom =
      (horizontalFirstPageNormalizedVerticalHomologyIso K p q).hom ≫
        HomologicalComplex.homologyMap (f.f p) q := by
  rw [horizontalFirstPageNormalizedVerticalHomologyIso_hom,
    horizontalFirstPageNormalizedVerticalHomologyIso_hom,
    Linear.comp_units_smul, Linear.units_smul_comp,
    horizontalFirstPageCoherentVerticalHomologyIso_hom_naturality]

/-- Naturality of the first-page row-complex comparison.

For fixed vertical degree `q`, the restricted first-page row map commutes with the normalized
isomorphism to the vertical-homology chain complex. -/
@[reassoc]
theorem
    horizontalFirstPageRowComplexIsoVerticalHomologyComplex_hom_naturality
    (f : K ⟶ L) (q : ℕ) :
    horizontalFirstPageRowMapOfBicomplex f q ≫
        (horizontalFirstPageRowComplexIsoVerticalHomologyComplex L q).hom =
      (horizontalFirstPageRowComplexIsoVerticalHomologyComplex K q).hom ≫
        verticalHomologyComplexMap f q := by
  apply HomologicalComplex.Hom.ext
  funext p
  simpa only [HomologicalComplex.comp_f,
    horizontalFirstPageRowMapOfBicomplex_f,
    horizontalFirstPageRowComplexIsoVerticalHomologyComplex_hom_f,
    verticalHomologyComplexMap_f] using
      horizontalFirstPageNormalizedVerticalHomologyIso_hom_naturality
        f p q

/-- Naturality on homology of the first-page row comparison.

Taking degree-`p` homology of the row-complex naturality square gives the corresponding
naturality square for row and vertical-homology-complex homology. -/
@[reassoc]
theorem
    horizontalFirstPageRowComplexIsoVerticalHomologyComplex_homology_naturality
    (f : K ⟶ L) (p q : ℕ) :
    HomologicalComplex.homologyMap
          (horizontalFirstPageRowMapOfBicomplex f q) p ≫
        (HomologicalComplex.homologyMapIso
          (horizontalFirstPageRowComplexIsoVerticalHomologyComplex L q)
          p).hom =
      (HomologicalComplex.homologyMapIso
        (horizontalFirstPageRowComplexIsoVerticalHomologyComplex K q)
        p).hom ≫
        HomologicalComplex.homologyMap
          (verticalHomologyComplexMap f q) p := by
  have h := congrArg
    (fun k ↦ HomologicalComplex.homologyMap k p)
    (horizontalFirstPageRowComplexIsoVerticalHomologyComplex_hom_naturality
      f q)
  rw [HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp] at h
  change HomologicalComplex.homologyMap
        (horizontalFirstPageRowMapOfBicomplex f q) p ≫
      HomologicalComplex.homologyMap
        (horizontalFirstPageRowComplexIsoVerticalHomologyComplex L q).hom
        p =
    HomologicalComplex.homologyMap
        (horizontalFirstPageRowComplexIsoVerticalHomologyComplex K q).hom
        p ≫
      HomologicalComplex.homologyMap
        (verticalHomologyComplexMap f q) p
  exact h

end HomologicalComplex₂

end
