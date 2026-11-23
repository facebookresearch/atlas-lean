/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

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
# Naturality of first-page vertical-homology comparisons

The coherent first-page comparison is natural under bicomplex maps.  Its
normalized form is natural because the same sign unit occurs at source and
target.  The normalized component squares assemble into naturality of the
fixed-row complex isomorphism, and therefore into the corresponding homology
square.

This file makes no successor-page, second-page, S⁻¹S, or
Bousfield--Kan claim.
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

/-- The coherent first-page comparison with vertical homology is natural in
the bicomplex. -/
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

/-- The sign-normalized first-page comparison with vertical homology is
natural in the bicomplex. -/
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

/-- The normalized isomorphism from a fixed first-page row to the
vertical-homology complex is natural in the bicomplex. -/
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

/-- Degreewise homology of the normalized row-complex naturality square. -/
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
