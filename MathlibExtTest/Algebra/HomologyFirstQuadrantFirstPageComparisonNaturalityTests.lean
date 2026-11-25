/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Data.ZMod.Basic
public import
  MathlibExt.Algebra.Homology.FirstQuadrantFirstPageComparisonNaturality

/-! # Tests for first-page comparison naturality -/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂.FirstQuadrantFirstPageComparisonNaturalityTests

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalFirstPageCoherentVerticalHomologyIso_hom_naturality
#check horizontalFirstPageNormalizedVerticalHomologyIso_hom_naturality
#check
  horizontalFirstPageRowComplexIsoVerticalHomologyComplex_hom_naturality
#check
  horizontalFirstPageRowComplexIsoVerticalHomologyComplex_homology_naturality

example (f : K ⟶ L) (p q : ℕ) :
    (horizontalPageMapOfBicomplex f 1 (by omega)).f (p, q) ≫
        (horizontalFirstPageCoherentVerticalHomologyIso L p q).hom =
      (horizontalFirstPageCoherentVerticalHomologyIso K p q).hom ≫
        HomologicalComplex.homologyMap (f.f p) q :=
  horizontalFirstPageCoherentVerticalHomologyIso_hom_naturality f p q

example (f : K ⟶ L) (p q : ℕ) :
    (horizontalPageMapOfBicomplex f 1 (by omega)).f (p, q) ≫
        (horizontalFirstPageNormalizedVerticalHomologyIso L p q).hom =
      (horizontalFirstPageNormalizedVerticalHomologyIso K p q).hom ≫
        HomologicalComplex.homologyMap (f.f p) q :=
  horizontalFirstPageNormalizedVerticalHomologyIso_hom_naturality f p q

example (f : K ⟶ L) (q : ℕ) :
    horizontalFirstPageRowMapOfBicomplex f q ≫
        (horizontalFirstPageRowComplexIsoVerticalHomologyComplex L q).hom =
      (horizontalFirstPageRowComplexIsoVerticalHomologyComplex K q).hom ≫
        verticalHomologyComplexMap f q :=
  horizontalFirstPageRowComplexIsoVerticalHomologyComplex_hom_naturality
    f q

-- The row-complex square has exactly the normalized component square.
example (f : K ⟶ L) (p q : ℕ) :
    (horizontalFirstPageRowMapOfBicomplex f q).f p ≫
        (horizontalFirstPageNormalizedVerticalHomologyIso L p q).hom =
      (horizontalFirstPageNormalizedVerticalHomologyIso K p q).hom ≫
        HomologicalComplex.homologyMap (f.f p) q :=
  horizontalFirstPageNormalizedVerticalHomologyIso_hom_naturality f p q

example (f : K ⟶ L) (p q : ℕ) :
    HomologicalComplex.homologyMap
          (horizontalFirstPageRowMapOfBicomplex f q) p ≫
        (HomologicalComplex.homologyMapIso
          (horizontalFirstPageRowComplexIsoVerticalHomologyComplex L q)
          p).hom =
      (HomologicalComplex.homologyMapIso
        (horizontalFirstPageRowComplexIsoVerticalHomologyComplex K q)
        p).hom ≫
        HomologicalComplex.homologyMap
          (verticalHomologyComplexMap f q) p :=
  horizontalFirstPageRowComplexIsoVerticalHomologyComplex_homology_naturality
    f p q

-- Boundary bidegrees and a positive coherent column.
example (f : K ⟶ L) (q : ℕ) :=
  horizontalFirstPageCoherentVerticalHomologyIso_hom_naturality f 0 q

example (f : K ⟶ L) (p q : ℕ) :=
  horizontalFirstPageNormalizedVerticalHomologyIso_hom_naturality
    f (p + 1) q

example (f : K ⟶ L) :=
  horizontalFirstPageRowComplexIsoVerticalHomologyComplex_hom_naturality
    f 0

example (f : K ⟶ L) :=
  horizontalFirstPageRowComplexIsoVerticalHomologyComplex_homology_naturality
    f 0 0

-- Identity and composite maps exercise the complete comparison chain.
example (p q : ℕ) :=
  horizontalFirstPageCoherentVerticalHomologyIso_hom_naturality
    (𝟙 K) p q

example (f : K ⟶ L) (g : L ⟶ M) (p q : ℕ) :=
  horizontalFirstPageNormalizedVerticalHomologyIso_hom_naturality
    (f ≫ g) p q

example (f : K ⟶ L) (g : L ⟶ M) (p q : ℕ) :=
  horizontalFirstPageRowComplexIsoVerticalHomologyComplex_homology_naturality
    (f ≫ g) p q

example (q : ℕ) :=
  horizontalFirstPageRowComplexIsoVerticalHomologyComplex_hom_naturality
    (𝟙 (HomologicalComplex.zero : HomologicalComplex₂ C
      (ComplexShape.down ℕ) (ComplexShape.down ℕ))) q

section ZeroRing

variable {K₀ L₀ : HomologicalComplex₂ (ModuleCat.{0} (ZMod 1))
  (ComplexShape.down ℕ) (ComplexShape.down ℕ)}

example (f : K₀ ⟶ L₀) (p q : ℕ) :=
  horizontalFirstPageCoherentVerticalHomologyIso_hom_naturality f p q

example (f : K₀ ⟶ L₀) (p q : ℕ) :=
  horizontalFirstPageRowComplexIsoVerticalHomologyComplex_homology_naturality
    f p q

end ZeroRing

#print axioms horizontalFirstPageCoherentVerticalHomologyIso_hom_naturality
#print axioms horizontalFirstPageNormalizedVerticalHomologyIso_hom_naturality
#print axioms
  horizontalFirstPageRowComplexIsoVerticalHomologyComplex_hom_naturality
#print axioms
  horizontalFirstPageRowComplexIsoVerticalHomologyComplex_homology_naturality

end HomologicalComplex₂.FirstQuadrantFirstPageComparisonNaturalityTests

end
