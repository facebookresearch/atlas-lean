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
  MathlibExt.Algebra.Homology.FirstQuadrantCanonicalAbutmentGradedNaturality

/-! # Tests for canonical-abutment associated-graded naturality -/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantCanonicalAbutmentGradedNaturalityTests

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalCanonicalAbutmentImageCompSquareOfBicomplex
#check horizontalCanonicalAbutmentImageQuotientMapOfBicomplex_eq_coker_map
#check horizontalCanonicalAbutmentImageQuotientGradedIso_naturality
#check horizontalCanonicalAbutmentGradedIso_naturality

example (f : K ⟶ L) (p q : ℕ) :
    (horizontalCanonicalAbutmentImageCompSquareOfBicomplex f p q).left =
      horizontalCanonicalAbutmentPreviousImageMapOfBicomplex f p q :=
  rfl

example (f : K ⟶ L) (p q : ℕ) :
    (horizontalCanonicalAbutmentImageCompSquareOfBicomplex f p q).right =
      horizontalCanonicalAbutmentCurrentImageMapOfBicomplex f p q :=
  rfl

example (f : K ⟶ L) (p q : ℕ) :
    horizontalCanonicalAbutmentImageQuotientMapOfBicomplex f p q =
      (Limits.coker C).map
        (horizontalCanonicalAbutmentImageCompSquareOfBicomplex f p q) :=
  horizontalCanonicalAbutmentImageQuotientMapOfBicomplex_eq_coker_map
    f p q

example (f : K ⟶ L) (p q : ℕ) :
    horizontalCanonicalAbutmentImageQuotientMapOfBicomplex f p q ≫
        (horizontalCanonicalAbutmentImageQuotientGradedIso L p q).hom =
      (horizontalCanonicalAbutmentImageQuotientGradedIso K p q).hom ≫
        horizontalTotalHomologyGradedPieceMapOfBicomplex f p q :=
  horizontalCanonicalAbutmentImageQuotientGradedIso_naturality f p q

example (f : K ⟶ L) (p q : ℕ) :
    horizontalCanonicalAbutmentMapOfBicomplex f p q ≫
        (horizontalCanonicalAbutmentGradedIso L p q).hom =
      (horizontalCanonicalAbutmentGradedIso K p q).hom ≫
        horizontalTotalHomologyGradedPieceMapOfBicomplex f p q :=
  horizontalCanonicalAbutmentGradedIso_naturality f p q

example (f : K ⟶ L) :
    horizontalCanonicalAbutmentMapOfBicomplex f 0 0 ≫
        (horizontalCanonicalAbutmentGradedIso L 0 0).hom =
      (horizontalCanonicalAbutmentGradedIso K 0 0).hom ≫
        horizontalTotalHomologyGradedPieceMapOfBicomplex f 0 0 :=
  horizontalCanonicalAbutmentGradedIso_naturality f 0 0

example (f : K ⟶ L) (q : ℕ) :
    horizontalCanonicalAbutmentMapOfBicomplex f 0 q ≫
        (horizontalCanonicalAbutmentGradedIso L 0 q).hom =
      (horizontalCanonicalAbutmentGradedIso K 0 q).hom ≫
        horizontalTotalHomologyGradedPieceMapOfBicomplex f 0 q :=
  horizontalCanonicalAbutmentGradedIso_naturality f 0 q

example (f : K ⟶ L) (p : ℕ) :
    horizontalCanonicalAbutmentMapOfBicomplex f p 0 ≫
        (horizontalCanonicalAbutmentGradedIso L p 0).hom =
      (horizontalCanonicalAbutmentGradedIso K p 0).hom ≫
        horizontalTotalHomologyGradedPieceMapOfBicomplex f p 0 :=
  horizontalCanonicalAbutmentGradedIso_naturality f p 0

example (f : K ⟶ L) (p q : ℕ) :
    horizontalCanonicalAbutmentMapOfBicomplex f (p + 1) q ≫
        (horizontalCanonicalAbutmentGradedIso L (p + 1) q).hom =
      (horizontalCanonicalAbutmentGradedIso K (p + 1) q).hom ≫
        horizontalTotalHomologyGradedPieceMapOfBicomplex f (p + 1) q :=
  horizontalCanonicalAbutmentGradedIso_naturality f (p + 1) q

example (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) (p q : ℕ) :
    horizontalCanonicalAbutmentMapOfBicomplex (𝟙 K) p q ≫
        (horizontalCanonicalAbutmentGradedIso K p q).hom =
      (horizontalCanonicalAbutmentGradedIso K p q).hom ≫
        horizontalTotalHomologyGradedPieceMapOfBicomplex (𝟙 K) p q :=
  horizontalCanonicalAbutmentGradedIso_naturality (𝟙 K) p q

example (f : K ⟶ L) (g : L ⟶ M) (p q : ℕ) :
    horizontalCanonicalAbutmentMapOfBicomplex (f ≫ g) p q ≫
        (horizontalCanonicalAbutmentGradedIso M p q).hom =
      (horizontalCanonicalAbutmentGradedIso K p q).hom ≫
        horizontalTotalHomologyGradedPieceMapOfBicomplex (f ≫ g) p q :=
  horizontalCanonicalAbutmentGradedIso_naturality (f ≫ g) p q

private abbrev ZeroModuleCat := ModuleCat (ZMod 1)

private abbrev ZeroBicomplex :=
  HomologicalComplex₂ ZeroModuleCat (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)

noncomputable example (K : ZeroBicomplex) (p q : ℕ) :
    horizontalFirstQuadrantCanonicalAbutmentTerm K p q ⟶
      horizontalTotalHomologyGradedPiece K p q :=
  (horizontalCanonicalAbutmentGradedIso K p q).hom

noncomputable example (K : ZeroBicomplex) (p q : ℕ) :
    horizontalCanonicalAbutmentMapOfBicomplex (𝟙 K) p q ≫
        (horizontalCanonicalAbutmentGradedIso K p q).hom =
      (horizontalCanonicalAbutmentGradedIso K p q).hom ≫
        horizontalTotalHomologyGradedPieceMapOfBicomplex (𝟙 K) p q :=
  horizontalCanonicalAbutmentGradedIso_naturality (𝟙 K) p q

#print axioms horizontalCanonicalAbutmentImageCompSquareOfBicomplex
#print axioms
  horizontalCanonicalAbutmentImageQuotientMapOfBicomplex_eq_coker_map
#print axioms horizontalCanonicalAbutmentImageQuotientGradedIso_naturality
#print axioms horizontalCanonicalAbutmentGradedIso_naturality

end HomologicalComplex₂.FirstQuadrantCanonicalAbutmentGradedNaturalityTests

end
