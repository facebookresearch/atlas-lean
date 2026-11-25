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
  MathlibExt.Algebra.Homology.FirstQuadrantCanonicalAbutmentPreviousImageNaturality

/-! # Tests for canonical-abutment previous-image naturality -/

@[expose] public section

open CategoryTheory Limits ComposableArrows

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantCanonicalAbutmentPreviousImageNaturalityTests

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalCompleteHomologyImageMapOfBicomplex_eq_previous
#check horizontalCanonicalAbutmentPreviousHomologySquareOfBicomplex
#check horizontalCanonicalAbutmentPreviousImageMapOfBicomplex
#check horizontalCanonicalAbutmentPreviousImageMapOfBicomplex_ι
#check horizontalCanonicalAbutmentPreviousImageIso_naturality_of_bicomplex

/-- The split-free formula covers every lower index, including `-1`. -/
example (f : K ⟶ L) (p q : ℕ) :
    horizontalCompleteHomologyImageMapOfBicomplex f (p + q)
        (horizontalFirstPageLowerIndex p) =
      horizontalPrevTotalHomologyFiltrationMapOfBicomplex f p q :=
  horizontalCompleteHomologyImageMapOfBicomplex_eq_previous f p q

example (f : K ⟶ L) (p q : ℕ) :
    (horizontalCanonicalAbutmentPreviousHomologySquareOfBicomplex
      f p q).left =
      ((horizontalCompleteFiltrationSpectralObjectMap f).hom
        (-((p + q : ℕ) : ℤ))).app
          (mk₁ (horizontalCanonicalAbutmentLowerMap p)) :=
  rfl

example (f : K ⟶ L) (p q : ℕ) :
    (horizontalCanonicalAbutmentPreviousHomologySquareOfBicomplex
      f p q).right =
      ((horizontalCompleteFiltrationSpectralObjectMap f).hom
        (-((p + q : ℕ) : ℤ))).app
          (mk₁ (horizontalCanonicalAbutmentTotalMap p q)) :=
  rfl

example (f : K ⟶ L) (p q : ℕ) :
    horizontalCanonicalAbutmentPreviousImageMapOfBicomplex f p q ≫
        image.ι (horizontalCanonicalAbutmentPreviousHomologyMap L p q ≫
          horizontalCanonicalAbutmentToUpperHomologyMap L p q) =
      image.ι (horizontalCanonicalAbutmentPreviousHomologyMap K p q ≫
          horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≫
        ((horizontalCompleteFiltrationSpectralObjectMap f).hom
          (-((p + q : ℕ) : ℤ))).app
            (mk₁ (horizontalCanonicalAbutmentTotalMap p q)) :=
  horizontalCanonicalAbutmentPreviousImageMapOfBicomplex_ι f p q

example (f : K ⟶ L) (p q : ℕ) :
    horizontalCanonicalAbutmentPreviousImageMapOfBicomplex f p q ≫
        (horizontalCanonicalAbutmentPreviousImageIso L p q).hom =
      (horizontalCanonicalAbutmentPreviousImageIso K p q).hom ≫
        horizontalPrevTotalHomologyFiltrationMapOfBicomplex f p q :=
  horizontalCanonicalAbutmentPreviousImageIso_naturality_of_bicomplex
    f p q

example (f : K ⟶ L) :
    horizontalCanonicalAbutmentPreviousImageMapOfBicomplex f 0 0 ≫
        (horizontalCanonicalAbutmentPreviousImageIso L 0 0).hom =
      (horizontalCanonicalAbutmentPreviousImageIso K 0 0).hom ≫
        horizontalPrevTotalHomologyFiltrationMapOfBicomplex f 0 0 :=
  horizontalCanonicalAbutmentPreviousImageIso_naturality_of_bicomplex
    f 0 0

example (f : K ⟶ L) (q : ℕ) :
    horizontalCanonicalAbutmentPreviousImageMapOfBicomplex f 0 q ≫
        (horizontalCanonicalAbutmentPreviousImageIso L 0 q).hom =
      (horizontalCanonicalAbutmentPreviousImageIso K 0 q).hom ≫
        horizontalPrevTotalHomologyFiltrationMapOfBicomplex f 0 q :=
  horizontalCanonicalAbutmentPreviousImageIso_naturality_of_bicomplex
    f 0 q

example (f : K ⟶ L) (p : ℕ) :
    horizontalCanonicalAbutmentPreviousImageMapOfBicomplex f p 0 ≫
        (horizontalCanonicalAbutmentPreviousImageIso L p 0).hom =
      (horizontalCanonicalAbutmentPreviousImageIso K p 0).hom ≫
        horizontalPrevTotalHomologyFiltrationMapOfBicomplex f p 0 :=
  horizontalCanonicalAbutmentPreviousImageIso_naturality_of_bicomplex
    f p 0

example (f : K ⟶ L) (p q : ℕ) :
    horizontalCanonicalAbutmentPreviousImageMapOfBicomplex f (p + 1) q ≫
        (horizontalCanonicalAbutmentPreviousImageIso L (p + 1) q).hom =
      (horizontalCanonicalAbutmentPreviousImageIso K (p + 1) q).hom ≫
        horizontalPrevTotalHomologyFiltrationMapOfBicomplex f (p + 1) q :=
  horizontalCanonicalAbutmentPreviousImageIso_naturality_of_bicomplex
    f (p + 1) q

example (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) (p q : ℕ) :
    horizontalCanonicalAbutmentPreviousImageMapOfBicomplex (𝟙 K) p q ≫
        (horizontalCanonicalAbutmentPreviousImageIso K p q).hom =
      (horizontalCanonicalAbutmentPreviousImageIso K p q).hom ≫
        horizontalPrevTotalHomologyFiltrationMapOfBicomplex (𝟙 K) p q :=
  horizontalCanonicalAbutmentPreviousImageIso_naturality_of_bicomplex
    (𝟙 K) p q

example (f : K ⟶ L) (g : L ⟶ M) (p q : ℕ) :
    horizontalCanonicalAbutmentPreviousImageMapOfBicomplex (f ≫ g) p q ≫
        (horizontalCanonicalAbutmentPreviousImageIso M p q).hom =
      (horizontalCanonicalAbutmentPreviousImageIso K p q).hom ≫
        horizontalPrevTotalHomologyFiltrationMapOfBicomplex (f ≫ g) p q :=
  horizontalCanonicalAbutmentPreviousImageIso_naturality_of_bicomplex
    (f ≫ g) p q

private abbrev ZeroModuleCat := ModuleCat (ZMod 1)

private abbrev ZeroBicomplex :=
  HomologicalComplex₂ ZeroModuleCat (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)

noncomputable example (K : ZeroBicomplex) (p q : ℕ) :
    image (horizontalCanonicalAbutmentPreviousHomologyMap K p q ≫
        horizontalCanonicalAbutmentToUpperHomologyMap K p q) ⟶
      image (horizontalCanonicalAbutmentPreviousHomologyMap K p q ≫
        horizontalCanonicalAbutmentToUpperHomologyMap K p q) :=
  horizontalCanonicalAbutmentPreviousImageMapOfBicomplex (𝟙 K) p q

#print axioms horizontalCompleteHomologyImageMapOfBicomplex_eq_previous
#print axioms
  horizontalCanonicalAbutmentPreviousHomologySquareOfBicomplex
#print axioms horizontalCanonicalAbutmentPreviousImageMapOfBicomplex
#print axioms horizontalCanonicalAbutmentPreviousImageMapOfBicomplex_ι
#print axioms
  horizontalCanonicalAbutmentPreviousImageIso_naturality_of_bicomplex

end HomologicalComplex₂.FirstQuadrantCanonicalAbutmentPreviousImageNaturalityTests

end
