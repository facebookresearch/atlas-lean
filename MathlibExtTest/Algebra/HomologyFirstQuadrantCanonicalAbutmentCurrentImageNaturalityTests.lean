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
  MathlibExt.Algebra.Homology.FirstQuadrantCanonicalAbutmentCurrentImageNaturality

/-! # Tests for canonical-abutment current-image naturality -/

@[expose] public section

open CategoryTheory Limits ComposableArrows

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantCanonicalAbutmentCurrentImageNaturalityTests

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalCompleteHomologyToTotalSquareOfBicomplex
#check horizontalCompleteHomologyImageMapOfBicomplex
#check horizontalCompleteHomologyImageMapOfBicomplex_ι
#check horizontalCompleteHomologyImageMapOfBicomplex_eq_current
#check horizontalCanonicalAbutmentCurrentHomologySquareOfBicomplex
#check horizontalCanonicalAbutmentCurrentImageMapOfBicomplex
#check horizontalCanonicalAbutmentCurrentImageMapOfBicomplex_ι
#check horizontalCanonicalAbutmentCurrentImageIso_naturality_of_bicomplex

example (f : K ⟶ L) (n : ℕ) (i : EInt) :
    (horizontalCompleteHomologyToTotalSquareOfBicomplex f n i).left =
      HomologicalComplex.homologyMap
        (horizontalCompleteFilteredTotalComplexMapOfBicomplex f i) n :=
  rfl

example (f : K ⟶ L) (n : ℕ) (i : EInt) :
    (horizontalCompleteHomologyToTotalSquareOfBicomplex f n i).right =
      HomologicalComplex.homologyMap
        (total.map f (ComplexShape.down ℕ)) n :=
  rfl

example (f : K ⟶ L) (n : ℕ) (i : EInt) :
    horizontalCompleteHomologyImageMapOfBicomplex f n i ≫
        image.ι (horizontalCompleteHomologyToTotal L n i) =
      image.ι (horizontalCompleteHomologyToTotal K n i) ≫
        HomologicalComplex.homologyMap
          (total.map f (ComplexShape.down ℕ)) n :=
  horizontalCompleteHomologyImageMapOfBicomplex_ι f n i

example (f : K ⟶ L) (p q : ℕ) :
    horizontalCompleteHomologyImageMapOfBicomplex f (p + q)
        (horizontalFirstPageUpperIndex p) =
      horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex
        f p q :=
  horizontalCompleteHomologyImageMapOfBicomplex_eq_current f p q

example (f : K ⟶ L) (p q : ℕ) :
    horizontalCanonicalAbutmentCurrentImageMapOfBicomplex f p q ≫
        image.ι (horizontalCanonicalAbutmentToUpperHomologyMap L p q) =
      image.ι (horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≫
        ((horizontalCompleteFiltrationSpectralObjectMap f).hom
          (-((p + q : ℕ) : ℤ))).app
            (mk₁ (horizontalCanonicalAbutmentTotalMap p q)) :=
  horizontalCanonicalAbutmentCurrentImageMapOfBicomplex_ι f p q

example (f : K ⟶ L) (p q : ℕ) :
    horizontalCanonicalAbutmentCurrentImageMapOfBicomplex f p q ≫
        (horizontalCanonicalAbutmentCurrentImageIso L p q).hom =
      (horizontalCanonicalAbutmentCurrentImageIso K p q).hom ≫
        horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex
          f p q :=
  horizontalCanonicalAbutmentCurrentImageIso_naturality_of_bicomplex
    f p q

example (f : K ⟶ L) :
    horizontalCanonicalAbutmentCurrentImageMapOfBicomplex f 0 0 ≫
        (horizontalCanonicalAbutmentCurrentImageIso L 0 0).hom =
      (horizontalCanonicalAbutmentCurrentImageIso K 0 0).hom ≫
        horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex
          f 0 0 :=
  horizontalCanonicalAbutmentCurrentImageIso_naturality_of_bicomplex
    f 0 0

example (f : K ⟶ L) (q : ℕ) :
    horizontalCanonicalAbutmentCurrentImageMapOfBicomplex f 0 q ≫
        (horizontalCanonicalAbutmentCurrentImageIso L 0 q).hom =
      (horizontalCanonicalAbutmentCurrentImageIso K 0 q).hom ≫
        horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex
          f 0 q :=
  horizontalCanonicalAbutmentCurrentImageIso_naturality_of_bicomplex
    f 0 q

example (f : K ⟶ L) (p : ℕ) :
    horizontalCanonicalAbutmentCurrentImageMapOfBicomplex f p 0 ≫
        (horizontalCanonicalAbutmentCurrentImageIso L p 0).hom =
      (horizontalCanonicalAbutmentCurrentImageIso K p 0).hom ≫
        horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex
          f p 0 :=
  horizontalCanonicalAbutmentCurrentImageIso_naturality_of_bicomplex
    f p 0

example (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) (p q : ℕ) :
    horizontalCanonicalAbutmentCurrentImageMapOfBicomplex (𝟙 K) p q ≫
        (horizontalCanonicalAbutmentCurrentImageIso K p q).hom =
      (horizontalCanonicalAbutmentCurrentImageIso K p q).hom ≫
        horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex
          (𝟙 K) p q :=
  horizontalCanonicalAbutmentCurrentImageIso_naturality_of_bicomplex
    (𝟙 K) p q

example (f : K ⟶ L) (g : L ⟶ M) (p q : ℕ) :
    horizontalCanonicalAbutmentCurrentImageMapOfBicomplex (f ≫ g) p q ≫
        (horizontalCanonicalAbutmentCurrentImageIso M p q).hom =
      (horizontalCanonicalAbutmentCurrentImageIso K p q).hom ≫
        horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex
          (f ≫ g) p q :=
  horizontalCanonicalAbutmentCurrentImageIso_naturality_of_bicomplex
    (f ≫ g) p q

private abbrev ZeroModuleCat := ModuleCat (ZMod 1)

private abbrev ZeroBicomplex :=
  HomologicalComplex₂ ZeroModuleCat (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)

noncomputable example (K : ZeroBicomplex) (p q : ℕ) :
    image (horizontalCanonicalAbutmentToUpperHomologyMap
      K p q) ⟶
      image (horizontalCanonicalAbutmentToUpperHomologyMap
        K p q) :=
  horizontalCanonicalAbutmentCurrentImageMapOfBicomplex
    (𝟙 K) p q

#print axioms horizontalCompleteHomologyToTotalSquareOfBicomplex
#print axioms horizontalCompleteHomologyImageMapOfBicomplex
#print axioms horizontalCompleteHomologyImageMapOfBicomplex_ι
#print axioms horizontalCompleteHomologyImageMapOfBicomplex_eq_current
#print axioms horizontalCanonicalAbutmentCurrentHomologySquareOfBicomplex
#print axioms horizontalCanonicalAbutmentCurrentImageMapOfBicomplex
#print axioms horizontalCanonicalAbutmentCurrentImageMapOfBicomplex_ι
#print axioms
  horizontalCanonicalAbutmentCurrentImageIso_naturality_of_bicomplex

end HomologicalComplex₂.FirstQuadrantCanonicalAbutmentCurrentImageNaturalityTests

end
