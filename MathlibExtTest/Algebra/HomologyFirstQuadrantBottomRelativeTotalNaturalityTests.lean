/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantBottomRelativeTotalNaturality

/-! # Tests for bottom-relative-to-total bicomplex naturality -/

@[expose] public section

open CategoryTheory Limits ComposableArrows

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantBottomRelativeTotalNaturalityTests

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalBottomRelativeHomologyToTotalIso_naturality_of_bicomplex

example (f : K ⟶ L) (p q : ℕ) :
    ((horizontalCompleteFiltrationSpectralObjectMap f).hom
        (-((p + q : ℕ) : ℤ))).app
          (mk₁ (horizontalCanonicalAbutmentTotalMap p q)) ≫
      (horizontalBottomRelativeHomologyToTotalIso L p q).hom =
    (horizontalBottomRelativeHomologyToTotalIso K p q).hom ≫
      HomologicalComplex.homologyMap
        (total.map f (ComplexShape.down ℕ)) (p + q) :=
  horizontalBottomRelativeHomologyToTotalIso_naturality_of_bicomplex
    f p q

example (f : K ⟶ L) :
    ((horizontalCompleteFiltrationSpectralObjectMap f).hom 0).app
          (mk₁ (horizontalCanonicalAbutmentTotalMap 0 0)) ≫
      (horizontalBottomRelativeHomologyToTotalIso L 0 0).hom =
    (horizontalBottomRelativeHomologyToTotalIso K 0 0).hom ≫
      HomologicalComplex.homologyMap
        (total.map f (ComplexShape.down ℕ)) 0 := by
  simpa using
    horizontalBottomRelativeHomologyToTotalIso_naturality_of_bicomplex
      f 0 0

example (f : K ⟶ L) (q : ℕ) :
    ((horizontalCompleteFiltrationSpectralObjectMap f).hom
        (-((0 + q : ℕ) : ℤ))).app
          (mk₁ (horizontalCanonicalAbutmentTotalMap 0 q)) ≫
      (horizontalBottomRelativeHomologyToTotalIso L 0 q).hom =
    (horizontalBottomRelativeHomologyToTotalIso K 0 q).hom ≫
      HomologicalComplex.homologyMap
        (total.map f (ComplexShape.down ℕ)) (0 + q) :=
  horizontalBottomRelativeHomologyToTotalIso_naturality_of_bicomplex
    f 0 q

example (f : K ⟶ L) (p : ℕ) :
    ((horizontalCompleteFiltrationSpectralObjectMap f).hom
        (-((p + 0 : ℕ) : ℤ))).app
          (mk₁ (horizontalCanonicalAbutmentTotalMap p 0)) ≫
      (horizontalBottomRelativeHomologyToTotalIso L p 0).hom =
    (horizontalBottomRelativeHomologyToTotalIso K p 0).hom ≫
      HomologicalComplex.homologyMap
        (total.map f (ComplexShape.down ℕ)) (p + 0) :=
  horizontalBottomRelativeHomologyToTotalIso_naturality_of_bicomplex
    f p 0

example (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) (p q : ℕ) :
    ((horizontalCompleteFiltrationSpectralObjectMap (𝟙 K)).hom
        (-((p + q : ℕ) : ℤ))).app
          (mk₁ (horizontalCanonicalAbutmentTotalMap p q)) ≫
      (horizontalBottomRelativeHomologyToTotalIso K p q).hom =
    (horizontalBottomRelativeHomologyToTotalIso K p q).hom ≫
      HomologicalComplex.homologyMap
        (total.map (𝟙 K) (ComplexShape.down ℕ)) (p + q) :=
  horizontalBottomRelativeHomologyToTotalIso_naturality_of_bicomplex
    (𝟙 K) p q

example (f : K ⟶ L) (g : L ⟶ M) (p q : ℕ) :
    ((horizontalCompleteFiltrationSpectralObjectMap (f ≫ g)).hom
        (-((p + q : ℕ) : ℤ))).app
          (mk₁ (horizontalCanonicalAbutmentTotalMap p q)) ≫
      (horizontalBottomRelativeHomologyToTotalIso M p q).hom =
    (horizontalBottomRelativeHomologyToTotalIso K p q).hom ≫
      HomologicalComplex.homologyMap
        (total.map (f ≫ g) (ComplexShape.down ℕ)) (p + q) :=
  horizontalBottomRelativeHomologyToTotalIso_naturality_of_bicomplex
    (f ≫ g) p q

#print axioms
  horizontalBottomRelativeHomologyToTotalIso_naturality_of_bicomplex

end HomologicalComplex₂.FirstQuadrantBottomRelativeTotalNaturalityTests

end
