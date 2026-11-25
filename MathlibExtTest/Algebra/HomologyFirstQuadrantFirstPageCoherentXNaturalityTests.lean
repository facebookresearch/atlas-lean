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
  MathlibExt.Algebra.Homology.FirstQuadrantFirstPageCoherentXNaturality

/-! # Tests for coherent first-page X naturality -/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits ComposableArrows

universe v u

namespace HomologicalComplex₂.FirstQuadrantFirstPageCoherentXNaturalityTests

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalFirstPageCoherentXIso_hom_naturality_of_bicomplex
#check horizontalFirstPageCoherentXIso_hom_naturality_of_bicomplex_assoc

example (f : K ⟶ L) (p q : ℕ) :
    (horizontalPageMapOfBicomplex f 1 (by omega)).f (p, q) ≫
        (horizontalFirstPageCoherentXIso L p q).hom =
      (horizontalFirstPageCoherentXIso K p q).hom ≫
        ((horizontalCompleteFiltrationSpectralObjectMap f).hom
          (-(p : ℤ) - q)).app
            (mk₁ (homOfLE
              (horizontalFirstPageCoherentIndex_le p))) :=
  horizontalFirstPageCoherentXIso_hom_naturality_of_bicomplex f p q

-- The bottom coherent window is the ordinary first filtration window.
example (f : K ⟶ L) (q : ℕ) :
    (horizontalPageMapOfBicomplex f 1 (by omega)).f (0, q) ≫
        (horizontalFirstPageCoherentXIso L 0 q).hom =
      (horizontalFirstPageCoherentXIso K 0 q).hom ≫
        ((horizontalCompleteFiltrationSpectralObjectMap f).hom
          (-((0 : ℕ) : ℤ) - q)).app
            (mk₁ (homOfLE
              (horizontalFirstPageCoherentIndex_le 0))) :=
  horizontalFirstPageCoherentXIso_hom_naturality_of_bicomplex f 0 q

-- Positive columns use the coherent successor window.
example (f : K ⟶ L) (p q : ℕ) :
    (horizontalPageMapOfBicomplex f 1 (by omega)).f (p + 1, q) ≫
        (horizontalFirstPageCoherentXIso L (p + 1) q).hom =
      (horizontalFirstPageCoherentXIso K (p + 1) q).hom ≫
        ((horizontalCompleteFiltrationSpectralObjectMap f).hom
          (-((p + 1 : ℕ) : ℤ) - q)).app
            (mk₁ (homOfLE
              (horizontalFirstPageCoherentIndex_le (p + 1)))) :=
  horizontalFirstPageCoherentXIso_hom_naturality_of_bicomplex
    f (p + 1) q

example (f : K ⟶ L) (p : ℕ) :
    (horizontalPageMapOfBicomplex f 1 (by omega)).f (p, 0) ≫
        (horizontalFirstPageCoherentXIso L p 0).hom =
      (horizontalFirstPageCoherentXIso K p 0).hom ≫
        ((horizontalCompleteFiltrationSpectralObjectMap f).hom
          (-(p : ℤ) - ((0 : ℕ) : ℤ))).app
            (mk₁ (homOfLE
              (horizontalFirstPageCoherentIndex_le p))) :=
  horizontalFirstPageCoherentXIso_hom_naturality_of_bicomplex f p 0

example (f : K ⟶ L) :
    (horizontalPageMapOfBicomplex f 1 (by omega)).f (0, 0) ≫
        (horizontalFirstPageCoherentXIso L 0 0).hom =
      (horizontalFirstPageCoherentXIso K 0 0).hom ≫
        ((horizontalCompleteFiltrationSpectralObjectMap f).hom 0).app
            (mk₁ (homOfLE
              (horizontalFirstPageCoherentIndex_le 0))) := by
  simpa using
    horizontalFirstPageCoherentXIso_hom_naturality_of_bicomplex f 0 0

-- Identity and composite bicomplex maps retain the same component square.
example (p q : ℕ) :=
  horizontalFirstPageCoherentXIso_hom_naturality_of_bicomplex
    (𝟙 K) p q

example (f : K ⟶ L) (g : L ⟶ M) (p q : ℕ) :=
  horizontalFirstPageCoherentXIso_hom_naturality_of_bicomplex
    (f ≫ g) p q

example (p q : ℕ) :=
  horizontalFirstPageCoherentXIso_hom_naturality_of_bicomplex
    (𝟙 (HomologicalComplex.zero : HomologicalComplex₂ C
      (ComplexShape.down ℕ) (ComplexShape.down ℕ))) p q

section ZeroRing

variable {K₀ L₀ : HomologicalComplex₂ (ModuleCat.{0} (ZMod 1))
  (ComplexShape.down ℕ) (ComplexShape.down ℕ)}

example (f : K₀ ⟶ L₀) (p q : ℕ) :=
  horizontalFirstPageCoherentXIso_hom_naturality_of_bicomplex f p q

end ZeroRing

#print axioms horizontalFirstPageCoherentXIso_hom_naturality_of_bicomplex

end HomologicalComplex₂.FirstQuadrantFirstPageCoherentXNaturalityTests

end
