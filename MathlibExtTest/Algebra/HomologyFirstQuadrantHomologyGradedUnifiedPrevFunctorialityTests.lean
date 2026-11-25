/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantHomologyGradedUnifiedPrevFunctoriality

/-! # Tests for unified predecessor homology-filtration functoriality -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂.FirstQuadrantHomologyGradedUnifiedPrevFunctorialityTests

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalPrevTotalHomologyFiltrationMapOfBicomplex_id
#check horizontalPrevTotalHomologyFiltrationMapOfBicomplex_comp

example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (p q : ℕ) :
    horizontalPrevTotalHomologyFiltrationMapOfBicomplex (𝟙 K) p q = 𝟙 _ := by
  simp

example (f : K ⟶ L) (g : L ⟶ M) (p q : ℕ) :
    horizontalPrevTotalHomologyFiltrationMapOfBicomplex (f ≫ g) p q =
      horizontalPrevTotalHomologyFiltrationMapOfBicomplex f p q ≫
        horizontalPrevTotalHomologyFiltrationMapOfBicomplex g p q := by
  simp

-- Column zero uses uniqueness from the complete `-1` source.
example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (q : ℕ) :
    horizontalPrevTotalHomologyFiltrationMapOfBicomplex (𝟙 K) 0 q = 𝟙 _ := by
  simp

example (f : K ⟶ L) (g : L ⟶ M) (q : ℕ) :
    horizontalPrevTotalHomologyFiltrationMapOfBicomplex (f ≫ g) 0 q =
      horizontalPrevTotalHomologyFiltrationMapOfBicomplex f 0 q ≫
        horizontalPrevTotalHomologyFiltrationMapOfBicomplex g 0 q := by
  simp

-- At the first positive column, the positive predecessor law is reused.
example (f : K ⟶ L) (g : L ⟶ M) (q : ℕ) :
    horizontalPrevTotalHomologyFiltrationMapOfBicomplex (f ≫ g) 1 q =
      horizontalPrevTotalHomologyFiltrationMapOfBicomplex f 1 q ≫
        horizontalPrevTotalHomologyFiltrationMapOfBicomplex g 1 q := by
  simp

-- Total degree `p` is covered by the same law when `q = 0`.
example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (p : ℕ) :
    horizontalPrevTotalHomologyFiltrationMapOfBicomplex (𝟙 K) p 0 = 𝟙 _ := by
  simp

-- The zero-column, zero-degree corner remains functorial.
example (f : K ⟶ L) (g : L ⟶ M) :
    horizontalPrevTotalHomologyFiltrationMapOfBicomplex (f ≫ g) 0 0 =
      horizontalPrevTotalHomologyFiltrationMapOfBicomplex f 0 0 ≫
        horizontalPrevTotalHomologyFiltrationMapOfBicomplex g 0 0 := by
  simp

#print axioms horizontalPrevTotalHomologyFiltrationMapOfBicomplex_id
#print axioms horizontalPrevTotalHomologyFiltrationMapOfBicomplex_comp

end HomologicalComplex₂.FirstQuadrantHomologyGradedUnifiedPrevFunctorialityTests

end
