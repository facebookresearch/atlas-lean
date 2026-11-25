/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantHomologyGradedZeroSquare

/-!
# Maps on the associated graded of first-quadrant total homology

The positive- and zero-column filtration squares are combined into one
all-column square.  Viewing that square as a morphism in the arrow category
and applying the cokernel functor gives the induced map on each associated
graded piece.

This file does not yet prove identity or composition laws for these maps.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- The map on the preceding complete total-homology filtration stages,
using the transported finite predecessor in positive columns and the zero
map from the genuinely zero lower stage in column zero. -/
noncomputable def horizontalPrevTotalHomologyFiltrationMapOfBicomplex
    (f : K ⟶ L) (p q : ℕ) :
    (horizontalTotalHomologyFiltration K (p + q)).obj
        ((((p : ℤ) - 1 : ℤ) : EInt)) ⟶
      (horizontalTotalHomologyFiltration L (p + q)).obj
        ((((p : ℤ) - 1 : ℤ) : EInt)) := by
  by_cases hp : 0 < p
  · exact horizontalPositivePrevTotalHomologyFiltrationMapOfBicomplex
      f p q hp
  · have hp0 : p = 0 := Nat.eq_zero_of_not_pos hp
    subst p
    exact horizontalZeroPrevTotalHomologyFiltrationMapOfBicomplex f q

/-- Every bicomplex map commutes with the consecutive complete
total-homology filtration step, including at column zero. -/
theorem horizontalTotalHomologyFiltrationStepMap_naturality
    (f : K ⟶ L) (p q : ℕ) :
    horizontalTotalHomologyFiltrationStepMap K p q ≫
        horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex f p q =
      horizontalPrevTotalHomologyFiltrationMapOfBicomplex f p q ≫
        horizontalTotalHomologyFiltrationStepMap L p q := by
  by_cases hp : 0 < p
  · simpa [horizontalPrevTotalHomologyFiltrationMapOfBicomplex, hp] using
      horizontalTotalHomologyFiltrationStepMap_naturality_of_pos f p q hp
  · have hp0 : p = 0 := Nat.eq_zero_of_not_pos hp
    subst p
    simpa [horizontalPrevTotalHomologyFiltrationMapOfBicomplex, hp] using
      horizontalTotalHomologyFiltrationStepMap_naturality_zero f q

/-- The consecutive-stage filtration square of a bicomplex map, packaged as
a morphism in the arrow category. -/
noncomputable def horizontalTotalHomologyFiltrationStepSquareOfBicomplex
    (f : K ⟶ L) (p q : ℕ) :
    Arrow.mk (horizontalTotalHomologyFiltrationStepMap K p q) ⟶
      Arrow.mk (horizontalTotalHomologyFiltrationStepMap L p q) :=
  Arrow.homMk
    (horizontalPrevTotalHomologyFiltrationMapOfBicomplex f p q)
    (horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex f p q)
    (horizontalTotalHomologyFiltrationStepMap_naturality f p q).symm

@[simp]
theorem horizontalTotalHomologyFiltrationStepSquareOfBicomplex_left
    (f : K ⟶ L) (p q : ℕ) :
    (horizontalTotalHomologyFiltrationStepSquareOfBicomplex f p q).left =
      horizontalPrevTotalHomologyFiltrationMapOfBicomplex f p q :=
  rfl

@[simp]
theorem horizontalTotalHomologyFiltrationStepSquareOfBicomplex_right
    (f : K ⟶ L) (p q : ℕ) :
    (horizontalTotalHomologyFiltrationStepSquareOfBicomplex f p q).right =
      horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex f p q :=
  rfl

/-- The map induced by a bicomplex morphism on a horizontal associated
graded piece of total homology. -/
noncomputable def horizontalTotalHomologyGradedPieceMapOfBicomplex
    (f : K ⟶ L) (p q : ℕ) :
    horizontalTotalHomologyGradedPiece K p q ⟶
      horizontalTotalHomologyGradedPiece L p q :=
  (Limits.coker C).map
    (horizontalTotalHomologyFiltrationStepSquareOfBicomplex f p q)

end HomologicalComplex₂

end
