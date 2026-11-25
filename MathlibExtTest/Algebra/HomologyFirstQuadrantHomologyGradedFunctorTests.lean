/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantHomologyGradedFunctor

/-! # Tests for the total-homology associated-graded functor -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂.FirstQuadrantHomologyGradedFunctorTests

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalPrevTotalHomologyFiltrationFunctor
#check horizontalCurrentTotalHomologyFiltrationFunctor
#check horizontalTotalHomologyFiltrationStepNatTrans
#check horizontalTotalHomologyFiltrationStepArrowFunctor
#check horizontalTotalHomologyGradedPieceFunctor
#check horizontalTotalHomologyGradedPieceMapOfBicomplex_id
#check horizontalTotalHomologyGradedPieceMapOfBicomplex_comp

example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (p q : ℕ) :
    (horizontalPrevTotalHomologyFiltrationFunctor
      (C := C) p q).obj K =
      (horizontalTotalHomologyFiltration K (p + q)).obj
        ((((p : ℤ) - 1 : ℤ) : EInt)) := by
  simp

example (f : K ⟶ L) (p q : ℕ) :
    (horizontalPrevTotalHomologyFiltrationFunctor
      (C := C) p q).map f =
      horizontalPrevTotalHomologyFiltrationMapOfBicomplex f p q := by
  simp

example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (p q : ℕ) :
    (horizontalCurrentTotalHomologyFiltrationFunctor
      (C := C) p q).obj K =
      (horizontalTotalHomologyFiltration K (p + q)).obj
        (((p : ℤ) : EInt)) := by
  simp

example (f : K ⟶ L) (p q : ℕ) :
    (horizontalCurrentTotalHomologyFiltrationFunctor
      (C := C) p q).map f =
      horizontalPositiveCurrentTotalHomologyFiltrationMapOfBicomplex f p q := by
  simp

example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (p q : ℕ) :
    (horizontalTotalHomologyFiltrationStepNatTrans
      (C := C) p q).app K =
      horizontalTotalHomologyFiltrationStepMap K p q := by
  simp

example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (p q : ℕ) :
    (horizontalTotalHomologyFiltrationStepArrowFunctor
      (C := C) p q).obj K =
      Arrow.mk (horizontalTotalHomologyFiltrationStepMap K p q) := by
  simp

example (f : K ⟶ L) (p q : ℕ) :
    (horizontalTotalHomologyFiltrationStepArrowFunctor
      (C := C) p q).map f =
      horizontalTotalHomologyFiltrationStepSquareOfBicomplex f p q := by
  simp

example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (p q : ℕ) :
    (horizontalTotalHomologyGradedPieceFunctor (C := C) p q).obj K =
      horizontalTotalHomologyGradedPiece K p q := by
  simp

example (f : K ⟶ L) (p q : ℕ) :
    (horizontalTotalHomologyGradedPieceFunctor (C := C) p q).map f =
      horizontalTotalHomologyGradedPieceMapOfBicomplex f p q := by
  simp

-- The zero column uses the genuine zero predecessor stage.
example (f : K ⟶ L) (q : ℕ) :
    (horizontalTotalHomologyGradedPieceFunctor (C := C) 0 q).map f =
      horizontalTotalHomologyGradedPieceMapOfBicomplex f 0 q := by
  simp

-- The first positive column uses finite predecessor stage zero.
example (f : K ⟶ L) (q : ℕ) :
    (horizontalTotalHomologyFiltrationStepArrowFunctor
      (C := C) 1 q).map f =
      horizontalTotalHomologyFiltrationStepSquareOfBicomplex f 1 q := by
  simp

-- Total degree `p` is covered when `q = 0`.
example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (p : ℕ) :
    (horizontalTotalHomologyGradedPieceFunctor (C := C) p 0).obj K =
      horizontalTotalHomologyGradedPiece K p 0 := by
  simp

-- The bidegree `(0,0)` map is the landed graded-piece map.
example (f : K ⟶ L) :
    (horizontalTotalHomologyGradedPieceFunctor (C := C) 0 0).map f =
      horizontalTotalHomologyGradedPieceMapOfBicomplex f 0 0 := by
  simp

example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (p q : ℕ) :
    horizontalTotalHomologyGradedPieceMapOfBicomplex (𝟙 K) p q = 𝟙 _ := by
  simp

example (f : K ⟶ L) (g : L ⟶ M) (p q : ℕ) :
    horizontalTotalHomologyGradedPieceMapOfBicomplex (f ≫ g) p q =
      horizontalTotalHomologyGradedPieceMapOfBicomplex f p q ≫
        horizontalTotalHomologyGradedPieceMapOfBicomplex g p q := by
  simp

#print axioms horizontalPrevTotalHomologyFiltrationFunctor
#print axioms horizontalCurrentTotalHomologyFiltrationFunctor
#print axioms horizontalTotalHomologyFiltrationStepNatTrans
#print axioms horizontalTotalHomologyFiltrationStepArrowFunctor
#print axioms horizontalTotalHomologyGradedPieceFunctor
#print axioms horizontalTotalHomologyGradedPieceMapOfBicomplex_id
#print axioms horizontalTotalHomologyGradedPieceMapOfBicomplex_comp

end HomologicalComplex₂.FirstQuadrantHomologyGradedFunctorTests

end
