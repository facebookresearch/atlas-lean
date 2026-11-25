/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantGradedPieceCokernelIso

/-! # Tests for the horizontal graded-piece cokernel isomorphism -/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantGradedPieceCokernelIsoTests

section

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example (p : ℕ) : ShortComplex (CochainComplex C ℤ) :=
  horizontalNaturalSuccCochainShortComplex K p

example (p : ℕ) (i : ℤ) :
    ((horizontalNaturalSuccCochainShortComplex K p).map
      (HomologicalComplex.eval C (ComplexShape.up ℤ) i)).Splitting :=
  horizontalNaturalSuccCochainEvalSplitting K p i

example (q : ℕ) :
    horizontalFilteredTotalObj K 0 (0 + q) ≅ (K.X 0).X q :=
  horizontalFilteredTopProjectionZeroIso K q

end

section

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example (p : ℕ) :
    (horizontalFirstPageDirectColumnShortComplex K p).ShortExact :=
  horizontalFirstPageDirectColumnShortExact K p

example (p : ℕ) :
    IsColimit (CokernelCofork.ofπ
      (horizontalCompleteDirectColumnProjectionMap K p)
      (horizontalFirstPageFiltrationMap_projection_zero K p)) :=
  horizontalCompleteDirectColumnProjectionMapIsCokernel K p

example (p : ℕ) :
    cokernel (horizontalFirstPageFiltrationMap K p) ≅
      horizontalDirectColumnCochain K p :=
  horizontalFirstPageCokernelIso K p

example (p : ℕ) :
    (horizontalFirstPageCokernelIso K p).hom =
      horizontalFirstPageCokernelToDirectColumn K p := rfl

example (p : ℕ) :
    IsIso (horizontalFirstPageCokernelToDirectColumn K p) := inferInstance

end

end HomologicalComplex₂.FirstQuadrantGradedPieceCokernelIsoTests

end
