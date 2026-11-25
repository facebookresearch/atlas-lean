/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageBoundaryComparison

/-! # Tests for the first-page boundary comparison -/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantFirstPageBoundaryComparisonTests

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example (p q : ℕ) :
    (horizontalFirstPageCokernelIso K p).inv.f (-(p : ℤ) - q) =
      horizontalCompleteDirectColumnSupportedSection K p q ≫
        (cokernel.π (horizontalFirstPageFiltrationMap K p)).f
          (-(p : ℤ) - q) :=
  horizontalFirstPageCokernelIso_inv_f_supported K p q

example (p q : ℕ) :
    horizontalFirstPageAdjacentBoundaryCycles K p q =
      horizontalDirectColumnRawHorizontalRepresentative K p q :=
  horizontalFirstPageAdjacentBoundaryCycles_eq_raw K p q

example (p q : ℕ) :
    (horizontalDirectColumnCochain K p).liftCycles
        (horizontalFirstPageAdjacentBoundaryCycles K p q)
        (-(p : ℤ) - q + 1) (by simp)
        (horizontalFirstPageAdjacentBoundaryCycles_d K p q) =
      ((q + 1 : ℕ) : ℤ).negOnePow •
        horizontalDirectColumnHorizontalCyclesMap K p q :=
  horizontalFirstPageAdjacentBoundaryLiftCycles_eq_horizontal K p q

example (p q : ℕ) :
    horizontalFirstPageAdjacentConnectingMap K p q =
      ((q + 1 : ℕ) : ℤ).negOnePow •
        ((horizontalDirectColumnHomologyIso K (p + 1) q).hom ≫
          HomologicalComplex.homologyMap (K.d (p + 1) p) q ≫
          (horizontalDirectColumnHomologyIso K p q).inv) :=
  horizontalFirstPageAdjacentConnectingMap_eq_horizontal K p q

example (p q : ℕ) :
    horizontalFirstPageAdjacentVerticalConnectingMap K p q =
      ((q + 1 : ℕ) : ℤ).negOnePow •
        horizontalFirstPageHorizontalHomologyMap K p q :=
  horizontalFirstPageAdjacentVerticalConnectingMap_eq_horizontal K p q

end HomologicalComplex₂.FirstQuadrantFirstPageBoundaryComparisonTests

end
