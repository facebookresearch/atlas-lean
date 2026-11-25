/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageDifferential

/-! # Tests for the actual first-page differential comparison -/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantFirstPageDifferentialTests

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example (p : ℕ) :
    horizontalFirstPageCoherentSuccessorMap K p =
      horizontalFirstPageNextFiltrationMap K p :=
  horizontalFirstPageCoherentSuccessorMap_eq_next K p

example (p : ℕ) :
    (horizontalFirstPageCoherentAdjacentShortComplexIso K p).hom.τ₃ =
      (horizontalFirstPageCoherentAdjacentShortComplexIso K (p + 1)).hom.τ₁ :=
  horizontalFirstPageCoherentAdjacentShortComplexIso_endpoint_coherence K p

example (p q : ℕ) :
    horizontalFirstPageCoherentConnectingMap K p q =
      horizontalFirstPageAdjacentConnectingMap K p q :=
  horizontalFirstPageCoherentConnectingMap_eq_adjacent K p q

example (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page 1).d
        (p + 1, q) (p, q) ≫
      (horizontalFirstPageCoherentDirectColumnIso K p q).hom =
    (horizontalFirstPageCoherentDirectColumnIso K (p + 1) q).hom ≫
      horizontalFirstPageAdjacentConnectingMap K p q :=
  horizontalFirstPage_d_coherentDirectColumn_eq_adjacent K p q

example (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page 1).d
        (p + 1, q) (p, q) ≫
      (horizontalFirstPageCoherentVerticalHomologyIso K p q).hom =
    (horizontalFirstPageCoherentVerticalHomologyIso K (p + 1) q).hom ≫
      (((q + 1 : ℕ) : ℤ).negOnePow •
        horizontalFirstPageHorizontalHomologyMap K p q) :=
  horizontalFirstPage_d_coherentVerticalHomology_eq_horizontal K p q

end HomologicalComplex₂.FirstQuadrantFirstPageDifferentialTests

end
