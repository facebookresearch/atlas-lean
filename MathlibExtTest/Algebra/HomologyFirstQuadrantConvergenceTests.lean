/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantConvergence

/-! # Tests for bounded first-quadrant convergence -/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantConvergenceTests

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example (p q : ℕ) :
    (horizontalCompleteFilteredTotalComplex K
      (horizontalAbutmentUpperIndex p q)).homology (p + q) ≅
      (K.total (ComplexShape.down ℕ)).homology (p + q) :=
  horizontalAbutmentUpperHomologyToTotalIso K p q

example (p q : ℕ) :
    CategoryTheory.imageCompMap
        (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
        (horizontalCanonicalAbutmentToUpperHomologyMap K p q) ≫
      (horizontalCanonicalAbutmentCurrentImageIso K p q).hom =
    (horizontalCanonicalAbutmentPreviousImageIso K p q).hom ≫
      horizontalTotalHomologyFiltrationStepMap K p q :=
  horizontalCanonicalAbutmentImageSquare K p q

example (p q : ℕ) :
    horizontalFirstQuadrantCanonicalAbutmentTerm K p q ≅
      horizontalTotalHomologyGradedPiece K p q :=
  horizontalCanonicalAbutmentGradedIso K p q

example (r : ℤ) (hr : 1 ≤ r) (p q : ℕ)
    (hlower : (p : ℤ) + 1 ≤ r) (hupper : (q : ℤ) + 2 ≤ r) :
    ((horizontalFirstQuadrantSpectralSequence K).page r).X (p, q) ≅
      horizontalTotalHomologyGradedPiece K p q :=
  horizontalStablePageGradedIso K r hr p q hlower hupper

example (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page
      (horizontalStablePageIndex p q)).X (p, q) ≅
      horizontalTotalHomologyGradedPiece K p q :=
  horizontalStablePageGradedIsoAtIndex K p q

end HomologicalComplex₂.FirstQuadrantConvergenceTests

end
