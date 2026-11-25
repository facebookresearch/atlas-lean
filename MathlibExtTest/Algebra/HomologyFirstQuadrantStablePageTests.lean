/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantStablePage

/-! # Tests for stable first-quadrant pages -/

@[expose] public section

open CategoryTheory Limits
open CategoryTheory.ComposableArrows

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantStablePageTests

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example (p q : ℕ) :
    (p : ℤ) + 1 ≤ horizontalStablePageIndex p q :=
  horizontalStablePageIndex_lower_bound p q

example (r : ℤ) (p q : ℕ) (h : (p : ℤ) + 1 ≤ r) :
    IsZero (((horizontalCompleteFiltrationSpectralObject K).H
      (-((p + q : ℕ) : ℤ) + 1)).obj
        (mk₁ (homOfLE (horizontalStablePageLowerIndex_le r p h)))) :=
  horizontalStableLowerRelativeHomologyIsZero K r p q h

example (r : ℤ) (p q : ℕ) (h : (q : ℤ) + 2 ≤ r) :
    IsZero (((horizontalCompleteFiltrationSpectralObject K).H
      (-((p + q + 1 : ℕ) : ℤ))).obj
        (mk₁ (homOfLE (horizontalStablePageUpperIndex_le r p q h)))) :=
  horizontalStableUpperRelativeHomologyIsZero K r p q h

example (r : ℤ) (hr : 1 ≤ r) (p q : ℕ)
    (hlower : (p : ℤ) + 1 ≤ r) (hupper : (q : ℤ) + 2 ≤ r) :
    ((horizontalFirstQuadrantSpectralSequence K).page r).X (p, q) ≅
      horizontalFirstQuadrantAbutmentTerm K p q :=
  horizontalStablePageAbutmentIso K r hr p q hlower hupper

example (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page
      (horizontalStablePageIndex p q)).X (p, q) ≅
      horizontalFirstQuadrantAbutmentTerm K p q :=
  horizontalStablePageAbutmentIsoAtIndex K p q

end HomologicalComplex₂.FirstQuadrantStablePageTests

end
