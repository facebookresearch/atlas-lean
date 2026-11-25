/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantTotal

/-! # Tests for finite first-quadrant total complexes -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂.FirstQuadrantTotalTests

example (n : ℕ) : DownNatTotalFiber n ≃ Fin (n + 1) :=
  downNatTotalFiberEquivFin n

example (n k : ℕ) (h : n ≤ k) :
    DownNatHorizontalFilteredFiber n k ≃ DownNatTotalFiber n :=
  downNatHorizontalFilteredFiberEquiv n k h

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteCoproducts C]

example (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) (n : ℕ) :
    (K.total (ComplexShape.down ℕ)).X n ≅
      ∐ fun p : Fin (n + 1) => (K.X p.val).X (n - p.val) :=
  firstQuadrantTotalXIso K n

end HomologicalComplex₂.FirstQuadrantTotalTests

end
