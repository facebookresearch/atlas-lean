/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFiltrationMaps

/-! # Tests for first-quadrant filtration maps -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂.FirstQuadrantFiltrationMapsTests

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example {k l : ℕ} (h : k ≤ l) :
    horizontalFilteredTotalComplex K k ⟶
      horizontalFilteredTotalComplex K l :=
  horizontalFilteredTotalComplexMap K h

example (k n : ℕ) (h : n ≤ k) :
    horizontalFilteredTotalObj K k n ≅
      (K.total (ComplexShape.down ℕ)).X n :=
  horizontalFilteredTotalIsoOfLE K k n h

end HomologicalComplex₂.FirstQuadrantFiltrationMapsTests

end
