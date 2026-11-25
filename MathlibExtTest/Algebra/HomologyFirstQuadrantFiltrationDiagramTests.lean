/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFiltrationDiagram

/-! # Tests for the canonical first-quadrant filtration -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂.FirstQuadrantFiltrationDiagramTests

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

example : CategoryTheory.Filtration
    (K.total (ComplexShape.down ℕ)) ℕ :=
  horizontalTotalFiltration K

example (k : ℕ) :
    (horizontalTotalFiltration K).obj k =
      horizontalFilteredTotalComplex K k :=
  rfl

example {k l : ℕ} (h : k ≤ l) :
    (horizontalTotalFiltration K).diagram.map (homOfLE h) =
      horizontalFilteredTotalComplexMap K h :=
  horizontalTotalFiltration_diagram_map K h

example (k : ℕ) :
    Mono ((horizontalTotalFiltration K).ι.app k) :=
  inferInstance

example (k n : ℕ) (h : n ≤ k) :
    ((horizontalTotalFiltration K).obj k).X n ≅
      (K.total (ComplexShape.down ℕ)).X n :=
  horizontalTotalFiltrationEvalIsoOfLE K k n h

end HomologicalComplex₂.FirstQuadrantFiltrationDiagramTests

end
