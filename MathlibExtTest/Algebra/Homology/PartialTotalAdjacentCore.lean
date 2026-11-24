/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.PartialTotalAdjacentCore

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

example (m q : ℕ) :
    B.partialTotalCochainFiltration.obj
        (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.i₂
          (m, q)) ⟶
      B.partialTotalCochainFiltration.obj
        (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.i₂
          (m + 1, q)) :=
  B.partialTotalE₁CoreSuccessorMap m q

example (m q : ℕ) :
    (B.partialTotalStepCochainShortComplex m).X₂ ⟶
      (B.partialTotalStepCochainShortComplex (m + 1)).X₂ :=
  B.partialTotalE₁AdjacentCochainMap m q

example (m q : ℕ) :
    B.partialTotalE₁AdjacentCoreDiagram m q ≅
      B.partialTotalE₁AdjacentStepDiagram m q :=
  B.partialTotalE₁AdjacentDiagramIso m q

example (q : ℕ) :
    B.partialTotalE₁AdjacentCoreDiagram 0 q ≅
      B.partialTotalE₁AdjacentStepDiagram 0 q :=
  B.partialTotalE₁AdjacentDiagramIso 0 q

end HomologicalComplex₂

end
