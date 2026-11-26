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

public import MathlibExt.Algebra.Homology.PartialTotalFirstPageDifferential
public import MathlibExt.Algebra.Homology.PartialTotalConnectingDifferential

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

example (m : ℕ) :
    (B.partialTotalStepCochainShortComplex (m + 1)).X₁ ≅
      (B.partialTotalStepCochainShortComplex m).X₂ :=
  B.partialTotalAdjacentStepCochainIso m

example (m n : ℕ) :
    HEq ((B.partialTotalAdjacentStepCochainIso m).hom.f
      (ComplexShape.embeddingDownNat.f n))
      (𝟙 ((B.partialTotal m).X n)) :=
  B.partialTotalAdjacentStepCochainIso_hom_f_heq m n

example :
    HEq ((B.partialTotalAdjacentStepCochainIso 0).hom.f
      (ComplexShape.embeddingDownNat.f 0))
      (𝟙 ((B.partialTotal 0).X 0)) :=
  B.partialTotalAdjacentStepCochainIso_hom_f_heq 0 0

example (m q : ℕ) :
    (B.totalRow (m + 1)).homology (m + 1 + q) ⟶
      (B.totalRow m).homology (m + q) :=
  B.partialTotalE₁ConnectingDifferential m q

example (q : ℕ) :
    (B.totalRow 1).homology (1 + q) ⟶
      (B.totalRow 0).homology (0 + q) :=
  B.partialTotalE₁ConnectingDifferential 0 q

example (q : ℕ) (pq' : ℕ × ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence
      CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat).page 1).d
        (0, q) pq' = 0 :=
  B.partialTotalSpectralSequenceFirstPage_d_zero q pq'

end HomologicalComplex₂

end
