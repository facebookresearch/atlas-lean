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

local notation "core" =>
  CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat

example (m q : ℕ) :
    (B.totalRow (m + 1)).homology (m + 1 + q) ⟶
      (B.totalRow m).homology (m + q) :=
  B.partialTotalE₁RowDifferential m q

example (m q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page 1).d
        (m + 1, q) (m, q) =
      (B.partialTotalSpectralSequenceFirstPageRowIso (m + 1) q).hom ≫
        B.partialTotalE₁RowDifferential m q ≫
        (B.partialTotalSpectralSequenceFirstPageRowIso m q).inv :=
  B.partialTotalSpectralSequenceFirstPage_d_eq m q

example (q : ℕ) (pq' : ℕ × ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page 1).d
      (0, q) pq' = 0 :=
  B.partialTotalSpectralSequenceFirstPage_d_zero q pq'

end HomologicalComplex₂

end
