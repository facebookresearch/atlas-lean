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

public import MathlibExt.Algebra.Homology.PartialTotalStepVanishing

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

example (n : ℤ) :
    (CochainComplex.mappingCone
        (B.partialTotalStepCochainShortComplex 0).f).homology n ≅
      ((B.totalRow 0).extend ComplexShape.embeddingDownNat).homology n :=
  B.partialTotalStepConeExtendedRowHomologyIso 0 n

example (m : ℕ) (n : ℤ) :
    (CochainComplex.mappingCone
        (B.partialTotalStepCochainShortComplex (m + 1)).f).homology n ≅
      ((B.totalRow (m + 1)).extend
        ComplexShape.embeddingDownNat).homology n :=
  B.partialTotalStepConeExtendedRowHomologyIso (m + 1) n

example (p k : ℕ) (h : k < p) :
    IsZero ((CochainComplex.mappingCone
      (B.partialTotalStepCochainShortComplex p).f).homology (-(k : ℤ))) :=
  B.isZero_partialTotalStepConeHomology_of_lt p k h

example (m : ℕ) :
    IsZero ((CochainComplex.mappingCone
      (B.partialTotalStepCochainShortComplex (m + 1)).f).homology
        (-(m : ℤ))) :=
  B.isZero_partialTotalStepConeHomology_of_lt (m + 1) m (by omega)

end HomologicalComplex₂

end
