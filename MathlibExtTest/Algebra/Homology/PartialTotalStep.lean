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

public import MathlibExt.Algebra.Homology.PartialTotalStep

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteCoproducts C]

local instance : HasFiniteBiproducts C :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

example : B.partialTotalStepShortComplex 0 =
    B.partialTotalZeroShortComplex :=
  B.partialTotalStepShortComplex_zero

example (m : ℕ) : B.partialTotalStepShortComplex (m + 1) =
    B.partialTotalSuccShortComplex m :=
  B.partialTotalStepShortComplex_succ m

example (p : ℕ) :
    (B.partialTotalStepShortComplex p).X₂ = B.partialTotal p :=
  B.partialTotalStepShortComplex_X₂ p

example (p : ℕ) :
    (B.partialTotalStepShortComplex p).X₃ = B.totalRow p :=
  B.partialTotalStepShortComplex_X₃ p

example : (B.partialTotalStepShortComplex 0).g =
    B.partialTotalRowQuotient 0 :=
  B.partialTotalStepShortComplex_g_zero

example (m : ℕ) : (B.partialTotalStepShortComplex (m + 1)).g =
    B.partialTotalRowQuotient (m + 1) :=
  B.partialTotalStepShortComplex_g_succ m

example (p : ℕ) : ShortComplex (CochainComplex C ℤ) :=
  B.partialTotalStepCochainShortComplex p

example (m : ℕ) :
    B.partialTotalStepCochainShortComplex (m + 1) =
      (B.partialTotalSuccShortComplex m).map
        (ComplexShape.embeddingDownNat.extendFunctor C) :=
  B.partialTotalStepCochainShortComplex_succ m

section Abelian

variable {D : Type u} [Category.{v} D] [Abelian D]

example (B : HomologicalComplex₂ D (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) (p : ℕ) :
    (B.partialTotalStepShortComplex p).ShortExact :=
  B.partialTotalStepShortExact p

example (B : HomologicalComplex₂ D (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) (p : ℕ) :
    (B.partialTotalStepCochainShortComplex p).ShortExact :=
  B.partialTotalStepCochainShortExact p

end Abelian

end HomologicalComplex₂

end
