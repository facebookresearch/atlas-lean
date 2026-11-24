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

public import MathlibExt.Algebra.Homology.PartialTotalZero

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteCoproducts C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

example (n : ℕ) :
    B.partialTotalRowQuotientF 0 n ≫
      B.partialTotalRowQuotientSectionF 0 n = 𝟙 _ :=
  B.partialTotalRowQuotientF_zero_comp_sectionF n

example : ShortComplex (ChainComplex C ℕ) :=
  B.partialTotalZeroShortComplex

example (n : ℕ) :
    ((B.partialTotalZeroShortComplex).map
      (HomologicalComplex.eval C (ComplexShape.down ℕ) n)).Splitting :=
  B.partialTotalZeroDegreeSplitting n

example (n : ℕ) :
    ((B.partialTotalZeroShortComplex).map
      (HomologicalComplex.eval C (ComplexShape.down ℕ) n)).ShortExact :=
  B.partialTotalZeroDegreewiseShortExact n

section Abelian

variable {D : Type u} [Category.{v} D] [Abelian D]

example (B : HomologicalComplex₂ D (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) :
    B.partialTotalZeroShortComplex.ShortExact :=
  B.partialTotalZeroShortExact

end Abelian

end HomologicalComplex₂

end
