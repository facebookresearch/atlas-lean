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

public import MathlibExt.Algebra.Homology.PartialTotalSuccessorCochainSplitting

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

example (m : ℕ) (i : ℤ) :
    ((B.partialTotalStepCochainShortComplex (m + 1)).map
      (HomologicalComplex.eval C (ComplexShape.up ℤ) i)).Splitting :=
  B.partialTotalSuccessorCochainSplitting m i

example (m k : ℕ) :
    HEq
      (B.partialTotalSuccessorCochainSplitting m
        (ComplexShape.embeddingDownNat.f k)).s
      (((B.totalRow (m + 1)).extendXIso
          ComplexShape.embeddingDownNat
          (i := k) (i' := ComplexShape.embeddingDownNat.f k) rfl).hom ≫
        B.partialTotalRowQuotientSectionF (m + 1) k ≫
        ((B.partialTotal (m + 1)).extendXIso
          ComplexShape.embeddingDownNat
          (i := k) (i' := ComplexShape.embeddingDownNat.f k) rfl).inv) :=
  B.partialTotalSuccessorCochainSplitting_s m k

example (m k : ℕ) {i : ℤ}
    (h : ComplexShape.embeddingDownNat.f k = i) :
    HEq (B.partialTotalSuccessorCochainSplitting m i).r
      (((B.partialTotal (m + 1)).extendXIso
          ComplexShape.embeddingDownNat
          (i := k) (i' := i) h).hom ≫
        B.partialTotalSuccRetractionF m k ≫
        ((B.partialTotal m).extendXIso
          ComplexShape.embeddingDownNat
          (i := k) (i' := i) h).inv) :=
  B.partialTotalSuccessorCochainSplitting_r m k h

example :
    HEq
      (B.partialTotalSuccessorCochainSplitting 0
        (ComplexShape.embeddingDownNat.f 0)).s
      (((B.totalRow 1).extendXIso ComplexShape.embeddingDownNat
          (i := 0) (i' := ComplexShape.embeddingDownNat.f 0) rfl).hom ≫
        B.partialTotalRowQuotientSectionF 1 0 ≫
        ((B.partialTotal 1).extendXIso ComplexShape.embeddingDownNat
          (i := 0) (i' := ComplexShape.embeddingDownNat.f 0) rfl).inv) :=
  B.partialTotalSuccessorCochainSplitting_s 0 0

example :
    HEq (B.partialTotalSuccessorCochainSplitting 0 0).r
      (((B.partialTotal 1).extendXIso ComplexShape.embeddingDownNat
          (i := 0) (i' := 0) (by
            change -((0 : ℕ) : ℤ) = (0 : ℤ)
            omega)).hom ≫
        B.partialTotalSuccRetractionF 0 0 ≫
        ((B.partialTotal 0).extendXIso ComplexShape.embeddingDownNat
          (i := 0) (i' := 0) (by
            change -((0 : ℕ) : ℤ) = (0 : ℤ)
            omega)).inv) := by
  simpa only using
    B.partialTotalSuccessorCochainSplitting_r 0 0 (i := 0) (by
      change -((0 : ℕ) : ℤ) = (0 : ℤ)
      omega)

end HomologicalComplex₂

end
