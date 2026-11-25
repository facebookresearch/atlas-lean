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

example (m k : ℕ)
    (hkdeg : ComplexShape.embeddingDownNat.f k =
      ComplexShape.embeddingDownNat.f (k + 1) + 1) :
    let Q :
        (B.partialTotalStepCochainShortComplex (m + 1)).X₁ ⟶
          (B.totalRow m).extend ComplexShape.embeddingDownNat :=
      (B.partialTotalAdjacentStepCochainIso m).hom ≫
        (B.partialTotalStepCochainShortComplex m).g ≫
        (B.partialTotalStepCochainX₃Iso m).hom
    HEq
      (Q.f (ComplexShape.embeddingDownNat.f (k + 1) + 1) ≫
        (CochainComplex.shiftFunctorObjXIso
          ((B.totalRow m).extend ComplexShape.embeddingDownNat) 1
          (ComplexShape.embeddingDownNat.f (k + 1))
          (ComplexShape.embeddingDownNat.f k) hkdeg).hom)
      (B.partialTotalRowQuotientF m k ≫
        ((B.totalRow m).extendXIso ComplexShape.embeddingDownNat
          (i := k) (i' := ComplexShape.embeddingDownNat.f k) rfl).inv) :=
  B.partialTotalAdjacentTargetMap_f_comp_shiftIso_heq m k hkdeg

example :
    let Q :
        (B.partialTotalStepCochainShortComplex (0 + 1)).X₁ ⟶
          (B.totalRow 0).extend ComplexShape.embeddingDownNat :=
      (B.partialTotalAdjacentStepCochainIso 0).hom ≫
        (B.partialTotalStepCochainShortComplex 0).g ≫
        (B.partialTotalStepCochainX₃Iso 0).hom
    HEq
      (Q.f (ComplexShape.embeddingDownNat.f (0 + 1) + 1) ≫
        (CochainComplex.shiftFunctorObjXIso
          ((B.totalRow 0).extend ComplexShape.embeddingDownNat) 1
          (ComplexShape.embeddingDownNat.f (0 + 1))
          (ComplexShape.embeddingDownNat.f 0) (by
            change -(0 : ℤ) = -(1 : ℤ) + 1
            omega)).hom)
      (B.partialTotalRowQuotientF 0 0 ≫
        ((B.totalRow 0).extendXIso ComplexShape.embeddingDownNat
          (i := 0) (i' := ComplexShape.embeddingDownNat.f 0) rfl).inv) := by
  simpa only using
    B.partialTotalAdjacentTargetMap_f_comp_shiftIso_heq 0 0 (by
      change -(0 : ℤ) = -(1 : ℤ) + 1
      omega)

example :
    let Q :
        (B.partialTotalStepCochainShortComplex (1 + 1)).X₁ ⟶
          (B.totalRow 1).extend ComplexShape.embeddingDownNat :=
      (B.partialTotalAdjacentStepCochainIso 1).hom ≫
        (B.partialTotalStepCochainShortComplex 1).g ≫
        (B.partialTotalStepCochainX₃Iso 1).hom
    HEq
      (Q.f (ComplexShape.embeddingDownNat.f (0 + 1) + 1) ≫
        (CochainComplex.shiftFunctorObjXIso
          ((B.totalRow 1).extend ComplexShape.embeddingDownNat) 1
          (ComplexShape.embeddingDownNat.f (0 + 1))
          (ComplexShape.embeddingDownNat.f 0) (by
            change -(0 : ℤ) = -(1 : ℤ) + 1
            omega)).hom)
      (B.partialTotalRowQuotientF 1 0 ≫
        ((B.totalRow 1).extendXIso ComplexShape.embeddingDownNat
          (i := 0) (i' := ComplexShape.embeddingDownNat.f 0) rfl).inv) := by
  simpa only using
    B.partialTotalAdjacentTargetMap_f_comp_shiftIso_heq 1 0 (by
      change -(0 : ℤ) = -(1 : ℤ) + 1
      omega)

end HomologicalComplex₂

end
