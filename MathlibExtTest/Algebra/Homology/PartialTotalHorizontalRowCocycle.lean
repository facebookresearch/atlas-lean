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

public import MathlibExt.Algebra.Homology.PartialTotalHorizontalRowCocycle

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

section Cochain

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteCoproducts C]

local instance : HasFiniteBiproducts C :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

example :
    (B.totalRow 1).d 2 1 ≫ B.partialTotalHorizontalRowF 0 0 +
      B.partialTotalHorizontalRowF 0 1 ≫ (B.totalRow 0).d 1 0 = 0 :=
  B.partialTotalHorizontalRowF_anticomm 0 0

example :
    (B.totalRow 2).d 2 1 ≫ B.partialTotalHorizontalRowF 1 0 +
      B.partialTotalHorizontalRowF 1 1 ≫ (B.totalRow 1).d 1 0 = 0 :=
  B.partialTotalHorizontalRowF_anticomm 1 0

example :
    (B.partialTotalHorizontalRowCochain 0).v
        (ComplexShape.embeddingDownNat.f 1)
        (ComplexShape.embeddingDownNat.f 0) (by
          change -((1 : ℕ) : ℤ) + 1 = -((0 : ℕ) : ℤ)
          omega) =
      ((B.totalRow 1).extendXIso
          ComplexShape.embeddingDownNat rfl).hom ≫
        B.partialTotalHorizontalRowF 0 0 ≫
        ((B.totalRow 0).extendXIso
          ComplexShape.embeddingDownNat rfl).inv :=
  B.partialTotalHorizontalRowCochain_v 0 0

example : (B.partialTotalHorizontalRowCochain 0).v 0 1 rfl = 0 :=
  B.partialTotalHorizontalRowCochain_v_zero 0

example :
    (B.partialTotalHorizontalRowCocycle 0).1.v
        (ComplexShape.embeddingDownNat.f 1)
        (ComplexShape.embeddingDownNat.f 0) (by
          change -((1 : ℕ) : ℤ) + 1 = -((0 : ℕ) : ℤ)
          omega) =
      ((B.totalRow 1).extendXIso
          ComplexShape.embeddingDownNat rfl).hom ≫
        B.partialTotalHorizontalRowF 0 0 ≫
        ((B.totalRow 0).extendXIso
          ComplexShape.embeddingDownNat rfl).inv :=
  B.partialTotalHorizontalRowCocycle_v 0 0

example :
    (B.partialTotalHorizontalRowCocycle 0).1.v 0 1 rfl = 0 := by
  simpa only [partialTotalHorizontalRowCocycle,
    CochainComplex.HomComplex.Cocycle.mk_coe] using
      B.partialTotalHorizontalRowCochain_v_zero 0

example :
    (B.partialTotalHorizontalRowShift 0).f
        (ComplexShape.embeddingDownNat.f 1) ≫
      (CochainComplex.shiftFunctorObjXIso
        ((B.totalRow 0).extend ComplexShape.embeddingDownNat)
        1 (ComplexShape.embeddingDownNat.f 1)
          (ComplexShape.embeddingDownNat.f 0) (by
            have h : ComplexShape.embeddingDownNat.f 1 + 1 =
                ComplexShape.embeddingDownNat.f 0 := by
              change -((1 : ℕ) : ℤ) + 1 = -((0 : ℕ) : ℤ)
              omega
            exact h.symm)).hom =
      ((B.totalRow 1).extendXIso
          ComplexShape.embeddingDownNat rfl).hom ≫
        B.partialTotalHorizontalRowF 0 0 ≫
        ((B.totalRow 0).extendXIso
          ComplexShape.embeddingDownNat rfl).inv :=
  B.partialTotalHorizontalRowShift_f_comp_shiftIso 0 0

end Cochain

section Homology

variable {D : Type u} [Category.{v} D] [Abelian D]

variable (A : HomologicalComplex₂ D (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

example (m q : ℕ) :
    (A.totalRow (m + 1)).homology (m + 1 + q) ⟶
      (A.totalRow m).homology (m + q) :=
  A.partialTotalHorizontalRowHomology m q

example :
    (A.totalRow 1).homology 1 ⟶ (A.totalRow 0).homology 0 :=
  A.partialTotalHorizontalRowHomology 0 0

example (m q : ℕ) :
    A.partialTotalHorizontalRowHomology m q =
      ((A.totalRow (m + 1)).extendHomologyIso
        ComplexShape.embeddingDownNat (show
          ComplexShape.embeddingDownNat.f (m + 1 + q) =
            -((m + 1 + q : ℕ) : ℤ) by rfl)).inv ≫
      (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) 0).shiftMap
        (A.partialTotalHorizontalRowShift m)
        (-((m + 1 + q : ℕ) : ℤ)) (-((m + q : ℕ) : ℤ)) (by omega) ≫
      ((A.totalRow m).extendHomologyIso
        ComplexShape.embeddingDownNat (show
          ComplexShape.embeddingDownNat.f (m + q) =
            -((m + q : ℕ) : ℤ) by rfl)).hom :=
  A.partialTotalHorizontalRowHomology_eq m q

end Homology

end HomologicalComplex₂

end
