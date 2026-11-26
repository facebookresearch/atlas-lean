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

public import MathlibExt.Algebra.Homology.PartialTotalStepHomology

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

example (p : ℕ) :
    HEq
      ((B.partialTotalStepCochainShortComplex p).g ≫
        (B.partialTotalStepCochainX₃Iso p).hom)
      (HomologicalComplex.extendMap
        (B.partialTotalRowQuotient p) ComplexShape.embeddingDownNat) :=
  B.partialTotalStepCochain_g_comp_X₃Iso_hom_heq p

example :
    (B.partialTotalStepCochainShortComplex 0).g ≫
        (B.partialTotalStepCochainX₃Iso 0).hom =
      HomologicalComplex.extendMap
        (B.partialTotalRowQuotient 0) ComplexShape.embeddingDownNat :=
  eq_of_heq (B.partialTotalStepCochain_g_comp_X₃Iso_hom_heq 0)

example (n : ℕ) :
    HEq ((B.partialTotalStepCochainX₃Iso 0).inv.f
      (ComplexShape.embeddingDownNat.f n))
      ((B.totalRow 0).extendXIso
        ComplexShape.embeddingDownNat (i := n)
          (i' := ComplexShape.embeddingDownNat.f n) rfl).hom :=
  B.partialTotalStepCochainX₃Iso_inv_f_heq 0 n

example (n : ℕ) :
    HEq ((B.partialTotalStepCochainX₃Iso 0).hom.f
      (ComplexShape.embeddingDownNat.f n))
      ((B.totalRow 0).extendXIso
        ComplexShape.embeddingDownNat (i := n)
          (i' := ComplexShape.embeddingDownNat.f n) rfl).inv :=
  B.partialTotalStepCochainX₃Iso_hom_f_heq 0 n

example (m n : ℕ) :
    HEq ((B.partialTotalStepCochainX₃Iso (m + 1)).inv.f
      (ComplexShape.embeddingDownNat.f n))
      ((B.totalRow (m + 1)).extendXIso
        ComplexShape.embeddingDownNat (i := n)
          (i' := ComplexShape.embeddingDownNat.f n) rfl).hom :=
  B.partialTotalStepCochainX₃Iso_inv_f_heq (m + 1) n

example (m n : ℕ) :
    HEq ((B.partialTotalStepCochainX₃Iso (m + 1)).hom.f
      (ComplexShape.embeddingDownNat.f n))
      ((B.totalRow (m + 1)).extendXIso
        ComplexShape.embeddingDownNat (i := n)
          (i' := ComplexShape.embeddingDownNat.f n) rfl).inv :=
  B.partialTotalStepCochainX₃Iso_hom_f_heq (m + 1) n

example (p q : ℕ) :
    CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.deg
        (p, q) =
      -((p + q : ℕ) : ℤ) :=
  coreE₁IncreasingHomologicalNat_deg_eq p q

example (p q : ℕ) :
    B.partialTotalStepE₁Homology p q ≅
      (B.totalRow p).homology (p + q) :=
  B.partialTotalStepE₁HomologyIso p q

example (q : ℕ) :
    B.partialTotalStepE₁Homology 0 q ≅
      (B.totalRow 0).homology (0 + q) :=
  B.partialTotalStepE₁HomologyIso 0 q

example (m q : ℕ) :
    B.partialTotalStepE₁Homology (m + 1) q ≅
      (B.totalRow (m + 1)).homology (m + 1 + q) :=
  B.partialTotalStepE₁HomologyIso (m + 1) q

example (p q n : ℕ) (h : p + q = n) :
    B.partialTotalStepE₁Homology p q ≅
      (B.totalRow p).homology n :=
  B.partialTotalStepE₁HomologyIsoAt p q n h

example (p q : ℕ) :
    B.partialTotalStepE₁Homology p q ≅
      (B.totalRow p).homology (p + q) :=
  B.partialTotalStepE₁HomologyIsoAt p q (p + q) rfl

example (p q : ℕ) :
    B.partialTotalStepE₁Homology p q ≅
      (B.totalRow p).homology (q + p) :=
  B.partialTotalStepE₁HomologyIsoAt p q (q + p) (Nat.add_comm p q)

example (q : ℕ) :
    B.partialTotalStepE₁Homology 0 q ≅
      (B.totalRow 0).homology q :=
  B.partialTotalStepE₁HomologyIsoAt 0 q q (Nat.zero_add q)

example (p : ℕ) :
    B.partialTotalStepE₁Homology p 0 ≅
      (B.totalRow p).homology p :=
  B.partialTotalStepE₁HomologyIsoAt p 0 p (Nat.add_zero p)

example :
    B.partialTotalStepE₁Homology 0 0 ≅
      (B.totalRow 0).homology 0 :=
  B.partialTotalStepE₁HomologyIsoAt 0 0 0 rfl

example :
    B.partialTotalStepE₁Homology 0 1 ≅
      (B.totalRow 0).homology 1 :=
  B.partialTotalStepE₁HomologyIsoAt 0 1 1 rfl

end HomologicalComplex₂

end
