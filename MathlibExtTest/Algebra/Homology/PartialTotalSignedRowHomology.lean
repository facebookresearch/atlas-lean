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

public import MathlibExt.Algebra.Homology.PartialTotalSignedRowHomology

/-!
# Tests for signed-row homology coordinates
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory

universe v u

namespace HomologicalComplex₂

section SignedRow

variable {C : Type u} [Category.{v} C] [Preadditive C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

example : B.signedRow 0 ≅ B.X 0 :=
  B.signedRowIso 0

example (q : ℕ) :
    (B.signedRowIso 1).hom.f q =
      (-1 : ℤˣ) ^ q • 𝟙 ((B.X 1).X q) := by
  simpa using B.signedRowIso_hom_f 1 q

example (p q : ℕ) :
    (B.signedRowIso p).inv.f q =
      (((ComplexShape.down ℕ).ε p) ^ q)⁻¹ •
        𝟙 ((B.X p).X q) :=
  B.signedRowIso_inv_f p q

example (p : ℕ) :
    (B.signedRowIso p).hom.f 0 = 𝟙 ((B.X p).X 0) := by
  simpa using B.signedRowIso_hom_f p 0

end SignedRow

section Homology

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

example (p q : ℕ) :
    (B.totalRow p).homology (p + q) ≅ (B.X p).homology q :=
  B.totalRowHomologyIso p q

example :
    (B.totalRow 0).homology 0 ≅ (B.X 0).homology 0 :=
  B.totalRowHomologyIso 0 0

example (p q n : ℕ) (h : p + q = n) :
    (B.totalRow p).homology n ≅ (B.X p).homology q :=
  B.totalRowHomologyIsoAt p q n h

example (p q n : ℕ) (h : p + q = n) :
    B.totalRowHomologyIsoAt p q n h =
      (B.signedRow p).extendHomologyIso
          (ComplexShape.embeddingDown'Add 1 p) (by
            change q + p = n
            omega) ≪≫
        HomologicalComplex.homologyMapIso (B.signedRowIso p) q := by
  rfl

example (p q : ℕ) :
    (B.totalRow p).homology (p + q) ≅ (B.X p).homology q :=
  B.totalRowHomologyIsoAt p q (p + q) rfl

example (p q : ℕ) :
    (B.totalRow p).homology (q + p) ≅ (B.X p).homology q :=
  B.totalRowHomologyIsoAt p q (q + p) (Nat.add_comm p q)

example (q : ℕ) :
    (B.totalRow 0).homology q ≅ (B.X 0).homology q :=
  B.totalRowHomologyIsoAt 0 q q (Nat.zero_add q)

example :
    (B.totalRow 0).homology 0 ≅ (B.X 0).homology 0 :=
  B.totalRowHomologyIsoAt 0 0 0 rfl

example :
    (B.totalRow 0).homology 1 ≅ (B.X 0).homology 1 :=
  B.totalRowHomologyIsoAt 0 1 1 rfl

example (p : ℕ) :
    (B.totalRow p).homology p ≅ (B.X p).homology 0 :=
  B.totalRowHomologyIsoAt p 0 p (Nat.add_zero p)

example (p : ℕ) :
    (B.totalRow p).homology (p + 1) ≅ (B.X p).homology 1 :=
  B.totalRowHomologyIsoAt p 1 (p + 1) rfl

example (p q n : ℕ) (h : p + q = n) :=
  HomologicalComplex₂.totalRowHomologyIsoAt
    (B := (HomologicalComplex.zero :
      HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)))
    p q n h

end Homology

end HomologicalComplex₂

end
