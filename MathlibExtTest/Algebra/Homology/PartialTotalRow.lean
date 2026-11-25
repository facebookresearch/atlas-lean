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

public import MathlibExt.Algebra.Homology.PartialTotalRow

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))
variable {B' B'' : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

example (p : ℕ) : ChainComplex C ℕ :=
  B.totalRow p

example (p q : ℕ) :
    (B.totalRow p).X (p + q) ≅ (B.X p).X q :=
  B.totalRowXIso p q (p + q) rfl

example (p n : ℕ) (h : n < p) :
    IsZero ((B.totalRow p).X n) :=
  B.totalRow_isZero_X p n h

example (p q q' n n' : ℕ) (h : p + q = n) (h' : p + q' = n') :
    (B.totalRowXIso p q n h).inv ≫ (B.totalRow p).d n n' =
      ((ComplexShape.down ℕ).ε p • (B.X p).d q q') ≫
        (B.totalRowXIso p q' n' h').inv :=
  B.totalRowXIso_inv_comp_d p q q' n n' h h'

example (q q' : ℕ) :
    (B.totalRowXIso 0 q q (Nat.zero_add q)).inv ≫
        (B.totalRow 0).d q q' =
      (B.X 0).d q q' ≫
        (B.totalRowXIso 0 q' q' (Nat.zero_add q')).inv := by
  simpa only [ComplexShape.ε_zero, one_smul] using
    B.totalRowXIso_inv_comp_d 0 q q' q q'
      (Nat.zero_add q) (Nat.zero_add q')

example (φ : B ⟶ B') (p : ℕ) :
    B.totalRow p ⟶ B'.totalRow p :=
  totalRowMap φ p

example (φ : B ⟶ B') (p q n : ℕ) (h : p + q = n) :
    (totalRowMap φ p).f n =
      (B.totalRowXIso p q n h).hom ≫ (φ.f p).f q ≫
        (B'.totalRowXIso p q n h).inv :=
  totalRowMap_f φ p q n h

example (p : ℕ) : totalRowMap (𝟙 B) p = 𝟙 _ :=
  totalRowMap_id B p

example (φ : B ⟶ B') (ψ : B' ⟶ B'') (p : ℕ) :
    totalRowMap (φ ≫ ψ) p = totalRowMap φ p ≫ totalRowMap ψ p :=
  totalRowMap_comp φ ψ p

end HomologicalComplex₂

end
