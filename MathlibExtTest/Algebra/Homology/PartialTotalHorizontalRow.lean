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

public import MathlibExt.Algebra.Homology.PartialTotalHorizontalRow

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

example (m q : ℕ) :
    B.partialTotalHorizontalRowF m (m + q) =
      (B.totalRowXIso (m + 1) q (m + q + 1) (by omega)).hom ≫
        (B.d (m + 1) m).f q ≫
        (B.totalRowXIso m q (m + q) rfl).inv :=
  B.partialTotalHorizontalRowF_eq m q

example :
    B.partialTotalHorizontalRowF 0 0 =
      (B.totalRowXIso 1 0 1 rfl).hom ≫
        (B.d 1 0).f 0 ≫
        (B.totalRowXIso 0 0 0 rfl).inv := by
  simpa using B.partialTotalHorizontalRowF_eq 0 0

example : B.partialTotalHorizontalRowF 1 0 = 0 :=
  B.partialTotalHorizontalRowF_eq_zero_of_lt 1 0 (by omega)

example (m q n : ℕ) (h : m + q = n) :
    B.partialTotalHorizontalRowF m n =
      (B.totalRowXIso (m + 1) q (n + 1) (by omega)).hom ≫
        (B.d (m + 1) m).f q ≫
        (B.totalRowXIso m q n h).inv :=
  B.partialTotalHorizontalRowF_eqAt m q n h

example (m q : ℕ) :
    B.partialTotalHorizontalRowF m (m + q) =
      (B.totalRowXIso (m + 1) q (m + q + 1) (by omega)).hom ≫
        (B.d (m + 1) m).f q ≫
        (B.totalRowXIso m q (m + q) rfl).inv :=
  B.partialTotalHorizontalRowF_eqAt m q (m + q) rfl

example (m q : ℕ) :
    B.partialTotalHorizontalRowF m (q + m) =
      (B.totalRowXIso (m + 1) q (q + m + 1) (by omega)).hom ≫
        (B.d (m + 1) m).f q ≫
        (B.totalRowXIso m q (q + m) (Nat.add_comm m q)).inv :=
  B.partialTotalHorizontalRowF_eqAt m q (q + m) (Nat.add_comm m q)

example (q : ℕ) :
    (B.partialTotalHorizontalRowF 0 q :
      (B.totalRow 1).X (q + 1) ⟶ (B.totalRow 0).X q) =
      (B.totalRowXIso 1 q (q + 1) (by omega)).hom ≫
        (B.d 1 0).f q ≫
        (B.totalRowXIso 0 q q (Nat.zero_add q)).inv :=
  B.partialTotalHorizontalRowF_eqAt 0 q q (Nat.zero_add q)

example :
    B.partialTotalHorizontalRowF 0 0 =
      (B.totalRowXIso 1 0 1 rfl).hom ≫
        (B.d 1 0).f 0 ≫
        (B.totalRowXIso 0 0 0 rfl).inv :=
  B.partialTotalHorizontalRowF_eqAt 0 0 0 rfl

example :
    B.partialTotalHorizontalRowF 0 1 =
      (B.totalRowXIso 1 1 2 rfl).hom ≫
        (B.d 1 0).f 1 ≫
        (B.totalRowXIso 0 1 1 rfl).inv :=
  B.partialTotalHorizontalRowF_eqAt 0 1 1 rfl

example (m : ℕ) :
    B.partialTotalHorizontalRowF m m =
      (B.totalRowXIso (m + 1) 0 (m + 1) (by omega)).hom ≫
        (B.d (m + 1) m).f 0 ≫
        (B.totalRowXIso m 0 m (Nat.add_zero m)).inv :=
  B.partialTotalHorizontalRowF_eqAt m 0 m (Nat.add_zero m)

end HomologicalComplex₂

end
