/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Limits.Shapes.FiniteProducts

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace FiniteProductsTests

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]

-- All original projections are retained, with independent object and Hom universes.
example (n : ℕ) (X : Fin (n + 1) → C) (i : Fin n) :
    (Pi.finSuccProductIso n X).hom ≫ prod.fst = Pi.π X 0 ∧
      (Pi.finSuccProductIso n X).hom ≫ prod.snd ≫ Pi.π _ i = Pi.π X i.succ ∧
      (Pi.finSuccProductIso n X).inv ≫ Pi.π X 0 = prod.fst ∧
      (Pi.finSuccProductIso n X).inv ≫ Pi.π X i.succ = prod.snd ≫ Pi.π _ i :=
  ⟨(Pi.finSuccProductIso_legs n X).1, (Pi.finSuccProductIso_legs n X).2.1 i,
    (Pi.finSuccProductIso_legs n X).2.2.1, (Pi.finSuccProductIso_legs n X).2.2.2 i⟩

-- The whole arrow comparison retains the literal source and target projections.
-- Factor maps are arbitrary; they need no invertibility or model-category predicates.
example (n : ℕ) {X Y : Fin (n + 1) → C} (f : ∀ i, X i ⟶ Y i) (i : Fin n) :
    (Pi.finSuccProductArrowIso n f).hom.left ≫ prod.snd ≫ Pi.π _ i = Pi.π X i.succ ∧
      (Pi.finSuccProductArrowIso n f).hom.right ≫ prod.snd ≫ Pi.π _ i = Pi.π Y i.succ ∧
      (Pi.finSuccProductArrowIso n f).inv.left ≫ Pi.π X 0 = prod.fst ∧
      (Pi.finSuccProductArrowIso n f).inv.right ≫ Pi.π Y 0 = prod.fst :=
  ⟨(Pi.finSuccProductIso_legs n X).2.1 i, (Pi.finSuccProductIso_legs n Y).2.1 i,
    (Pi.finSuccProductIso_legs n X).2.2.1, (Pi.finSuccProductIso_legs n Y).2.2.1⟩

-- The inverse comparison satisfies the original square as well.
example (n : ℕ) {X Y : Fin (n + 1) → C} (f : ∀ i, X i ⟶ Y i) :
    (Pi.finSuccProductIso n X).inv ≫ CategoryTheory.Limits.Pi.map f =
      prod.map (f 0) (CategoryTheory.Limits.Pi.map (fun i : Fin n => f i.succ)) ≫
        (Pi.finSuccProductIso n Y).inv :=
  (Pi.finSuccProductArrowIso n f).inv.w

-- The zero-length tail uses the same chosen product and its head projection.
example (X : Fin 1 → C) :
    (Pi.finSuccProductIso 0 X).hom ≫ prod.fst = Pi.π X 0 :=
  (Pi.finSuccProductIso_legs 0 X).1

end FiniteProductsTests
