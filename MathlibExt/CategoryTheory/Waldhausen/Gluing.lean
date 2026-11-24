/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.Basic

/-!
# Waldhausen gluing axiom

This file records the gluing axiom for weak equivalences as an explicit
proposition.  A weak map of two spans whose distinguished left legs are
cofibrations induces a weak map between their pushout apices.

The carrier is deliberately not a typeclass.  It proves no inherited gluing
statement for arrow or cofibration-arrow categories and installs no global
instance.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

/-- Waldhausen's gluing axiom for weak equivalences across pushout squares
along cofibrations. -/
structure WaldhausenGluingAxiom : Prop where
  gluing :
    ∀ {X Y Z P X' Y' Z' P' : C}
      {i : X ⟶ Y} {f : X ⟶ Z} {inY : Y ⟶ P} {inZ : Z ⟶ P}
      {i' : X' ⟶ Y'} {f' : X' ⟶ Z'}
      {inY' : Y' ⟶ P'} {inZ' : Z' ⟶ P'}
      (_hP : IsPushout i f inY inZ)
      (_hP' : IsPushout i' f' inY' inZ')
      (x : X ⟶ X') (y : Y ⟶ Y') (z : Z ⟶ Z') (p : P ⟶ P'),
      IsCofibration i →
      IsCofibration i' →
      i ≫ y = x ≫ i' →
      f ≫ z = x ≫ f' →
      inY ≫ p = y ≫ inY' →
      inZ ≫ p = z ≫ inZ' →
      IsWeakEquivalence x →
      IsWeakEquivalence y →
      IsWeakEquivalence z →
      IsWeakEquivalence p

end CategoryTheory
