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

public import MathlibExt.CategoryTheory.Waldhausen.BinaryCoproductPushout
public import MathlibExt.CategoryTheory.Waldhausen.BinaryCoproductCobaseChange
public import MathlibExt.CategoryTheory.Waldhausen.BinaryCoproductWeakZero
public import MathlibExt.CategoryTheory.Waldhausen.Product
public import MathlibExt.CategoryTheory.Waldhausen.ExactFunctor

/-!
# Exactness of the genuine Waldhausen coproduct functor

The actual derived coproduct functor preserves zero objects,
cofibrations and product pushouts by their proved universal properties.
The genuine base gluing axiom supplies weak preservation. These four
derived fields give exactness for the same named product Waldhausen
value, installed only locally.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The actual coproduct functor is Waldhausen exact for the original
named product structure, under the genuine original gluing axiom. -/
theorem waldhausenCoproductFunctor_isWaldhausenExact
    (hG : WaldhausenGluingAxiom (C := C)) :
    letI : WaldhausenCategoryWithoutGluing (C × C) := prodWaldhausen (C := C) (D := C);
    (waldhausenCoproductFunctor C).IsWaldhausenExact := by
  let : WaldhausenCategoryWithoutGluing (C × C) := prodWaldhausen (C := C) (D := C)
  refine {
    map_isZero := ?_
    map_cofibration := ?_
    map_weakEquivalence := ?_
    map_pushout := ?_ }
  · intro X hX
    exact waldhausenCoproductFunctor_obj_isZero C X hX
  · intro X Y f hf
    have hparts := (isCofibration_prod_iff f).mp hf
    exact waldhausenCoproductFunctor_map_isCofibration C f hparts.1 hparts.2
  · intro X Y f hf
    have hparts := (isWeakEquivalence_prod_iff f).mp hf
    exact waldhausenCoproductFunctor_map_isWeakEquivalence C hG f hparts.1 hparts.2
  · intro X Y X' P i f inl inr _ hp
    exact waldhausenCoproductFunctor_map_isPushout C f i inl inr hp

end CategoryTheory.Waldhausen
