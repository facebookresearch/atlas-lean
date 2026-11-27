/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

import MathlibExt.CategoryTheory.Products.Limits
import MathlibExt.CategoryTheory.Waldhausen.Basic
import MathlibExt.CategoryTheory.Waldhausen.Product

/-!
# Product Waldhausen consumer tests

Bounded generic checks for the product foundation: product zero object
inferred from the canonical lower product-zero instance with instance
inference check, componentwise cofibration/weak-equivalence behavior
through the deliberately non-instance `prodWaldhausen`, and the
two-direction cofiber-sequence correspondence
`isCofibrationSequence_prod_iff`. The product zero comes from
`MathlibExt.CategoryTheory.Products.Limits`; the Waldhausen structures
come from the source; no `WaldhausenCategoryWithoutGluing (C × D)` instance is assumed.
-/

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace MathlibExtTest.CategoryTheory.Waldhausen.ProductTests

variable (C : Type u₁) (D : Type u₂) [Category.{v₁} C] [Category.{v₂} D]
  [Limits.HasZeroObject C] [Limits.HasZeroObject D]
  [WaldhausenCategoryWithoutGluing C] [WaldhausenCategoryWithoutGluing D]

/-- Product zero object is inferred from the component zero objects. -/
example : Limits.HasZeroObject (C × D) := inferInstance

/-- Componentwise cofibration behavior through `prodWaldhausen`. -/
example (X Y : C × D) (f : X ⟶ Y) :
    @IsCofibration (C × D) _ _ prodWaldhausen X Y f ↔
      IsCofibration (C := C) f.1 ∧ IsCofibration (C := D) f.2 :=
  isCofibration_prod_iff f

/-- Componentwise weak-equivalence behavior through `prodWaldhausen`. -/
example (X Y : C × D) (f : X ⟶ Y) :
    @IsWeakEquivalence (C × D) _ _ prodWaldhausen X Y f ↔
      IsWeakEquivalence (C := C) f.1 ∧ IsWeakEquivalence (C := D) f.2 :=
  isWeakEquivalence_prod_iff f

/-- Two-direction cofiber-sequence correspondence for the product. -/
example (X Y Z : C × D) (f : X ⟶ Y) (g : Y ⟶ Z) :
    @IsCofibrationSequence (C × D) _ _ prodWaldhausen X Y Z f g ↔
      IsCofibrationSequence (C := C) f.1 g.1 ∧
        IsCofibrationSequence (C := D) f.2 g.2 :=
  isCofibrationSequence_prod_iff f g

end MathlibExtTest.CategoryTheory.Waldhausen.ProductTests
