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

import MathlibExt.CategoryTheory.Products.Additive

/-!
# Consumer checks for product additive instances

Componentwise addition/zero behavior, additive projections, zero-object
inference, and one biproduct projection computation for `C × D`.
-/

open CategoryTheory
open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace MathlibExtTest.CategoryTheory.Products.AdditiveTests

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C]
variable (D : Type u₂) [Category.{v₂} D] [Preadditive D]

/-- Addition in a product is componentwise. -/
example (X Y : C × D) (f g : X ⟶ Y) :
    (f + g).1 = f.1 + g.1 ∧ (f + g).2 = f.2 + g.2 :=
  ⟨rfl, rfl⟩

/-- Zero morphisms in a product are componentwise. -/
example (X Y : C × D) : (0 : X ⟶ Y).1 = 0 ∧ (0 : X ⟶ Y).2 = 0 :=
  ⟨rfl, rfl⟩

example : (CategoryTheory.Prod.fst C D).Additive := inferInstance

example : (CategoryTheory.Prod.snd C D).Additive := inferInstance

example [HasZeroObject C] [HasZeroObject D] : HasZeroObject (C × D) :=
  inferInstance

example [HasBinaryBiproducts C] [HasBinaryBiproducts D] :
    HasBinaryBiproducts (C × D) :=
  inferInstance

example [HasBinaryBiproducts C] [HasBinaryBiproducts D] (P Q : C × D) :
    (biprod.inl : P ⟶ P ⊞ Q) ≫ (biprod.fst : P ⊞ Q ⟶ P) = 𝟙 P :=
  biprod.inl_fst

end MathlibExtTest.CategoryTheory.Products.AdditiveTests
