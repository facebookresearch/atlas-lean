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

import MathlibExt.CategoryTheory.MorphismProperty.Prod

/-!
# Generic product closure consumer tests

Focused consumer checks for `MorphismProperty.prod`: the product is
multiplicative when both components are, and respects isomorphisms when both
components do. Membership unfolds to the ordered component conjunction.

This file provides no stage, nerve, realization, or K-theory claim.
-/

namespace CategoryTheory.MorphismProperty.ProdTest

open CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C₁ : Type u₁} [Category.{v₁} C₁]
variable {C₂ : Type u₂} [Category.{v₂} C₂]
variable (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)

-- Product inherits multiplicativity; catches a missing `Prod.isMultiplicative`.
example [W₁.IsMultiplicative] [W₂.IsMultiplicative] :
    (W₁.prod W₂).IsMultiplicative :=
  inferInstance

-- Product inherits iso-respect; catches a missing `Prod.respectsIso`.
example [W₁.RespectsIso] [W₂.RespectsIso] :
    (W₁.prod W₂).RespectsIso :=
  inferInstance

-- Membership is the ordered conjunction; catches component-order swaps.
example {X Y : C₁ × C₂} {f : X ⟶ Y} :
    (W₁.prod W₂) f ↔ W₁ f.1 ∧ W₂ f.2 :=
  Iff.rfl

end CategoryTheory.MorphismProperty.ProdTest
