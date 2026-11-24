/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Subfunctor.TransfiniteCardinality

/-!
# Tests for strict-prefix cardinality bounds
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u

open Cardinal CategoryTheory

namespace CategoryTheory.Subfunctor.TransfiniteCardinalityTest

variable {C : Type} [SmallCategory C] {F : Cᵒᵖ ⥤ Type u}

/-- The client retains the initial bound, every earlier seed bound, and the
literal strict-prefix conclusion. -/
example {J : Type u} [LinearOrder J]
    (A : Subfunctor F) (B : J → Subfunctor F) (j : J)
    (γ : Cardinal.{u}) (hγ : ℵ₀ ≤ γ)
    (hA : Cardinal.mk A.toFunctor.Elements ≤ γ)
    (hindex : Cardinal.mk (Set.Iio j) ≤ γ)
    (hB : ∀ k : Set.Iio j,
      Cardinal.mk (B k.1).toFunctor.Elements ≤ γ) :
    Cardinal.mk (Subfunctor.strictPrefixUnion A B j).toFunctor.Elements ≤ γ :=
  Subfunctor.mk_elements_strictPrefixUnion_le A B j hγ hA hindex hB

/-- Both the previous prefix and the new seed occur at the next stage. -/
example {J : Type u} [LinearOrder J] [SuccOrder J]
    (A : Subfunctor F) (B : J → Subfunctor F) (j : J)
    (hj : ¬ IsMax j) :
    Subfunctor.strictPrefixUnion A B j ≤
        Subfunctor.strictPrefixUnion A B (Order.succ j) ∧
      B j ≤ Subfunctor.strictPrefixUnion A B (Order.succ j) :=
  ⟨Subfunctor.strictPrefixUnion_le_succ A B j,
    Subfunctor.seed_le_strictPrefixUnion_succ A B j hj⟩

end CategoryTheory.Subfunctor.TransfiniteCardinalityTest
