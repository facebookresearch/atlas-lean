/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.CategoryTheory.SmallObject.Construction
public import Mathlib.Basic.Countable.Basic

/-!
# Countability of the entire original small-object attachment squares

The actual index, top map and bottom map determine the entire native
commutative-square record. Its original equation is retained. Thus
countability of those three genuine inputs counts every actual square.
-/

@[expose] public section

universe u v w
open CategoryTheory

namespace CategoryTheory.SmallObject

variable {C : Type u} [Category.{v} C] {I : Type w} {A B : I → C}
  (f : ∀ i, A i ⟶ B i) {X S : C} (p : X ⟶ S)

/-- All actual attachment squares are countable when their full original indexing and both
whole-map sets are countable. -/
instance countable_functorObjIndex [Countable I]
    [∀ i, Countable (A i ⟶ X)] [∀ i, Countable (B i ⟶ S)] :
    Countable (FunctorObjIndex f p) := by
  let φ (x : FunctorObjIndex f p) : Σ i, (A i ⟶ X) × (B i ⟶ S) := ⟨x.i, x.t, x.b⟩
  have hφ : Function.Injective φ := by
    rintro ⟨i₁, t₁, b₁, _⟩ ⟨i₂, t₂, b₂, _⟩ h
    obtain rfl : i₁ = i₂ := by simpa [φ] using congr($(h).fst)
    simpa [φ] using h
  exact hφ.countable

end CategoryTheory.SmallObject
