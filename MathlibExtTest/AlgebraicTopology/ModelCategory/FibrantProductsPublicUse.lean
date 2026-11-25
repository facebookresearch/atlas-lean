/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/
module

public import MathlibExt.AlgebraicTopology.ModelCategory.FibrantProducts

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uC vC w
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace FibrantProductsNeutralPublicUse
variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {J : Type w} [HasProductsOfShape J C]
  {X Y : J → C} [∀ j, IsFibrant (X j)] [∀ j, IsFibrant (Y j)]
  (f : ∀ j, X j ⟶ Y j) (hf : ∀ j, WeakEquivalence (f j))

/-- The actual product map of an arbitrary fibrant family is weak. -/
example : WeakEquivalence (Limits.Pi.map f) :=
  originalPiMap_weakEquivalence_of_fibrant f hf

/-- A caller's two distinct limiting fans retain their actual comparison map. -/
example (c : Fan X) (hc : IsLimit c) (d : Fan Y) (hd : IsLimit d)
    (p : c.pt ⟶ d.pt) (hp : ∀ j, p ≫ d.proj j = c.proj j ≫ f j) :
    WeakEquivalence p := originalFanMap_weak_of_fibrant c hc d hd f p hp hf
end FibrantProductsNeutralPublicUse
