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

public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Fibrancy under object isomorphisms

Let C have a terminal object and a specified class of fibrations that respects isomorphisms.
An object X is fibrant when its map X → terminal C is a fibration.

An isomorphism X ≅ Y induces an isomorphism of their terminal arrows. Therefore X is fibrant
if and only if Y is fibrant, and fibrancy can be transported in either direction. Only the
category with fibrations and its terminal object are used.
-/

@[expose] public section

namespace HomotopicalAlgebra

open CategoryTheory Limits

variable {C : Type*} [Category* C]

section

variable [CategoryWithFibrations C] [HasTerminal C]

/-- Fibrancy equivalence along an object isomorphism.

In a category with terminal object and fibrations respecting isomorphisms, an isomorphism e :
X ≅ Y gives IsFibrant X ↔ IsFibrant Y. The terminal arrows are isomorphic as objects of the
arrow category. -/
theorem isFibrant_iff_of_iso [(fibrations C).RespectsIso] {X Y : C}
    (e : X ≅ Y) : IsFibrant X ↔ IsFibrant Y := by
  simp only [fibration_iff]
  exact (fibrations C).arrow_mk_iso_iff
    (Arrow.isoMk' (terminal.from X) (terminal.from Y) e (Iso.refl _)
      (by simp [terminal.comp_from]))

/-- Transport of fibrancy along an isomorphism.

If fibrations respect isomorphisms and C has a terminal object, an isomorphism X ≅ Y and
fibrancy of X imply fibrancy of Y. -/
theorem isFibrant_of_iso [(fibrations C).RespectsIso] {X Y : C}
    (e : X ≅ Y) (h : IsFibrant X) : IsFibrant Y :=
  (isFibrant_iff_of_iso e).mp h

end

end HomotopicalAlgebra
