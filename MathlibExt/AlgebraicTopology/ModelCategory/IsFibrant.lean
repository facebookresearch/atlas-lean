/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Avocado
-/

module

public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Fibrancy is invariant under isomorphisms

This file shows that in a category with fibrations whose fibrations respect
isomorphisms, the property `IsFibrant` is invariant under object isomorphisms.
The proof goes through the generic terminal-arrow and `MorphismProperty`/`Arrow`
iso APIs.
-/

@[expose] public section

namespace HomotopicalAlgebra

open CategoryTheory Limits

variable {C : Type*} [Category* C]

section

variable [CategoryWithFibrations C] [HasTerminal C]

/-- Fibrancy is invariant under an object isomorphism when fibrations respect
isomorphisms. -/
theorem isFibrant_iff_of_iso [(fibrations C).RespectsIso] {X Y : C}
    (e : X ≅ Y) : IsFibrant X ↔ IsFibrant Y := by
  simp only [fibration_iff]
  exact (fibrations C).arrow_mk_iso_iff
    (Arrow.isoMk' (terminal.from X) (terminal.from Y) e (Iso.refl _)
      (by simp [terminal.comp_from]))

/-- Transport fibrancy along an isomorphism. -/
theorem isFibrant_of_iso [(fibrations C).RespectsIso] {X Y : C}
    (e : X ≅ Y) (h : IsFibrant X) : IsFibrant Y :=
  (isFibrant_iff_of_iso e).mp h

end

end HomotopicalAlgebra
