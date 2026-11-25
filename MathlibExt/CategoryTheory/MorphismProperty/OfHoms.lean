/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-! # Strict functorial images of generating families -/

@[expose] public section

set_option autoImplicit false

universe uC vC uD vD w

namespace CategoryTheory.MorphismProperty

variable {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D]

/-- Strictly mapping a generating family retains exactly its mapped arrows. -/
theorem strictMap_ofHoms {ι : Type w} {X Y : ι → C}
    (f : ∀ i, X i ⟶ Y i) (F : C ⥤ D) :
    (ofHoms f).strictMap F = ofHoms (fun i => F.map (f i)) := by
  ext A B g
  constructor
  · intro h
    cases h with
    | map h =>
      cases h with
      | mk i => exact .mk i
  · intro h
    cases h with
    | mk i => exact .map (.mk i)

end CategoryTheory.MorphismProperty
