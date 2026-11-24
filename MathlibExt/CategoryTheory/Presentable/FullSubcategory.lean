/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Presentable.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Presentability in accessibly embedded full subcategories

The original full inclusion reflects compactness when it preserves the
relevant filtered colimits. Its Hom equivalence retains the original arrows.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w u v

open CategoryTheory Limits Opposite

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C]

/-- Ambient compactness transfers to the original full object at the same regular rank. -/
theorem isCardinalPresentable_of_ι (P : ObjectProperty C) (κ : Cardinal.{w})
    [Fact κ.IsRegular] [P.ι.IsCardinalAccessible κ]
    (A : P.FullSubcategory) [IsCardinalPresentable A.obj κ] :
    IsCardinalPresentable A κ := by
  let e : coyoneda.obj (op A) ≅ P.ι ⋙ coyoneda.obj (op A.obj) :=
    NatIso.ofComponents (fun B => P.fullyFaithfulι.homEquiv.toIso)
      (by intro B D f; ext g; rfl)
  constructor
  intro J _ _
  have := P.ι.preservesColimitsOfShape_of_isCardinalAccessible κ J
  have := preservesColimitsOfShape_of_isCardinalPresentable A.obj κ J
  have : PreservesColimitsOfShape J (P.ι ⋙ coyoneda.obj (op A.obj)) := inferInstance
  exact preservesColimitsOfShape_of_natIso e.symm

end CategoryTheory.ObjectProperty
