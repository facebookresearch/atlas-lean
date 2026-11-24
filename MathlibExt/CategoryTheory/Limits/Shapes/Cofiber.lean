/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Ordinary categorical cofibers

For an arrow `X ⟶ Y`, its cofiber span is `Y ← X ⟶ *`. This neutral file
defines that span, its ordinary colimit, the two cocone legs and their pushout
and naturality laws without importing any model-category infrastructure.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

section

variable [HasTerminal C]

/-- The walking span `Y ← X ⟶ *` associated to an arrow `X ⟶ Y`. -/
noncomputable def cofiberSpan : Arrow C ⥤ (WalkingSpan ⥤ C) where
  obj f := span f.hom (terminal.from f.left)
  map {f g} sq := spanHomMk sq.left sq.right (𝟙 _)
    sq.w.symm (by simp)
  map_id f := by
    ext j
    rcases j with (_ | _ | _) <;> simp
  map_comp sq₁ sq₂ := by
    ext j
    rcases j with (_ | _ | _) <;> simp

variable [HasColimitsOfShape WalkingSpan C]

/-- The ordinary categorical cofiber, as the colimit of `Y ← X ⟶ *`. -/
noncomputable def ordinaryCofiber : Arrow C ⥤ C :=
  cofiberSpan (C := C) ⋙ colim

/-- The target-to-cofiber leg of the ordinary cofiber cocone. -/
def ordinaryCofiberTarget (f : Arrow C) : f.right ⟶ (ordinaryCofiber (C := C)).obj f :=
  colimit.ι ((cofiberSpan (C := C)).obj f) WalkingSpan.left

/-- The terminal-to-cofiber leg of the same ordinary cofiber cocone. -/
def ordinaryCofiberPoint (f : Arrow C) : (⊤_ C) ⟶ (ordinaryCofiber (C := C)).obj f :=
  colimit.ι ((cofiberSpan (C := C)).obj f) WalkingSpan.right

/-- The selected ordinary cofiber legs have the pushout universal property. -/
theorem ordinaryCofiberIsPushout (f : Arrow C) :
    IsPushout f.hom (terminal.from f.left) (ordinaryCofiberTarget f) (ordinaryCofiberPoint f) :=
  IsPushout.of_isColimit_cocone (colimit.isColimit ((cofiberSpan (C := C)).obj f))

/-- The target leg is natural in the entire arrow square. -/
@[reassoc]
theorem ordinaryCofiberTarget_naturality {f g : Arrow C} (sq : f ⟶ g) :
    ordinaryCofiberTarget f ≫ (ordinaryCofiber (C := C)).map sq =
      sq.right ≫ ordinaryCofiberTarget g :=
  ι_colimMap ((cofiberSpan (C := C)).map sq) WalkingSpan.left

/-- The terminal leg is natural in the same entire arrow square. -/
@[reassoc]
theorem ordinaryCofiberPoint_naturality {f g : Arrow C} (sq : f ⟶ g) :
    ordinaryCofiberPoint f ≫ (ordinaryCofiber (C := C)).map sq = ordinaryCofiberPoint g :=
  (ι_colimMap ((cofiberSpan (C := C)).map sq) WalkingSpan.right).trans (Category.id_comp _)

end

end HomotopicalAlgebra
