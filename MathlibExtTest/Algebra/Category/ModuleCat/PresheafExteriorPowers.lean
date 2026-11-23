/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Algebra.Category.ModuleCat.PresheafExteriorPowers

/-! # Tests for presheaves of sectionwise exterior powers

The sections are the exterior powers of the sections, restriction of a wedge is the wedge of the
restrictions, restriction is functorial, and it is semilinear along the restriction maps of the
ring presheaf (which are not the identity in general).
-/

open CategoryTheory

namespace MathlibExtTest.Algebra.Category.ModuleCat.PresheafExteriorPowers

universe v u w a

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}

local instance (X : Cᵒᵖ) : CommRing ((O ⋙ forget₂ CommRingCat RingCat).obj X) :=
  inferInstanceAs (CommRing (O.obj X))

variable (n : ℕ) (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat))

example (X : Cᵒᵖ) (x : (PresheafOfModules.extPow n F).obj X) :
    PresheafOfModules.extPowSections n F X x = x := rfl

/-- Restricting a wedge gives the wedge of the restrictions. -/
example {X Y : Cᵒᵖ} (f : X ⟶ Y) (v : Fin n → F.obj X) :
    (PresheafOfModules.extPow n F).map f (exteriorPower.ιMulti _ n v) =
      exteriorPower.ιMulti _ n fun i => F.map f (v i) :=
  PresheafOfModules.extPow_map_ιMulti n F f v

example (X : Cᵒᵖ) (x : (PresheafOfModules.extPow n F).obj X) :
    (PresheafOfModules.extPow n F).map (𝟙 X) x = x := by
  rw [PresheafOfModules.map_id]
  rfl

example {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (x : (PresheafOfModules.extPow n F).obj X) :
    (PresheafOfModules.extPow n F).map (f ≫ g) x =
      (PresheafOfModules.extPow n F).map g ((PresheafOfModules.extPow n F).map f x) :=
  PresheafOfModules.map_comp_apply _ f g x

/-- Restriction is semilinear along the restriction map `O(X) → O(Y)` of the ring presheaf. -/
example {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : O.obj X) (x : (PresheafOfModules.extPow n F).obj X) :
    (PresheafOfModules.extPow n F).map f (r • x) =
      O.map f r • (PresheafOfModules.extPow n F).map f x :=
  (PresheafOfModules.extPow n F).map_smul f r x

end MathlibExtTest.Algebra.Category.ModuleCat.PresheafExteriorPowers
