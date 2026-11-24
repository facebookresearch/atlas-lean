/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Whiskering

/-!
# The native adjunction mate of a pullback square

This fixes the base-change map from the actual pullback comparison,
unit and counit. Its isomorphism property is a separate theorem; an
independent purported canonical base-change map is not an input.
-/

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.CanonicalAdjunctionBaseChange

open _root_.CategoryTheory
open _root_.CategoryTheory.Functor

universe uA vA uB vB uC vC uD vD

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {FU : B ⥤ A} {GU : A ⥤ B} {FV : D ⥤ C} {GV : C ⥤ D}
  (U : FU ⊣ GU) (V : FV ⊣ GV) (BP : B ⥤ D) (RP : A ⥤ C)
  (square : FU ⋙ RP ≅ BP ⋙ FV)

/-- The source base-change operator is the actual adjunction mate. -/
def map : GU ⋙ BP ⟶ RP ⋙ GV :=
  whiskerLeft (GU ⋙ BP) V.unit ≫
    whiskerRight (whiskerLeft GU square.inv) GV ≫
      whiskerRight (whiskerRight U.counit RP) GV

/-- It is Mathlib's adjunction mate `mateEquiv` of the inverse square. -/
theorem map_eq_mateEquiv : map U V BP RP square = mateEquiv U V square.inv := by
  ext x
  simp [map]

theorem component (M : A) : (map U V BP RP square).app M =
    V.unit.app (BP.obj (GU.obj M)) ≫ GV.map (square.inv.app (GU.obj M)) ≫
      GV.map (RP.map (U.counit.app M)) := rfl

end MathlibExt.CategoryTheory.CanonicalAdjunctionBaseChange
