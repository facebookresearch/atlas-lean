/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Whole original undercategory adjunction records

An original adjunction and its supplied point isomorphism determine the
unchanged undercategory adjunction. Complete forgetful functor records
are compared before reading its unit, counit, or either hom-equivalence
direction. All point maps and the supplied inverse remain original.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u₁ u₂ v₁ v₂

open CategoryTheory

namespace CategoryTheory.Adjunction.UnderPointRecords

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) {P : C} {Q : D} (e : F.obj P ≅ Q)

/-- The original postcomposition and the same selected point inverse give the complete left
functor. -/
abbrev left : Under P ⥤ Under Q := Under.post F ⋙ Under.map e.inv

/-- The original point map, right functor, and original point-unit give the complete right
functor. -/
abbrev right : Under Q ⥤ Under P :=
  Under.map e.hom ⋙ Under.post G ⋙ Under.map (a.unit.app P)

/-- The same selected whole point-isomorphism unit retains its original identity on
underlying objects. -/
theorem pointIso_unit_right (X : Under (F.obj P)) :
    ((Under.mapIso e.symm).unitIso.hom.app X).right = 𝟙 X.right := by
  simp [Under.mapIso, Comma.mapLeftIso]

/-- The same selected whole point-isomorphism counit retains its original identity on
underlying objects. -/
theorem pointIso_counit_right (Y : Under Q) :
    ((Under.mapIso e.symm).counitIso.hom.app Y).right = 𝟙 Y.right := by
  simp [Under.mapIso, Comma.mapLeftIso]

/-- The same entire original undercategory adjunction retains the original supplied point
isomorphism. -/
def adjunction : left e ⊣ right a e :=
  (Under.postAdjunctionLeft a).comp (Under.mapIso e.symm).toAdjunction

/-- The complete original left record retains the whole original underlying functor before
projection. -/
theorem left_forget : left e ⋙ Under.forget Q = Under.forget P ⋙ F :=
  Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

/-- The complete original right record retains the whole original underlying functor before
projection. -/
theorem right_forget : right a e ⋙ Under.forget P = Under.forget Q ⋙ G :=
  Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

/-- The actual original composite unit retains the same complete original unit map after
forgetting. -/
theorem unit_right (X : Under P) :
    ((adjunction a e).unit.app X).right = a.unit.app X.right := by
  rw [adjunction, Adjunction.comp_unit_app, Under.comp_right,
    Equivalence.toAdjunction_unit]
  change a.unit.app X.right ≫
      G.map ((Under.mapIso e.symm).unitIso.hom.app ((Under.post F).obj X)).right =
        a.unit.app X.right
  rw [pointIso_unit_right]
  change a.unit.app X.right ≫ G.map (𝟙 (F.obj X.right)) = a.unit.app X.right
  exact (congrArg (a.unit.app X.right ≫ ·) (G.map_id _)).trans (Category.comp_id _)

/-- The actual original composite counit retains the same whole original counit map after
forgetting. -/
theorem counit_right (Y : Under Q) :
    ((adjunction a e).counit.app Y).right = a.counit.app Y.right := by
  rw [adjunction, Adjunction.comp_counit_app, Under.comp_right,
    Equivalence.toAdjunction_counit]
  change a.counit.app Y.right ≫ ((Under.mapIso e.symm).counitIso.hom.app Y).right =
    a.counit.app Y.right
  rw [pointIso_counit_right]
  exact Category.comp_id _

/-- The same whole original adjunction mate retains the original underlying unit and map. -/
theorem homEquiv_right (X : Under P) (Y : Under Q) (p : (left e).obj X ⟶ Y) :
    ((adjunction a e).homEquiv X Y p).right = a.homEquiv X.right Y.right p.right := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change ((adjunction a e).unit.app X).right ≫ G.map p.right = a.unit.app X.right ≫ G.map p.right
  rw [unit_right]

/-- The same selected original inverse mate retains the original whole counit and map. -/
theorem homEquiv_symm_right (X : Under P) (Y : Under Q) (p : X ⟶ (right a e).obj Y) :
    (((adjunction a e).homEquiv X Y).symm p).right = (a.homEquiv X.right Y.right).symm p.right := by
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  change F.map p.right ≫ ((adjunction a e).counit.app Y).right = F.map p.right ≫
    a.counit.app Y.right
  rw [counit_right]

end CategoryTheory.Adjunction.UnderPointRecords
