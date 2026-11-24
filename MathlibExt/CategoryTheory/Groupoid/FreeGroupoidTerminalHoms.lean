/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.CategoryTheory.Groupoid.FreeGroupoidOfCategory
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# The full native groupoid completion of a category with a terminal object

Every completed original Hom is the terminal arrow of its source followed
by the inverse terminal arrow of its target. The formula is proved on
all native original arrows, inverses and compositions. Thus all actual
completed Homs are nonempty and subsingleton, retaining the full original
objects and maps at independent object and Hom universes.
-/

noncomputable section
universe u v
open CategoryTheory Limits

namespace CategoryTheory.FreeGroupoid
variable {C : Type u} [Category.{v} C] (t : C) (ht : IsTerminal t)

/-- The actual original arrow from a completed original object to the SAME terminal object. -/
def terminalArrow (x : FreeGroupoid C) : x ⟶ mk t :=
  (of C).map (ht.from x.as.as)

/-- Every complete original groupoid Hom retains the original terminal-cone naturality equation. -/
theorem terminal_hom_natural {x y : FreeGroupoid C} (f : x ⟶ y) :
    f ≫ terminalArrow t ht y = terminalArrow t ht x := by
  induction f using FreeGroupoid.hom_rec with
  | homMk f =>
      change (of C).map f ≫ (of C).map (ht.from _) = (of C).map (ht.from _)
      exact ((of C).map_comp _ _).symm.trans (congrArg (of C).map (ht.hom_ext _ _))
  | inv f ih =>
      apply (cancel_epi f).mp
      exact (IsIso.hom_inv_id_assoc f (terminalArrow t ht _)).trans ih.symm
  | comp f g ihf ihg =>
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun a => f ≫ a) ihg).trans ihf)

/-- Every complete original groupoid Hom is the SAME original terminal-cone formula. -/
theorem terminal_hom_formula {x y : FreeGroupoid C} (f : x ⟶ y) :
    f = terminalArrow t ht x ≫ inv (terminalArrow t ht y) := by
  have h := congrArg (fun a => a ≫ inv (terminalArrow t ht y)) (terminal_hom_natural t ht f)
  have he : (f ≫ terminalArrow t ht y) ≫ inv (terminalArrow t ht y) = f :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun a => f ≫ a) (IsIso.hom_inv_id (terminalArrow t ht y))).trans
        (Category.comp_id f))
  exact he.symm.trans h

include t ht in
/-- The actual full native completion Hom is subsingleton. -/
theorem homSubsingleton (x y : FreeGroupoid C) : Subsingleton (x ⟶ y) :=
  ⟨fun f g => (terminal_hom_formula t ht f).trans (terminal_hom_formula t ht g).symm⟩

include t ht in
/-- The actual full native completion Hom contains its original terminal-cone map. -/
theorem homNonempty (x y : FreeGroupoid C) : Nonempty (x ⟶ y) :=
  ⟨terminalArrow t ht x ≫ inv (terminalArrow t ht y)⟩

end CategoryTheory.FreeGroupoid
