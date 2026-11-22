/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Actual original root-enlargement and one-cell pushout comparisons

Both new root and new cell pushout universal properties are constructed
from the original selected pushouts. The whole pasted square retains
the actual original root and attaching-cell comparison functions.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe u v

namespace CategoryTheory.SmallObject.RootedCellPushoutComparison

open Limits

variable {C : Type u} [Category.{v} C] [HasPushouts C] {D D' X Y : C}
  (u : D ⟶ X) (f : D ⟶ Y) (rootMap : D ⟶ D') (toOriginal : D' ⟶ X)
  (hRoot : rootMap ≫ toOriginal = u)

/-- The actual root-stage comparison uses the original selected pushout descender. -/
def rootComparison : pushout rootMap f ⟶ pushout u f :=
  pushout.desc (toOriginal ≫ pushout.inl u f) (pushout.inr u f) (by
    rw [← Category.assoc, hRoot]
    exact pushout.condition)

/-- The new original root inclusion retains the exact original root-stage function. -/
theorem rootComparison_root :
    pushout.inl rootMap f ≫ rootComparison u f rootMap toOriginal hRoot =
      toOriginal ≫ pushout.inl u f :=
  pushout.inl_desc _ _ _

/-- The new original cell-side inclusion retains the same original old-stage function. -/
theorem rootComparison_local :
    pushout.inr rootMap f ≫ rootComparison u f rootMap toOriginal hRoot = pushout.inr u f :=
  pushout.inr_desc _ _ _

/-- The actual original small-root pushout and old whole pushout construct the new root UP. -/
theorem rootIsPushout :
    IsPushout toOriginal (pushout.inl rootMap f) (pushout.inl u f)
      (rootComparison u f rootMap toOriginal hRoot) := by
  have outer : IsPushout (rootMap ≫ toOriginal) f (pushout.inl u f)
      (pushout.inr rootMap f ≫ rootComparison u f rootMap toOriginal hRoot) := by
    rw [hRoot, rootComparison_local]
    exact IsPushout.of_hasPushout u f
  exact outer.of_left (rootComparison_root u f rootMap toOriginal hRoot).symm
    (IsPushout.of_hasPushout rootMap f)

variable {A B : C} (a : A ⟶ pushout u f) (j : A ⟶ B)
  (a' : A ⟶ pushout rootMap f)
  (hAttaching : a' ≫ rootComparison u f rootMap toOriginal hRoot = a)

/-- The actual new cell comparison uses precisely the original attaching-map equation. -/
def cellComparison : pushout a' j ⟶ pushout a j :=
  pushout.desc (rootComparison u f rootMap toOriginal hRoot ≫ pushout.inl a j)
    (pushout.inr a j) (by
      rw [← Category.assoc, hAttaching]
      exact pushout.condition)

/-- The actual new-cell old-stage map retains the original root-stage comparison. -/
theorem cellComparison_old :
    pushout.inl a' j ≫ cellComparison u f rootMap toOriginal hRoot a j a' hAttaching =
      rootComparison u f rootMap toOriginal hRoot ≫ pushout.inl a j :=
  pushout.inl_desc _ _ _

/-- The actual newly attached generator keeps its same original cell-side inclusion. -/
theorem cellComparison_new :
    pushout.inr a' j ≫ cellComparison u f rootMap toOriginal hRoot a j a' hAttaching =
      pushout.inr a j :=
  pushout.inr_desc _ _ _

/-- Both original cell pushouts and the actual attaching equation construct the new cell UP. -/
theorem cellIsPushout :
    IsPushout (rootComparison u f rootMap toOriginal hRoot) (pushout.inl a' j)
      (pushout.inl a j) (cellComparison u f rootMap toOriginal hRoot a j a' hAttaching) := by
  have outer : IsPushout (a' ≫ rootComparison u f rootMap toOriginal hRoot) j
      (pushout.inl a j)
      (pushout.inr a' j ≫ cellComparison u f rootMap toOriginal hRoot a j a' hAttaching) := by
    rw [hAttaching, cellComparison_new]
    exact IsPushout.of_hasPushout a j
  exact outer.of_left
    (cellComparison_old u f rootMap toOriginal hRoot a j a' hAttaching).symm
    (IsPushout.of_hasPushout a' j)

/-- The actual pasted whole root/one-cell square has its constructed original pushout UP. -/
theorem wholeIsPushout :
    IsPushout toOriginal (pushout.inl rootMap f ≫ pushout.inl a' j)
      (pushout.inl u f ≫ pushout.inl a j)
      (cellComparison u f rootMap toOriginal hRoot a j a' hAttaching) :=
  (rootIsPushout u f rootMap toOriginal hRoot).paste_vert
    (cellIsPushout u f rootMap toOriginal hRoot a j a' hAttaching)

end CategoryTheory.SmallObject.RootedCellPushoutComparison
