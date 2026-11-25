/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# Entire native undercategory chains over a constant original base word

An actual native undercategory chain whose whole original forgetful
projection is a constant word is itself constant at its original first
arrow, transported only by the proved target equality. All original
objects, arrows, triangles and every chain arity are retained. This is
the exact strict Hom-fibre geometry of the native under-nerve projection.
-/

noncomputable section
universe u v
open CategoryTheory

namespace CategoryTheory.Under

variable {C : Type u} [Category.{v} C] {X Y : C} {n : ℕ}
  (F : Fin (n + 1) ⥤ Under X)
  (h : F ⋙ Under.forget X = (Functor.const (Fin (n + 1))).obj Y)

/-- The SAME original first arrow of an entire undercategory chain, with only its actual
base-target equality
transport. -/
def constantProjectionArrow : X ⟶ Y :=
  (F.obj 0).hom ≫ eqToHom (Functor.congr_obj h 0)

/-- Every SAME actual original undercategory object over the constant base word is its first
original arrow. -/
theorem constantProjection_obj (i : Fin (n + 1)) : F.obj i =
  Under.mk (constantProjectionArrow F h) := by
  let hi := Functor.congr_obj h i
  let h₀ := Functor.congr_obj h 0
  let k := F.map (homOfLE (Fin.zero_le i))
  have hk : k.right ≫ eqToHom hi = eqToHom h₀ := by
    have he := Functor.congr_hom h (homOfLE (Fin.zero_le i))
    change k.right = eqToHom h₀ ≫ 𝟙 Y ≫ eqToHom hi.symm at he
    exact (congrArg (fun m => m ≫ eqToHom hi) he).trans (by simp)
  apply StructuredArrow.obj_ext (F.obj i) (Under.mk (constantProjectionArrow F h)) hi
  change (F.obj i).hom ≫ eqToHom hi = constantProjectionArrow F h
  exact (congrArg (fun m => m ≫ eqToHom hi) (Under.w k)).symm.trans
    ((Category.assoc _ _ _).trans (congrArg (fun m => (F.obj 0).hom ≫ m) hk))

/-- The SAME entire native undercategory chain is exactly its constant first-arrow word
whenever its full original
base projection is constant. -/
theorem constantProjection_chain : F = (Functor.const (Fin (n + 1))).obj (Under.mk
  (constantProjectionArrow F h)) := by
  refine Functor.ext (F := F)
    (G := (Functor.const (Fin (n + 1))).obj (Under.mk (constantProjectionArrow F h)))
    (constantProjection_obj F h) ?_
  intro i j f
  apply Under.UnderMorphism.ext
  simpa only [Under.comp_right, Under.eqToHom_right, Under.id_right, Under.mk_right,
    Under.forget_obj, Under.forget_map,
    Functor.const_obj_map, Functor.const_obj_obj, Functor.comp_map, Functor.comp_obj]
    using Functor.congr_hom h f

end CategoryTheory.Under
