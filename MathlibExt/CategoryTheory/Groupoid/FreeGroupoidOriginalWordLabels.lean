/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.CategoryTheory.Groupoid.FreeGroupoid
import Mathlib.CategoryTheory.SingleObj
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Full original quiver-groupoid words retain their labelled native generators

Each original arrow is labelled by its SAME individual source, target
and full arrow coefficient. The native free groupoid maps to the native
free group on these full original labels. Opposite multiplication
retains the SAME path concatenation order. No faithfulness, tree
contractibility or weak comparison is assumed or concluded here.
-/

noncomputable section
universe u v
open CategoryTheory
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V]

/-- All original generating arrows, retaining both individual original endpoints. -/
abbrev Labels := Σ x : V, Σ y : V, x ⟶ y

/-- The original full generator labels give an actual native quiver map to the free group. -/
def labelledQuiver : V ⥤q SingleObj (MulOpposite (FreeGroup (Labels V))) where
  obj _ := SingleObj.star _
  map {x y} a := MulOpposite.op (FreeGroup.of ⟨x, y, a⟩)

/-- The full original native quiver free groupoid retains the complete original generator labels. -/
def labelledFunctor : Quiver.FreeGroupoid V ⥤ SingleObj (MulOpposite (FreeGroup (Labels V))) :=
  Quiver.FreeGroupoid.lift (labelledQuiver V)

/-- Every SAME original full native generator maps to its exact source/target/arrow label. -/
lemma labelledFunctor_generator {x y : V} (a : x ⟶ y) :
    (labelledFunctor V).map ((Quiver.FreeGroupoid.of V).map a) =
      MulOpposite.op (FreeGroup.of ⟨x, y, a⟩) := by
  have h := Prefunctor.congr_hom (Quiver.FreeGroupoid.lift_spec (labelledQuiver V)) a
  exact eq_of_heq ((Quiver.homOfEq_heq _ _ _).symm.trans (heq_of_eq h))

/-- The SAME actual original inverse generator has precisely the inverse native free-group label. -/
lemma labelledFunctor_inverse_generator {x y : V} (a : x ⟶ y) :
    (labelledFunctor V).map (inv ((Quiver.FreeGroupoid.of V).map a)) =
      MulOpposite.op ((FreeGroup.of ⟨x, y, a⟩)⁻¹) := by
  have h := Functor.map_inv (labelledFunctor V) ((Quiver.FreeGroupoid.of V).map a)
  exact h.trans ((SingleObj.inv_as_inv (MulOpposite (FreeGroup (Labels V))) ((labelledFunctor V).map
    ((Quiver.FreeGroupoid.of V).map a))).trans
    (congrArg (fun f : MulOpposite (FreeGroup (Labels V)) => f⁻¹) (labelledFunctor_generator V a)))

/-- Every complete original completed word has its actual native reduced original-label word. -/
def normalWord {x y : Quiver.FreeGroupoid V} (a : x ⟶ y) : List (Labels V × Bool) :=
  @FreeGroup.toWord (Labels V) (Classical.decEq _) (MulOpposite.unop ((labelledFunctor V).map a))

/-- The actual complete original native generator has a one-letter reduced label word. -/
lemma normalWord_generator {x y : V} (a : x ⟶ y) :
    normalWord V ((Quiver.FreeGroupoid.of V).map a) = [(⟨x, y, a⟩, true)] := by
  classical
  let _ : DecidableEq (Labels V) := Classical.decEq _
  rw [normalWord, labelledFunctor_generator]
  exact FreeGroup.toWord_of _

end Quiver.FreeGroupoid.OriginalWords
