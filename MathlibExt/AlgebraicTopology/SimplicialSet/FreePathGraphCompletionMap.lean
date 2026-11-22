/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreePathNerveGraphWeak
import MathlibExt.CategoryTheory.Groupoid.FreePathCompletion

/-!
# The SAME original graph and native completed word nerve map

The actual original full path evaluation in the native quiver free
groupoid restricts to the SAME original generating graph. The full
categorical completion unit and proved native completion coordinate
equivalence retain that same whole map. No graph-to-completion weak
outcome is assumed or concluded.
-/

noncomputable section
universe u v
open CategoryTheory Limits Opposite
open scoped Simplicial
namespace CategoryTheory.FreePathNerveCoordinates
variable (V : Type u) [Quiver.{v} V]

/-- The entire SAME original full path evaluation nerve map into its native quiver free groupoid. -/
def pathCompletionMap : nerve (Paths V) ⟶ nerve (Quiver.FreeGroupoid V) :=
  nerveMap (FreePathCompletion.pathToQuiverGroupoid V)

/-- The complete original generating graph maps by its SAME native original path evaluation. -/
def graphCompletionMap : (generatingGraph V : SSet.{max u v}) ⟶ nerve (Quiver.FreeGroupoid V) :=
  (generatingGraph V).ι ≫ pathCompletionMap V

/-- The original native categorical completion unit retains the SAME full quiver word map. -/
lemma nativeUnit_pathCompletionMap :
    nerveMap (FreeGroupoid.of (Paths V)) ≫ nerveMap (FreePathCompletion.toQuiverGroupoid V) =
      pathCompletionMap V := by
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro w
  exact (Functor.assoc w (FreeGroupoid.of (Paths V)) (FreePathCompletion.toQuiverGroupoid V)).trans
    (congrArg (fun F => w ⋙ F) (FreePathCompletion.unit_toQuiverGroupoid V))

/-- Every actual complete original path-word coefficient is evaluated by the SAME native path functor. -/
lemma pathCompletionMap_app (n : ℕ) (w : (nerve (Paths V)) _⦋n⦌) :
    (pathCompletionMap V).app (op ⦋n⦌) w = w ⋙ FreePathCompletion.pathToQuiverGroupoid V := rfl

/-- The original graph map retains every full native word and the SAME generator evaluation. -/
lemma graphCompletionMap_app (n : ℕ) (w : (generatingGraph V : SSet.{max u v}) _⦋n⦌) :
    (graphCompletionMap V).app (op ⦋n⦌) w = w.val ⋙ FreePathCompletion.pathToQuiverGroupoid V := rfl

/-- Every genuine original singleton generator edge retains its SAME full native free-groupoid generator. -/
lemma pathCompletionMap_generator {x y : V} (a : x ⟶ y) :
    (pathCompletionMap V).app (op ⦋1⦌)
      (ComposableArrows.mk₁ (C := Paths V) (X₀ := x) (X₁ := y) a.toPath) =
        ComposableArrows.mk₁ ((Quiver.FreeGroupoid.of V).map a) := by
  refine ComposableArrows.ext₁
    (F := (pathCompletionMap V).app (op ⦋1⦌)
      (ComposableArrows.mk₁ (C := Paths V) (X₀ := x) (X₁ := y) a.toPath))
    (G := ComposableArrows.mk₁ ((Quiver.FreeGroupoid.of V).map a)) rfl rfl ?_
  change (FreePathCompletion.pathToQuiverGroupoid V).map a.toPath =
    eqToHom rfl ≫ (Quiver.FreeGroupoid.of V).map a ≫ eqToHom rfl
  rw [eqToHom_refl, Category.id_comp]
  change (FreePathCompletion.pathToQuiverGroupoid V).map
      (X := (x : Paths V)) (Y := (y : Paths V)) a.toPath =
    (Quiver.FreeGroupoid.of V).map a ≫ 𝟙 ((Quiver.FreeGroupoid.of V).obj y)
  exact (Paths.lift_toPath (Quiver.FreeGroupoid.of V) a).trans (Category.comp_id _).symm

end CategoryTheory.FreePathNerveCoordinates
