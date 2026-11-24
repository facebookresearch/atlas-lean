/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# Edges in functorial strings of composable arrows

This file packages a fixed edge of a functorial string of composable arrows as
a natural transformation.  It is useful when a construction already produces
a functor into `ComposableArrows`, and individual arrows of that string are the
semantic maps exposed to clients.
-/

@[expose] public section

open CategoryTheory

universe vX uX vC uC

namespace CategoryTheory.ComposableArrows

variable {X : Type uX} [Category.{vX} X]
variable {C : Type uC} [Category.{vC} C]
variable {n : ℕ}

/-- A fixed edge in a functorial string of composable arrows, regarded as a
natural transformation between the corresponding evaluation functors. -/
def edgeNatTrans (F : X ⥤ ComposableArrows C n)
    (i j : ℕ) (hij : i ≤ j := by omega) (hj : j ≤ n := by omega) :
    F ⋙ (evaluation (Fin (n + 1)) C).obj ⟨i, by omega⟩ ⟶
      F ⋙ (evaluation (Fin (n + 1)) C).obj ⟨j, by omega⟩ where
  app x := (F.obj x).map' i j hij hj
  naturality _ _ f :=
    (ComposableArrows.naturality' (F.map f) i j hij hj).symm

@[simp]
lemma edgeNatTrans_app (F : X ⥤ ComposableArrows C n)
    (i j : ℕ) (hij : i ≤ j := by omega) (hj : j ≤ n := by omega)
    (x : X) :
    (edgeNatTrans F i j hij hj).app x = (F.obj x).map' i j hij hj :=
  rfl

end CategoryTheory.ComposableArrows
