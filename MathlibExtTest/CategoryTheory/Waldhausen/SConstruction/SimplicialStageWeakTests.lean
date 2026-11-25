/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.SimplicialStageWeak

/-!
# Simplicial stage weak-equivalence consumer tests

Focused public-API checks for the `simplicialStageWeak`: degree-0/1/2
objects, a concrete face map, a concrete degeneracy map, and explicit
opposite-order composition. No nerve, realization, G-theory, or Q/S comparison.
-/

open CategoryTheory Simplicial
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.SimplicialStageWeakTests

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Degree-0/1/2 objects are the bundled `StageWeakCategory` categories. -/
example :
    (simplicialStageWeak C).obj (Opposite.op ⦋0⦌) = Cat.of (StageWeakCategory C 0) ∧
      (simplicialStageWeak C).obj (Opposite.op ⦋1⦌) = Cat.of (StageWeakCategory C 1) ∧
      (simplicialStageWeak C).obj (Opposite.op ⦋2⦌) = Cat.of (StageWeakCategory C 2) :=
  ⟨simplicialStageWeak_obj C _, simplicialStageWeak_obj C _, simplicialStageWeak_obj C _⟩

/-- Concrete face map acts by weak reindexing along `δ`. -/
example :
    (simplicialStageWeak C).map (SimplexCategory.δ (0 : Fin 2)).op =
      (reindexStageWeak C (SimplexCategory.δ (0 : Fin 2))).toCatHom :=
  simplicialStageWeak_map C _

/-- Concrete degeneracy map acts by weak reindexing along `σ`. -/
example :
    (simplicialStageWeak C).map (SimplexCategory.σ (0 : Fin 1)).op =
      (reindexStageWeak C (SimplexCategory.σ (0 : Fin 1))).toCatHom :=
  simplicialStageWeak_map C _

/-- Composition unfolds to opposite-order `reindexStageWeak` composition. -/
example (a b c : SimplexCategoryᵒᵖ) (f : a ⟶ b) (g : b ⟶ c) :
    (simplicialStageWeak C).map (f ≫ g) =
      (reindexStageWeak C f.unop ⋙ reindexStageWeak C g.unop).toCatHom := by
  rw [simplicialStageWeak_map, unop_comp, reindexStageWeak_comp]

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.SimplicialStageWeakTests
