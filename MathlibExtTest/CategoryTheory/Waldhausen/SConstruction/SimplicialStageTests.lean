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

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.SimplicialStage

/-!
# Simplicial-stage object consumer tests

Focused public-API checks for the `simplicialStage`: degree-0/1/2
objects, a concrete face map, a concrete degeneracy map, and explicit
opposite-order composition. No weak-equivalence nerve, realization, G-theory,
or Q/S comparison.
-/

open CategoryTheory Simplicial
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.SimplicialStageTests

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Degree-0/1/2 objects are the bundled `Stage` categories. -/
example :
    (simplicialStage C).obj (Opposite.op ⦋0⦌) = Cat.of (Stage C 0) ∧
      (simplicialStage C).obj (Opposite.op ⦋1⦌) = Cat.of (Stage C 1) ∧
      (simplicialStage C).obj (Opposite.op ⦋2⦌) = Cat.of (Stage C 2) :=
  ⟨simplicialStage_obj C _, simplicialStage_obj C _, simplicialStage_obj C _⟩

/-- Concrete face map acts by reindexing along `δ`. -/
example :
    (simplicialStage C).map (SimplexCategory.δ (0 : Fin 2)).op =
      (reindexStage (SimplexCategory.δ (0 : Fin 2))).toCatHom :=
  simplicialStage_map C _

/-- Concrete degeneracy map acts by reindexing along `σ`. -/
example :
    (simplicialStage C).map (SimplexCategory.σ (0 : Fin 1)).op =
      (reindexStage (SimplexCategory.σ (0 : Fin 1))).toCatHom :=
  simplicialStage_map C _

/-- Composition unfolds to opposite-order `reindexStage` composition. -/
example (a b c : SimplexCategoryᵒᵖ) (f : a ⟶ b) (g : b ⟶ c) :
    (simplicialStage C).map (f ≫ g) =
      (reindexStage f.unop ⋙ reindexStage g.unop).toCatHom := by
  rw [simplicialStage_map, unop_comp, reindexStage_comp]

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.SimplicialStageTests
