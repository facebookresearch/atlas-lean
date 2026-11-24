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

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakNerve

/-!
# Levelwise weak-stage nerve consumer tests

Focused public-API checks for the `stageWeakNerve`: outer degrees 0/1
are nerves of the stage weak-equivalence categories, one concrete nonidentity
face map acts by `nerveMap` of weak reindexing with opposite variance, and mapped
`mk₁` simplices land on the reindexed morphism. No diagonal, realization,
weak-equivalence, additivity, or Q/S comparison content.
-/

open CategoryTheory Simplicial
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageWeakNerveTests

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Outer degrees 0 and 1 are nerves of `StageWeakCategory C 0/1`.

Protects against wiring `stageWeakNerve` to the wrong stage degree or to the
plain `Stage` category instead of the weak-equivalence wide subcategory. -/
example :
    (stageWeakNerve C).obj (Opposite.op ⦋0⦌) =
        CategoryTheory.nerve (StageWeakCategory C 0) ∧
      (stageWeakNerve C).obj (Opposite.op ⦋1⦌) =
        CategoryTheory.nerve (StageWeakCategory C 1) :=
  ⟨stageWeakNerve_obj C _, stageWeakNerve_obj C _⟩

/-- A concrete nonidentity face map acts by `nerveMap` of weak reindexing.

Protects against dropping the `f.unop` opposite-variance flip or wiring the
simplicial map to a different reindexing functor. -/
example :
    (stageWeakNerve C).map (SimplexCategory.δ (0 : Fin 2)).op =
      CategoryTheory.nerveMap
        (reindexStageWeak C (SimplexCategory.δ (0 : Fin 2))) :=
  stageWeakNerve_map C _

/-- Mapped `mk₁` simplices land on the reindexed morphism.

Protects against a map/morphism mismatch where the simplicial action reindexes
morphisms differently from the stated `mk₁` computation law. -/
example (X Y : StageWeakCategory C 1) (φ : X ⟶ Y) :
    ((stageWeakNerve C).map (SimplexCategory.δ (0 : Fin 2)).op).app (Opposite.op ⦋1⦌)
        (ComposableArrows.mk₁ φ) =
      ComposableArrows.mk₁ ((reindexStageWeak C (SimplexCategory.δ (0 : Fin 2))).map φ) :=
  stageWeakNerve_map_app_mk₁ C ((SimplexCategory.δ (0 : Fin 2)).op) φ

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageWeakNerveTests
