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

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.SimplicialStageMap

/-!
# Simplicial stage-map consumer tests

Focused same-universe checks for `simplicialStageMap` and `simplicialStageMapWeak`: their
degree-one components observed through evaluation at the `(0, 1)` interval (weak case through
the stage inclusions),
and one concrete `δ` face-naturality orientation observed through the
forgetful functor. No identity/composition or reindex restatements.
-/

open CategoryTheory Limits Simplicial
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.SimplicialStageMapTests

variable (C : Type u) [Category.{v} C] [Preadditive C] [Limits.HasZeroObject C]
  [HasBinaryBiproducts C] [ExactCategory C]
variable (D : Type u) [Category.{v} D] [Preadditive D] [Limits.HasZeroObject D]
  [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [Functor.IsExact F]

local instance : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
local instance : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D

/-- Degree-one component through `(0, 1)` evaluation is `F` applied downstream. -/
example (X : Stage C 1) :
    (eval D 1 (interval (0 : Fin 2) 1 (by decide))).obj
      (((simplicialStageMap C D F).app (Opposite.op ⦋1⦌)).toFunctor.obj X) =
      F.obj ((eval C 1 (interval (0 : Fin 2) 1 (by decide))).obj X) := rfl

/-- Degree-one weak component through inclusion/evaluation is `F` applied downstream. -/
example (X : StageWeakCategory C 1) :
    (eval D 1 (interval (0 : Fin 2) 1 (by decide))).obj
      ((stageWeakInclusion D 1).obj
        (((simplicialStageMapWeak C D F).app (Opposite.op ⦋1⦌)).toFunctor.obj X)) =
      F.obj ((eval C 1 (interval (0 : Fin 2) 1 (by decide))).obj
        ((stageWeakInclusion C 1).obj X)) := rfl

/-- Concrete `δ 0` naturality orientation through the forgetful functor. -/
example (X : Stage C 2) :
    (forget D 1).obj
      (((simplicialStageMap C D F).app (Opposite.op ⦋1⦌)).toFunctor.obj
        (((simplicialStage C).map (SimplexCategory.δ (0 : Fin 3)).op).toFunctor.obj X)) =
    (forget D 1).obj
      (((simplicialStage D).map (SimplexCategory.δ (0 : Fin 3)).op).toFunctor.obj
        (((simplicialStageMap C D F).app (Opposite.op ⦋2⦌)).toFunctor.obj X)) := rfl

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.SimplicialStageMapTests
