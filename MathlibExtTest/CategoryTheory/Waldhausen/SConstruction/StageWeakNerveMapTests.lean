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

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakNerveMap

/-!
# Stage weak-equivalence nerve-map consumer tests

Focused same-universe checks for the public `stageWeakNerveMap`: its outer
degree-2 component is `nerveFunctor.map` of `mapStageWeak 2`, its action
on a `mk₀` simplex is `mk₀` of the mapped weak-stage object, and its action
on a `mk₁` simplex is `mk₁` of the mapped weak-stage morphism. No
identity/composition restatements.

Nonclaims: no diagonal, realization, additivity, K/G-theory, or Q/S comparison.
-/

open CategoryTheory Limits Simplicial
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageWeakNerveMapTests

variable (C : Type u) [Category.{v} C] [Preadditive C] [Limits.HasZeroObject C]
  [HasBinaryBiproducts C] [ExactCategory C]
variable (D : Type u) [Category.{v} D] [Preadditive D] [Limits.HasZeroObject D]
  [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [Functor.IsExact F]

local instance : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
local instance : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D

/-- Outer degree-2 component is `nerveFunctor.map` of `mapStageWeak 2`. -/
example :
    (stageWeakNerveMap C D F).app (Opposite.op ⦋2⦌) =
      nerveFunctor.map (mapStageWeak C D F 2).toCatHom := rfl

/-- Action on a `mk₀` simplex is `mk₀` of the mapped weak-stage object. -/
example (X : StageWeakCategory C 2) :
    ((stageWeakNerveMap C D F).app (Opposite.op ⦋2⦌)).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ X) =
      ComposableArrows.mk₀ ((mapStageWeak C D F 2).obj X) :=
  stageWeakNerveMap_app_mk₀ C D F (Opposite.op ⦋2⦌) X

/-- Action on a `mk₁` simplex is `mk₁` of the mapped weak-stage morphism. -/
example {X Y : StageWeakCategory C 2} (φ : X ⟶ Y) :
    ((stageWeakNerveMap C D F).app (Opposite.op ⦋2⦌)).app (Opposite.op ⦋1⦌)
      (ComposableArrows.mk₁ φ) =
      ComposableArrows.mk₁ ((mapStageWeak C D F 2).map φ) :=
  stageWeakNerveMap_app_mk₁ C D F (Opposite.op ⦋2⦌) φ

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageWeakNerveMapTests
