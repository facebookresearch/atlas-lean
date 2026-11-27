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

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageOneEquivalence

/-!
# Degree-one stage equivalence consumer tests

Focused downstream checks for the public `stageOneEquivalence` API: its
forward direction is `stageOne`, its inverse is interval evaluation, plus one
object and one morphism computation through the equivalence. No new API,
simplicial object, nerve, realization, weak equivalence, or K/G-theory
definition.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageOneEquivalenceTests

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Forward direction of the equivalence is `stageOne`. -/
example : (stageOneEquivalence C).functor = stageOne C :=
  stageOneEquivalence_functor C

/-- Inverse direction of the equivalence is interval evaluation. -/
example : (stageOneEquivalence C).inverse = stageOneEval C :=
  stageOneEquivalence_inverse C

/-- Object computation through the equivalence at the `(0, 1)` interval. -/
example (X : C) (h : (0 : Fin 2) ≤ 1) :
    ((stageOneEquivalence C).functor.obj X).obj.obj (interval 0 1 h) = X := by
  rw [stageOneEquivalence_functor]
  exact stageOne_obj_interval_zero_one C X h

/-- Morphism computation through the equivalence at the `(0, 1)` interval. -/
example {X Y : C} (f : X ⟶ Y) :
    ((stageOneEquivalence C).functor.map f).hom.app
      (interval (0 : Fin 2) 1 (by decide)) = f :=
  stageOne_map_interval_zero_one C f

/-- `stageOneEval.map f` is the component at the `(0, 1)` interval. -/
example {S T : Stage C 1} (f : S ⟶ T) :
    (stageOneEval C).map f = f.hom.app (interval (0 : Fin 2) 1 (by decide)) :=
  rfl

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageOneEquivalenceTests
