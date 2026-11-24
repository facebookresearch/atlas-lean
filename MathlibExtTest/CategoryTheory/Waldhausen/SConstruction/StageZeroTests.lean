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

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageZero

/-!
# Degree-zero stage terminal-object consumer tests

Downstream checks for `stageZero` and `stageZero_isTerminal`: the canonical
object is a `Stage C 0`, its `Limits.IsTerminal` witness is consumed, and the
unique morphism from a generic stage is exercised. Categorical terminality
only, not topological contractibility.
-/

open CategoryTheory CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageZeroTests

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Any two morphisms into the canonical zero stage agree. -/
example (A : Stage C 0) (f g : A ⟶ stageZero C) : f = g :=
  (stageZero_isTerminal C).hom_ext f g

/-- Consume the terminality witness for the canonical zero stage. -/
noncomputable example : Limits.IsTerminal (stageZero C) :=
  stageZero_isTerminal C

/-- Unique morphism from a generic degree-zero stage into the canonical one. -/
noncomputable example (A : Stage C 0) : A ⟶ stageZero C :=
  (stageZero_isTerminal C).from A

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageZeroTests
