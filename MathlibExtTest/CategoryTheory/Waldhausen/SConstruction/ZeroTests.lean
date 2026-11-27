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

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.Stage
import MathlibExt.CategoryTheory.Waldhausen.SConstruction.Zero

/-!
# Zero-stage consumer tests

Minimal coverage distinguishing the weak `zeroDiagram` constructor assumptions
(`Category` plus `HasZeroObject` only, per the accepted repair contract) from the
`WaldhausenCategoryWithoutGluing` stage proof: bundle the constant-zero stage and recover its
property. No simplicial object, nerve, realization, or K/G-theory content.
-/

open CategoryTheory
open CategoryTheory.Waldhausen.SConstruction

universe v u

noncomputable section

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.ZeroTests

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] (n : ℕ)

/-- `zeroDiagram` needs only `Category` plus `HasZeroObject`. -/
example : Ar n ⥤ C :=
  zeroDiagram C n

variable [WaldhausenCategoryWithoutGluing C]

/-- Bundle the constant-zero diagram as a `Stage`. -/
example : Stage C n :=
  ⟨zeroDiagram C n, isStage_zeroDiagram C n⟩

/-- Recover `IsStage` through the bundled zero stage's property. -/
example : IsStage n ((forget C n).obj ⟨zeroDiagram C n, isStage_zeroDiagram C n⟩) :=
  (⟨zeroDiagram C n, isStage_zeroDiagram C n⟩ : Stage C n).property

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.ZeroTests
