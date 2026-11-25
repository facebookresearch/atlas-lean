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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageZeroObject

/-! # Tests for zero objects in finite Waldhausen stages -/

@[expose] public section

open CategoryTheory Limits ZeroObject

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageZeroObjectTests

open _root_.CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

/-- Every finite stage category has the canonical transferred zero object. -/
example (n : ℕ) : HasZeroObject (Stage C n) := inferInstance

/-- The selected object is actually zero. -/
example (n : ℕ) : IsZero (0 : Stage C n) := isZero_zero (Stage C n)

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageZeroObjectTests
