/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalRealization

/-!
# Weak-diagonal realization consumer tests

Focused public-API checks for `stageWeakDiagonalReal`: unpointed realization,
realized basepoint, pointed bundle and its two projections.
No induced maps, identity/composition laws, paths, homotopies, connectedness,
additivity, π₀/K₀, G-theory, spectra, or Q/S comparison.
-/

open CategoryTheory Simplicial
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalRealizationTests

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategory C]

/-- Unpointed realization elaborates as a topological object. -/
noncomputable example : TopCat.{max u v} :=
  stageWeakDiagonalReal C

/-- Realized basepoint elaborates as a point of the realization. -/
noncomputable example : stageWeakDiagonalReal C :=
  stageWeakDiagonalReal.basepoint C

/-- Bundled pointed realization elaborates as a pointed space. -/
noncomputable example : PointedTopCat.{max u v} :=
  stageWeakDiagonalReal.toPointed C

/-- Pointed bundle projects to the unpointed realization. -/
example : (stageWeakDiagonalReal.toPointed C).right =
    stageWeakDiagonalReal C :=
  stageWeakDiagonalReal.toPointed_right C

/-- Pointed bundle is pointed at the realized basepoint. -/
example : (stageWeakDiagonalReal.toPointed C).hom PUnit.unit =
    stageWeakDiagonalReal.basepoint C :=
  stageWeakDiagonalReal.toPointed_hom_apply C

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalRealizationTests
