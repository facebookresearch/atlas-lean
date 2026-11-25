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

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalConnected
import MathlibExt.AlgebraicTopology.SimplicialSet.PiZeroConnectedRealization

/-!
# StageWeak diagonal connected-realization consumer test

Focused downstream check for `stageWeakDiagonal_isConnected`: simplicial
connectedness of `stageWeakDiagonal C` supplies `PathConnectedSpace` for its
geometric realization via `SSet.pathConnectedSpace_realization_of_isConnected`.

Nonclaims: no contractibility, additivity, `π₀ = K₀`, equivalence, or strict
pointedness. No spectra or Q/S comparison.
-/

open CategoryTheory Simplicial
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalConnectedTests

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Realization of the simplicially connected weak diagonal is path-connected.
Catches signature drift in the connectedness theorem and its realization consumer. -/
example : PathConnectedSpace ↑(SSet.toTop.obj (stageWeakDiagonal C)) := by
  have := stageWeakDiagonal_isConnected C
  exact SSet.pathConnectedSpace_realization_of_isConnected (stageWeakDiagonal C)

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalConnectedTests
