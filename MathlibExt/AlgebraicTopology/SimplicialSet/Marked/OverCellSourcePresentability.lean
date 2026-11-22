/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CellSourcePresentability
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.SmallLimits
import MathlibExt.CategoryTheory.Presentable.OverSource
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverFibrationCells

/-!
# The original cell-source bound in every marked slice

Each actual target-to-base map indexes an original source in the marked
slice. Native source presentability transfers with its full base map,
without a presentability or cardinality bound on the base. Thus the same
original-universe rank controls all of the genuine slice cell sources.
-/

noncomputable section
universe u
open CategoryTheory

namespace SSet.Marked.CellSmallness

local instance overCellSourceRegularCardinal : Fact cardinal.{u}.IsRegular := cardinal_regular

/-- Every actual Cartesian slice cell source is presentable at the original common source rank. -/
theorem cartesian_over_source_presentable (B : SSet.{u})
    (s : MorphismProperty.OverCellIndex cartesianCell.{u} (max B)) :
    IsCardinalPresentable (Over.mk ((cartesianCell.{u} s.1).hom ≫ s.2)) cardinal.{u} := by
  let _ : IsCardinalPresentable (cartesianCell.{u} s.1).left cardinal.{u} :=
    cartesian_source_presentable s.1
  exact over_mk_isCardinalPresentable _ _

/-- The dual actual slice sources obey the same bound for every original base and mark set. -/
theorem cocartesian_over_source_presentable (B : SSet.{u})
    (s : MorphismProperty.OverCellIndex cocartesianCell.{u} (max B)) :
    IsCardinalPresentable (Over.mk ((cocartesianCell.{u} s.1).hom ≫ s.2)) cardinal.{u} := by
  let _ : IsCardinalPresentable (cocartesianCell.{u} s.1).left cardinal.{u} :=
    cocartesian_source_presentable s.1
  exact over_mk_isCardinalPresentable _ _

end SSet.Marked.CellSmallness
