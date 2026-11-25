/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanPointFiberComparison

/-! # Tests for the Bousfield--Kan point-fiber comparison -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace SSet.BousfieldKanPointFiberComparisonTests

universe u

variable {J : Type u} [Category.{0} J]
  (E : J ⥤ SSet.{u}) (j : J)

#check bkPointWeightedIndex
#check bkPointOuterDataMap
#check bkPointOuterMap
#check bkPointInclusion
#check bkDiagramToPoint
#check bkHocolimToNerve
#check bkPointInclusion_comp_bkHocolimToNerve
#check bkPointFiberComparison
#check bkPointFiberComparison_toTotal
#check bkPointFiberComparison_path

example :
    bkPointInclusion E j ≫ bkHocolimToNerve E =
      SSet.const (ComposableArrows.mk₀ j) :=
  bkPointInclusion_comp_bkHocolimToNerve E j

example :
    bkPointFiberComparison E j ≫
        TopCat.homotopyFiberToTotal
          (SSet.toTop.map (bkHocolimToNerve E))
          (bkPointRealizedVertex j) =
      SSet.toTop.map (bkPointInclusion E j) :=
  bkPointFiberComparison_toTotal E j

example :
    bkPointFiberComparison E j ≫
        TopCat.homotopyFiberPath
          (SSet.toTop.map (bkHocolimToNerve E))
          (bkPointRealizedVertex j) =
      bkPointConstantPath E j :=
  bkPointFiberComparison_path E j

#print axioms bkPointOuterDataMap
#print axioms bkPointInclusion
#print axioms bkPointInclusion_comp_bkHocolimToNerve
#print axioms bkPointFiberComparison
#print axioms bkPointFiberComparison_toTotal
#print axioms bkPointFiberComparison_path

end SSet.BousfieldKanPointFiberComparisonTests

end
