/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHHornIntervalComparison

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace MathlibExtTest.CGWHHornIntervalComparison

#check @CGWH.homotopyIntervalIsoInterval
#check @CGWH.homotopyIntervalIsoInterval.{0, 0}
#check @CGWH.homotopyIntervalIsoInterval.{0, 1}
#check @CGWH.homotopyIntervalIsoInterval.{1, 0}
#check @CGWH.homotopyIntervalIsoInterval.{1, 1}

example : CGWH.homotopyIntervalIsoInterval.{u, v} =
    CGWH.fullyFaithfulCgwhToTop.{u, v}.preimageIso
      (X := CGWH.homotopyInterval.{u, v}) (Y := CGWH.interval.{u, v})
      ((SSet.realizationToTopIso.{u, v}.app (Δ[1] : SSet.{v})) ≪≫
        SSet.stdSimplex.toTopObjIsoI.{v}).symm := rfl

example : CGWH.homotopyIntervalIsoInterval.{u, v}.hom ≫
    CGWH.homotopyIntervalIsoInterval.{u, v}.inv =
      𝟙 CGWH.homotopyInterval.{u, v} :=
  CGWH.homotopyIntervalIsoInterval.hom_inv_id

example : CGWH.homotopyIntervalIsoInterval.{u, v}.inv ≫
    CGWH.homotopyIntervalIsoInterval.{u, v}.hom =
      𝟙 CGWH.interval.{u, v} :=
  CGWH.homotopyIntervalIsoInterval.inv_hom_id

example : CGWH.cgwhToTop.map CGWH.homotopyIntervalIsoInterval.{u, v}.hom =
    ((SSet.realizationToTopIso.{u, v}.app (Δ[1] : SSet.{v})) ≪≫
      SSet.stdSimplex.toTopObjIsoI.{v}).inv :=
  CGWH.cgwhToTop_map_homotopyIntervalIsoInterval_hom

example : CGWH.cgwhToTop.map CGWH.homotopyIntervalIsoInterval.{u, v}.inv =
    ((SSet.realizationToTopIso.{u, v}.app (Δ[1] : SSet.{v})) ≪≫
      SSet.stdSimplex.toTopObjIsoI.{v}).hom :=
  CGWH.cgwhToTop_map_homotopyIntervalIsoInterval_inv

example : CGWH.homotopyIntervalEndpoint.{u, v} 0 ≫
    CGWH.homotopyIntervalIsoInterval.{u, v}.hom =
      CGWH.point_isTerminal.from (𝟙_ CGWH.{u, v}) ≫ CGWH.intervalZero.{u, v} :=
  CGWH.homotopyIntervalIsoInterval_zero

example : CGWH.homotopyIntervalEndpoint.{u, v} 1 ≫
    CGWH.homotopyIntervalIsoInterval.{u, v}.hom =
      CGWH.point_isTerminal.from (𝟙_ CGWH.{u, v}) ≫ CGWH.intervalOne.{u, v} :=
  CGWH.homotopyIntervalIsoInterval_one

example : (CGWH.point_isTerminal.from (𝟙_ CGWH.{u, v}) ≫
    CGWH.intervalZero.{u, v}) ≫ CGWH.homotopyIntervalIsoInterval.{u, v}.inv =
      CGWH.homotopyIntervalEndpoint.{u, v} 0 := by
  rw [← CGWH.homotopyIntervalIsoInterval_zero, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

example : (CGWH.point_isTerminal.from (𝟙_ CGWH.{u, v}) ≫
    CGWH.intervalOne.{u, v}) ≫ CGWH.homotopyIntervalIsoInterval.{u, v}.inv =
      CGWH.homotopyIntervalEndpoint.{u, v} 1 := by
  rw [← CGWH.homotopyIntervalIsoInterval_one, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

#print axioms CGWH.homotopyIntervalIsoInterval
#print axioms CGWH.homotopyIntervalIsoInterval_zero
#print axioms CGWH.homotopyIntervalIsoInterval_one

end MathlibExtTest.CGWHHornIntervalComparison
