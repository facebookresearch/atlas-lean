/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.MapModuliCharts

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.MapModuliCharts
open MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies

/-- A represented varying chart evaluates the actual family over its base. -/
example {V S : Scheme} {q : V ⟶ S} {n g : ℕ}
    (M : VaryingModel q n g) (a : M.Chart) (i : Fin n) :
    a.evaluation i ≫ q = a.atlas.U.hom := evaluation_over a.family i

/-- Parameter reindexing commutes with actual evaluations, not a free operator. -/
example {V S : Scheme} {q : V ⟶ S} {n g : ℕ}
    (M : VaryingModel q n g) {T U : Over S} (f : T ⟶ U)
    (x : M.stack.Fibre U) (i : Fin n) :
    MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies.evaluation
        (M.toVaryingData.family T ((M.toVaryingData.pull f).obj x)) i =
      f.left ≫ MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies.evaluation
        (M.toVaryingData.family U x) i := by
  unfold MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies.evaluation
  rw [← M.targetMap f x, ← Category.assoc, M.markings f x i]
  exact Category.assoc _ _ _
