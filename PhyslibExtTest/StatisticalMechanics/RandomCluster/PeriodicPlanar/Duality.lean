/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Duality

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Duality`

* at `q = 4`, `p = 1 / 2` the dual parameter is `4 / 5`, and `dualParam_involutive` returns
  `1 / 2` from it;
* `dual_parameter_boundary_involutive` at `p = 1 / 2`, `q = 4` and wired boundary;
* `finite_planar_free_dual_exchange` on an explicit one-vertex planar subgraph of `ℤ²` at
  `p = 1 / 2`, `q = 4` and the all-closed configuration.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Duality

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar _root_.StatMech.BeffaraDC
open _root_.StatMech.Lattice

/-- The dual parameter of `p = 1 / 2` at `q = 4` is `4 / 5`. -/
theorem dualParam_half_four : dualParam (1 / 2) 4 = 4 / 5 := by
  norm_num [dualParam]

-- The involution returns `1 / 2` from `4 / 5`.
example : dualParam (4 / 5) 4 = 1 / 2 := by
  rw [← dualParam_half_four]
  exact dualParam_involutive (by norm_num) (by norm_num) (by norm_num)

-- The boundary involution statement at a concrete parameter.
example : dualParam (1 / 2) 4 ∈ Set.Ioo (0 : ℝ) 1 ∧
    dualParam (dualParam (1 / 2) 4) 4 = 1 / 2 ∧
    RSW.dualBC (RSW.dualBC BoundaryCondition.wired) = BoundaryCondition.wired :=
  dual_parameter_boundary_involutive (by norm_num) (by norm_num) (by norm_num) _

/-- A one-vertex planar subgraph of `ℤ²` (no edges), at the origin. -/
def pointSubgraph : PlanarZ2Subgraph where
  V := Unit
  finV := inferInstance
  decV := inferInstance
  G := ⊥
  emb := ⟨fun _ => 0, fun _ _ _ => rfl⟩
  isSub := fun _ _ h => h.elim

-- Finite planar free/dual exchange on the one-vertex subgraph.
example : dualParam (1 / 2) 4 ∈ Set.Ioo (0 : ℝ) 1 ∧
    RSW.dualBC BoundaryCondition.free = BoundaryCondition.wired ∧
    FK.fkProb pointSubgraph.G (1 / 2) 4 (fun _ => false) =
      pfdDualProb pointSubgraph (dualParam (1 / 2) 4) 4 (fun _ => false) :=
  finite_planar_free_dual_exchange pointSubgraph _ (by norm_num) (by norm_num) (by norm_num)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Duality
