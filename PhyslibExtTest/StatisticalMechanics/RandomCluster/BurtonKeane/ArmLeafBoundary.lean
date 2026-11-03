/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmLeafBoundary

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmLeafBoundary`

* `bc102_bc64_disjointStar_degrees`: the star `bc64_starG` has a degree-3 centre and leaves;
* `bc102_BK_count_reduces_to_connectedForest` instantiated at the all-closed configuration.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmLeafBoundary

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls

-- The star has centre degree three.
example : bc64_starG.degree 0 = 3 := bc102_bc64_disjointStar_degrees.1

-- Every other vertex of the star is a leaf.
example : bc64_starG.degree 1 = 1 := bc102_bc64_disjointStar_degrees.2 1 (by decide)

-- The count reduction, instantiated at the all-closed configuration of `ℤ²`.
example := bc102_BK_count_reduces_to_connectedForest (d := 2) (fun _ => false) 3 2

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ArmLeafBoundary
