/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.PercolationApproximation

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.PercolationApproximation`

* the root of the hexagonal lattice lies in its orbit box of radius `0`;
* the square lattice has a percolation cylinder approximation at `q = 1`, and its root-to-boundary
  cylinders intersect to the percolation event;
* on the triangular lattice at `q = 2`, `θ(1/4) ≤ θ(1/2)` (unconditional monotonicity);
* `offCriticalSharpness` for the triangular lattice, given `pc ∈ (0, 1)`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.PercolationApproximation

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar Set

-- The root of the hexagonal lattice is in the radius-`0` orbit box.
example : hexagonal.root ∈ hexagonal.orbitBox 0 :=
  hexagonal.root_mem_orbitBox_zero

-- The square lattice has a cylinder approximation; the cylinders decrease to percolation.
example : square.HasPercolationCylinderApproximation 1 ∧
    (⋂ n : ℕ, square.bufferedCylinder n (square.bufferedRootBoundaryEvent n)) =
      square.percolationEvent :=
  ⟨square.hasPercolationCylinderApproximation le_rfl, square.iInter_bufferedRootBoundaryCylinder⟩

-- Unconditional monotonicity of `θ` on the triangular lattice at `q = 2`.
example : triangular.wiredPercolationProbability (1 / 4) 2 ≤
    triangular.wiredPercolationProbability (1 / 2) 2 :=
  triangular.wiredPercolationProbability_monotoneOn (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

-- Off-critical sharpness of the triangular lattice at `q = 2`, given `pc ∈ (0, 1)`.
example (hpc : triangular.criticalPoint 2 ∈ Ioo (0 : ℝ) 1) :
    OffCriticalSharpness (fun p => triangular.wiredPercolates p 2)
      (triangular.criticalPoint 2) :=
  triangular.offCriticalSharpness (by norm_num) hpc

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.PercolationApproximation
