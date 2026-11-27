/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.FKFiniteWiredSweep

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.FKFiniteWiredSweep`

* the terminals of the cell at `0` are triangular neighbors (`triangularGraph_adj_…`) and
  hexagonal neighbors of the black center (`hexagonalGraph_adj_…`);
* `triHexFK_finiteWiredBoundaryReachRatio_eq` on one cell with terminals `Fin 3`, boundary `{0}`,
  root `2`, at `q = 4`, triangle odds `(1, 1, 1)`, star odds `(4, 4, 4)`;
* `triHexPlanarFiniteWiredBoundaryReachRatio_eq_homogeneous` at radius `0`, `q = 4`, `p = 1/2`
  (odds `1`, a root of `y³ + 3y² - 4`).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.FKFiniteWiredSweep

open _root_.StatMech.FK.PeriodicPlanar _root_.StatMech.FK.TriHex

-- Two terminals of the cell at `0` are triangular-lattice neighbors.
example : triangularGraph.Adj (triHexPlanarCellTerminal 0 0) (triHexPlanarCellTerminal 0 1) :=
  triangularGraph_adj_triHexPlanarCellTerminal 0 0 1 (by decide)

-- A terminal is a hexagonal neighbor of the black center.
example : hexagonalGraph.Adj (0, false) (triHexPlanarCellTerminal 0 2, true) :=
  hexagonalGraph_adj_triHexPlanarCellTerminal 0 2

-- Star–triangle invariance of the boundary-reach ratio on a single cell.
example : starFKFiniteWiredBoundaryReachRatio 4 4 4 4 (fun (_ : Fin 1) (i : Fin 3) => i)
      (fun v => v = 0) 2 =
    triangleFKFiniteWiredBoundaryReachRatio 4 1 1 1 (fun (_ : Fin 1) (i : Fin 3) => i)
      (fun v => v = 0) 2 :=
  triHexFK_finiteWiredBoundaryReachRatio_eq (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [triangularFKCriticalSurface]) _ _ _

-- The planar volume of radius `0` at the triangular critical point `p = 1/2`, `q = 4`.
example : (triHexPlanarFiniteWiredLevel 0).starBoundaryReachRatio 4 (1 / 2) =
    (triHexPlanarFiniteWiredLevel 0).triangleBoundaryReachRatio 4 (1 / 2) :=
  triHexPlanarFiniteWiredBoundaryReachRatio_eq_homogeneous 0 (by norm_num)
    ⟨by norm_num, by norm_num⟩ (by norm_num [triangularFKCriticalPolynomial, fkEdgeOdds])

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.FKFiniteWiredSweep
