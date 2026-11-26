/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.FKFiniteWiredWeights

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.FKFiniteWiredWeights`

At radius `0`, `q = 4`, `p = 1/2` (odds `y = 1`, a root of `y³ + 3y² - 4`), with dual parameter
`dualParam (1/2) 4 = 4/5` (odds `4`):
* `triHexPlanarFiniteTriangleWiredBoundaryProbability_eq` identifies the triangular wired
  boundary probability with the abstract triangle ratio (`1/2 = (1 - 1/2) · 1`);
* `triHexPlanarFiniteStarWiredBoundaryProbability_eq` does the same for the star at `p = 4/5`
  (`4/5 = (1 - 4/5) · 4`);
* `triHexPlanarFiniteWiredBoundaryProbability_eq_homogeneous`: the hexagonal probability at
  `4/5` equals the triangular one at `1/2`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.FKFiniteWiredWeights

open _root_.StatMech.FK.PeriodicPlanar _root_.StatMech.FK.TriHex _root_.StatMech.BeffaraDC

-- Triangle side: the measure-theoretic probability is the abstract sweep ratio.
example : triHexPlanarFiniteTriangleWiredBoundaryProbability 0 (1 / 2) 4 =
    triangleFKFiniteWiredBoundaryReachRatio 4 1 1 1 (triHexPlanarFiniteTerminalMap 0)
      (triHexPlanarFiniteBoundary 0)
      (triHexPlanarFiniteTerminalMap 0 (triHexPlanarFiniteRootCell 0) 0) :=
  triHexPlanarFiniteTriangleWiredBoundaryProbability_eq 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

-- Star side at the dual parameter `4/5`.
example : triHexPlanarFiniteStarWiredBoundaryProbability 0 (4 / 5) 4 =
    starFKFiniteWiredBoundaryReachRatio 4 4 4 4 (triHexPlanarFiniteTerminalMap 0)
      (triHexPlanarFiniteBoundary 0)
      (triHexPlanarFiniteTerminalMap 0 (triHexPlanarFiniteRootCell 0) 0) :=
  triHexPlanarFiniteStarWiredBoundaryProbability_eq 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

-- The headline at the critical point.
example : triHexPlanarFiniteStarWiredBoundaryProbability 0 (dualParam (1 / 2) 4) 4 =
    triHexPlanarFiniteTriangleWiredBoundaryProbability 0 (1 / 2) 4 :=
  triHexPlanarFiniteWiredBoundaryProbability_eq_homogeneous 0 (by norm_num)
    ⟨by norm_num, by norm_num⟩ (by norm_num [triangularFKCriticalPolynomial, fkEdgeOdds])

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.FKFiniteWiredWeights
