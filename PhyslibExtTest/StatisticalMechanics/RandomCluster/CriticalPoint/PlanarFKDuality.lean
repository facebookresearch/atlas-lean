/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.PlanarFKDuality

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.PlanarFKDuality`

On the one-vertex planar subgraph of `ℤ²` (vertex at the origin, no edges):
* `pfd_numDualClusters_eq_faceCount` and `pfd_clusterEuler` for the empty open subgraph;
* `pfd_weight_duality` at `p = 1/2`, `q = 2`;
* `pfd_fkProb_duality` at `p = 1/3`, `q = 2` for the unique configuration.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.PlanarFKDuality

open _root_.StatMech _root_.StatMech.BeffaraDC _root_.StatMech.Lattice

/-- The planar subgraph with one vertex at the origin and no edges. -/
noncomputable def P1 : PlanarZ2Subgraph where
  V := Unit
  finV := inferInstance
  decV := inferInstance
  G := ⊥
  emb := ⟨fun _ => 0, fun _ _ _ => rfl⟩
  isSub := fun _ _ h => h.elim

-- Dual clusters are faces.
example := pfd_numDualClusters_eq_faceCount P1 ⊥ le_rfl

-- Euler's formula for clusters and dual clusters.
example := pfd_clusterEuler P1 ⊥ le_rfl

-- Weight duality at `p = 1/2`, `q = 2`.
example := pfd_weight_duality P1 ⊥ le_rfl (p := 1 / 2) (q := 2)
  (by norm_num) (by norm_num) (by norm_num)

-- Measure duality at `p = 1/3`, `q = 2`.
example (omega : ConfigSpace (Sym2 P1.V)) :=
  pfd_fkProb_duality P1 omega (p := 1 / 3) (q := 2) (by norm_num) (by norm_num) (by norm_num)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.PlanarFKDuality
