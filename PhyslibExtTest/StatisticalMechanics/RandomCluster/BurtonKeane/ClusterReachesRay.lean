/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClusterReachesRay

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClusterReachesRay`

* `crr_axisOpen_connected_in` and `crr_axisOpen_connected_removeSite` for the all-open
  configuration of `ℤ²`;
* `crr_corridor_internal` for the all-open configuration at `x = e₀`;
* `crr_clusterReachesRay_of_runsAlongAxis` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ClusterReachesRay

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation

-- Along an open axis, `e₀` is connected to `4 e₀` (all-open configuration).
example : Connected 2 (fun _ => true) (hrHD_rayPt 0 1) (hrHD_rayPt 0 ((3 : ℕ) + 1)) :=
  crr_axisOpen_connected_in _ 0 5 (fun _ _ => rfl) 3 (by norm_num)

-- The same after removing the origin.
example : Connected 2 (removeSite 0 (fun _ => true)) (hrHD_rayPt 0 1)
    (hrHD_rayPt 0 ((3 : ℕ) + 1)) :=
  crr_axisOpen_connected_removeSite _ 0 5 (fun _ _ => rfl) 3 (by norm_num)

-- Corridor edges lie in the cluster of `e₀` (all-open configuration).
example := crr_corridor_internal (d := 2) (fun _ => true) (hrHD_rayPt 0 1) 0 4
  (connected_refl _ _) (fun _ _ => rfl)

-- Running along an axis reaches the ray.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) (j : Fin d)
    (h : crr_ClusterRunsAlongAxis ω x j) : lma_ClusterReachesRay ω x j :=
  crr_clusterReachesRay_of_runsAlongAxis ω x j h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ClusterReachesRay
