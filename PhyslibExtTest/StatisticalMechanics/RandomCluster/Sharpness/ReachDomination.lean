/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.ReachDomination

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.ReachDomination`

On the path `0 — 1 — 2` (two edges, endpoints `![0, 1]` and `![1, 2]`), frontier `{0}`:

* non-vacuity of `ClusterMeasurable`: `clusterMeasurable_indicatorConn` for the indicator that
  site `2` is connected to `{0}`;
* `IncidentCluster` holds for edge `0` (its first endpoint lies in the frontier);
* `frontierConn_indicatorConn_last`: `FrontierConn` for the last edge of the identity order;
* `frontierConn_of_clusterMeasurable` via `prefixCoversCluster_of_prefix_cofinite`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.ReachDomination

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.ReachDomination
open _root_.StatMech.OSSS.ReachBoxCrossing _root_.StatMech.OSSS.RevealmentConstruction

/-- First endpoints of the path `0 — 1 — 2`. -/
def endU : Fin 2 → Fin 3 := ![0, 1]

/-- Second endpoints of the path `0 — 1 — 2`. -/
def endV : Fin 2 → Fin 3 := ![1, 2]

-- Connection indicators are cluster measurable.
example : ClusterMeasurable (indicatorConn endU endV {0} {2}) endU endV {0} :=
  clusterMeasurable_indicatorConn endU endV {0} {2}

-- Edge `0` meets the cluster of `{0}` in every configuration.
example (X : ConfigSpace (Fin 2)) : IncidentCluster endU endV X {0} 0 :=
  Or.inl (connOpenSet_of_mem rfl)

-- The last edge of the identity order satisfies the frontier connection.
example : FrontierConn (Equiv.refl (Fin 2)) (indicatorConn endU endV {0} {2}) endU endV {0} 1 :=
  frontierConn_indicatorConn_last (by norm_num) _ endU endV {0} {2} rfl

-- `PrefixCoversCluster` ⇒ `FrontierConn` for a cluster-measurable observable.
example (f : ConfigSpace (Fin 2) → ℝ) (hf : ClusterMeasurable f endU endV {0}) :
    FrontierConn (Equiv.refl (Fin 2)) f endU endV {0} 1 :=
  frontierConn_of_clusterMeasurable _ endU endV {0} 1 hf
    (prefixCoversCluster_of_prefix_cofinite _ endU endV {0} 1
      (prefix_cofinite_of_last (by norm_num) _ rfl))

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.ReachDomination
