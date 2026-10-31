/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.TorusConnected

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.TorusConnected`

* `onsTorusGraph_connected` for the `3 × 3` torus, and reachability of two explicit vertices;
* `onsTorusGraph_eq_cycleGraph_boxProd` at `n = 3` (the `4 × 4` torus).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.TorusConnected

open _root_.StatMech _root_.StatMech.BeffaraDC _root_.StatMech.Onsager

instance : Fact (2 < 3) := ⟨by norm_num⟩

instance : Fact (2 < 3 + 1) := ⟨by norm_num⟩

-- The `3 × 3` torus is connected.
example : (onsTorusGraph 3).Connected := onsTorusGraph_connected 3

-- Two explicit vertices of the `3 × 3` torus are joined by a path.
example : (onsTorusGraph 3).Reachable (0, 0) (1, 2) := (onsTorusGraph_connected 3).preconnected _ _

-- The `4 × 4` torus is the box product of two `4`-cycles.
example : onsTorusGraph (3 + 1) = SimpleGraph.cycleGraph (3 + 1) □ SimpleGraph.cycleGraph (3 + 1) :=
  onsTorusGraph_eq_cycleGraph_boxProd 3

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.TorusConnected
