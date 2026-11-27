/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.FiniteGraphBoundaryDifferential

/-!
# Tests for `FiniteGraphBoundaryDifferential`

Module under test:
`PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.FiniteGraphBoundaryDifferential`

* `openCrossEvent_isIncreasing` for one edge `0 — 1` on `Fin 2`, crossing from `0` to `{1}`;
* `closedProd_incident_le_openCross_complement` on the same instance
  (`0 ∉ {1}`);
* `activeBC_openCross_one_sub_lower` and `activeBC_openCross_differential_inequality`, the
  headline conditional inequalities, stated as terms.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness
namespace FiniteGraphBoundaryDifferential

open _root_.StatMech _root_.StatMech.OSSS
open _root_.StatMech.OSSS.FiniteGraphBoundaryDifferential

-- The open-crossing event from `0` to `{1}` along a single edge is increasing.
example :
    IsIncreasing (openCrossEvent (fun _ : Fin 1 => (0 : Fin 2)) (fun _ => 1) 0 {1}) :=
  openCrossEvent_isIncreasing _ _ _ _

-- If all edges at `0` are closed then `0` is not connected to `{1}`.
example (ω : ConfigSpace (Fin 1)) :
    FK.closedProd (openIncidentEdges (fun _ : Fin 1 => (0 : Fin 2)) (fun _ => 1) 0) ω
      ≤ 1 - (openCrossEvent (fun _ : Fin 1 => (0 : Fin 2)) (fun _ => 1) 0 {1}).indicator
          (fun _ => (1 : ℝ)) ω :=
  closedProd_incident_le_openCross_complement _ _ _ _ (by simp) ω

-- The lower bound on the non-crossing probability elaborates with its hypotheses.
example := @activeBC_openCross_one_sub_lower

-- The finite-graph OSSS differential inequality elaborates with its hypotheses.
example := @activeBC_openCross_differential_inequality

end FiniteGraphBoundaryDifferential
end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness
