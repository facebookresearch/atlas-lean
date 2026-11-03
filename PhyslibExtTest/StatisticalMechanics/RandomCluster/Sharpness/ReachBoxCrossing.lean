/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.ReachBoxCrossing

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.ReachBoxCrossing`

* non-vacuity of `FrontierConn`: `frontierConn_univ` on two edges with an arbitrary observable;
* `frontierConn_satisfiable` for the uniform mass on configurations of two edges;
* `reachProb_le_connOpen` applied to the frontier `univ`;
* `revealAdapt_le_connBox` and `os_cov_lower_bound_from_box_crossing`, stated by name.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.ReachBoxCrossing

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.ReachBoxCrossing
open _root_.StatMech.OSSS.RevealmentConstruction _root_.StatMech.OSSS.AdaptMConditional
open _root_.StatMech.OSSS.RevealmentBoxCrossing

/-- First endpoints of the path `0 — 1 — 2`. -/
def endU : Fin 2 → Fin 3 := ![0, 1]

/-- Second endpoints of the path `0 — 1 — 2`. -/
def endV : Fin 2 → Fin 3 := ![1, 2]

-- Non-vacuity: the frontier connection holds for the frontier `univ`.
example (f : ConfigSpace (Fin 2) → ℝ) (e : Fin 2) :
    FrontierConn (Equiv.refl (Fin 2)) f endU endV Set.univ e :=
  frontierConn_univ _ f endU endV e

open Classical in
-- The reach probability bound for the uniform mass, with frontier `univ`.
example (f : ConfigSpace (Fin 2) → ℝ) (e : Fin 2) :
    reachProb (fun _ => (1 / 4 : ℝ)) (Equiv.refl (Fin 2)) f e
      ≤ Lindeberg.mean (fun _ => (1 / 4 : ℝ))
          (fun X => if ConnOpenSet endU endV X (endU e) Set.univ then (1 : ℝ) else 0)
        + Lindeberg.mean (fun _ => (1 / 4 : ℝ))
          (fun X => if ConnOpenSet endU endV X (endV e) Set.univ then (1 : ℝ) else 0) :=
  frontierConn_satisfiable (fun _ => by norm_num) _ f endU endV e

open Classical in
-- The same bound through `reachProb_le_connOpen`.
example (f : ConfigSpace (Fin 2) → ℝ) :
    reachProb (fun _ => (1 / 4 : ℝ)) (Equiv.refl (Fin 2)) f 0
      ≤ Lindeberg.mean (fun _ => (1 / 4 : ℝ))
          (fun X => if ConnOpenSet endU endV X (endU 0) Set.univ then (1 : ℝ) else 0)
        + Lindeberg.mean (fun _ => (1 / 4 : ℝ))
          (fun X => if ConnOpenSet endU endV X (endV 0) Set.univ then (1 : ℝ) else 0) :=
  reachProb_le_connOpen (fun _ => by norm_num) _ f endU endV Set.univ 0
    (frontierConn_univ _ f endU endV 0)

-- The conditional revealment and covariance bounds exist with the expected names.
example := @revealAdapt_le_connBox
example := @os_cov_lower_bound_from_box_crossing

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.ReachBoxCrossing
