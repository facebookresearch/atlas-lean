/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TwoPointPathLower

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TwoPointPathLower`

On the one-edge graph `⊤` on `Fin 2` at `p = 1/2`, `q = 2`:
* `cFE_pow_walk_length_le_twoPoint` for the one-step walk `0 → 1` (bound `cFE`);
* the same for the empty walk at `0` (bound `1`).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TwoPointPathLower

open _root_.StatMech _root_.StatMech.FK

/-- The one-edge test graph. -/
abbrev G2 : SimpleGraph (Fin 2) := ⊤

/-- The one-step walk from `0` to `1`. -/
def w01 : G2.Walk 0 1 := .cons (by decide) .nil

-- The two-point function is at least `cFE`.
example : cFE (1 / 2) 2 ≤ twoPointFun G2 (1 / 2) 2 0 1 := by
  simpa [w01] using
    cFE_pow_walk_length_le_twoPoint G2 (p := 1 / 2) (by norm_num) (by norm_num) one_le_two w01

-- The empty walk gives the trivial bound `1 ≤ φ(0 ↔ 0)`.
example : cFE (1 / 2) 2 ^ 0 ≤ twoPointFun G2 (1 / 2) 2 0 0 :=
  cFE_pow_walk_length_le_twoPoint G2 (p := 1 / 2) (by norm_num) (by norm_num) one_le_two
    (SimpleGraph.Walk.nil : G2.Walk 0 0)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TwoPointPathLower
