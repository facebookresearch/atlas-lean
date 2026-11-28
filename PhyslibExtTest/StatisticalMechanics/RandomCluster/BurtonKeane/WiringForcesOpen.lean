/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.WiringForcesOpen

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.WiringForcesOpen`

* instance: in `ℤ¹` with the all-closed configuration, forcing the axis corridor of length `3` makes
  the edge from `1` to `2` open (`bc_wiring_forces_open_eq_true`);
* `bc_wiring_forces_open`: the corridor edge from `2` to `3` is an open lattice edge, so its
  endpoints are connected;
* the general statement for every `t < L` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.WiringForcesOpen

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

-- The corridor edge `{e₀, 2e₀}` is open after forcing the corridor in the all-closed configuration.
example : forceOpenFinset (hrHD_corridorEdges (0 : Fin 1) (2 + 1)) (fun _ => false)
    s(hrHD_rayPt 0 (((0 : ℕ) : ℤ) + 1), hrHD_rayPt 0 (((0 : ℕ) : ℤ) + 2)) = true :=
  bc_wiring_forces_open_eq_true _ 0 2 0 (by decide)

-- It is an open lattice edge, so its endpoints are connected.
example : Connected 1 (forceOpenFinset (hrHD_corridorEdges (0 : Fin 1) (2 + 1)) (fun _ => false))
    (hrHD_rayPt 0 (((1 : ℕ) : ℤ) + 1)) (hrHD_rayPt 0 (((1 : ℕ) : ℤ) + 2)) :=
  (bc_wiring_forces_open _ 0 2 1 (by decide)).connected

-- Every corridor edge is open after forcing.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L t : ℕ) (ht : t < L) :
    IsOpenEdge d (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω)
      (hrHD_rayPt j ((t : ℤ) + 1)) (hrHD_rayPt j ((t : ℤ) + 2)) :=
  bc_wiring_forces_open ω j L t ht

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.WiringForcesOpen
