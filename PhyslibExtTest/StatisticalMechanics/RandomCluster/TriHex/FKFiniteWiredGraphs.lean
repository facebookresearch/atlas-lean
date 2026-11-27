/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.FKFiniteWiredGraphs

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.FKFiniteWiredGraphs`

* the triangle and star edge sets both have `3 · #cells` edges (`…EdgeEquiv`);
* `triHexPlanarFiniteStarConfigEquiv_direction` reads off an all-open configuration;
* `TriHexPlanarFiniteStarIsolatedCenter` is inhabited (non-vacuity) for the all-closed star
  configuration, at every cell;
* `triHexPlanarFiniteStar_numClustersWired_eq_sector_add_isolated` applied to the all-closed
  configuration at radius `0`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.FKFiniteWiredGraphs

open _root_.StatMech.FK.PeriodicPlanar _root_.StatMech.FK _root_.StatMech.Lattice

-- Both finite graphs have three edges per cell.
example (n : ℕ) : Nat.card (triHexPlanarFiniteTriangleGraph n).edgeSet =
      Nat.card (TriHexPlanarFiniteCell n × Fin 3) ∧
    Nat.card (triHexPlanarFiniteStarGraph n).edgeSet =
      Nat.card (TriHexPlanarFiniteCell n × Fin 3) :=
  ⟨(Nat.card_congr (triHexPlanarFiniteTriangleEdgeEquiv n)).symm,
    (Nat.card_congr (triHexPlanarFiniteStarEdgeEquiv n)).symm⟩

-- The all-open configuration opens every spoke of every star.
example (n : ℕ) (z : TriHexPlanarFiniteCell n) (i : Fin 3) :
    triHexLocalDirection (triHexPlanarFiniteStarConfigEquiv n (fun _ => true) z) i = true := by
  simp

/-- In the all-closed star configuration every black center is isolated. -/
noncomputable def isolatedCenter (n : ℕ) (z : TriHexPlanarFiniteCell n) :
    TriHexPlanarFiniteStarIsolatedCenter n (fun _ => false) := by
  refine ⟨z, ?_⟩
  have h : ∀ i, triHexLocalDirection
      (triHexPlanarFiniteStarConfigEquiv n (fun _ => false) z) i = false := by
    intro i
    simp
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp only [triHexLocalDirection, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two] at h0 h1 h2
  exact Prod.ext h0 (Prod.ext h1 h2)

-- The wired star cluster count splits off the isolated centers (all-closed, radius `0`).
example : numClustersWired (triHexPlanarFiniteStarGraph 0) (triHexPlanarFiniteStarBoundary 0)
      (extendActive (triHexPlanarFiniteStarGraph 0) (fun _ => false)) =
    Nat.card (triHexPlanarFiniteStarWiredSectorGraph 0 (fun _ => false)).ConnectedComponent +
      Fintype.card (TriHexPlanarFiniteStarIsolatedCenter 0 (fun _ => false)) :=
  triHexPlanarFiniteStar_numClustersWired_eq_sector_add_isolated 0 _

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.FKFiniteWiredGraphs
