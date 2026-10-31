/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClusterReachesRay
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.MengerCorridors
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.WiringForcesOpen

/-!
# Running along an axis after forcing the corridor

Forcing the axis corridor opens its axis edges, so a cluster connected to the axis neighbour after
forcing runs along the axis in the forced configuration.

## i. Overview

The axis edges between `e_j` and `(L + 1) e_j` belong to `hrHD_corridorEdges j (L + 1)`, so they are
open after forcing it. `craf_AxisRoutingPremise ω x j L` asks that, after forcing, `x` be connected
to `e_j` and `(L + 1) e_j` have an infinite cluster without the origin. It gives the run-along
condition, axis assignment and ray reaching for the forced configuration, and holds for the axis
neighbour.

## ii. Key results

- `craf_clusterRunsAlongAxis_of_insertion` : running along the axis after forcing.

## iii. Table of contents

- A. The forced corridor

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}

/-! ## A. The forced corridor -/

lemma craf_mem_corridorEdges (j : Fin d) (L : ℕ) {t : ℕ} (ht : t < L) :
    s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)) ∈ hrHD_corridorEdges j (L + 1) := by
  have hmem := hrHD_mem_corridorEdges (j := j) (L := L + 1) (t := t + 1) (by omega)
  have e1 : (((t : ℕ) + 1 : ℕ) : ℤ) = (t : ℤ) + 1 := by push_cast; ring
  rw [e1] at hmem
  have e2 : ((t : ℤ) + 1 + 1) = (t : ℤ) + 2 := by ring
  rwa [e2] at hmem

/-- After forcing the corridor along `j`, `x` is connected to `e_j` and `(L + 1) e_j` has an
infinite
cluster without the origin. -/
def craf_AxisRoutingPremise (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) (j : Fin d)
    (L : ℕ) : Prop :=
  Connected d (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) x (hrHD_rayPt j 1) ∧
    Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω)) x
      (hrHD_rayPt j 1) ∧
    (cluster d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω)) x).Infinite

lemma craf_clusterRunsAlongAxis_of_insertion (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) (L : ℕ) (h : craf_AxisRoutingPremise ω x j L) :
    crr_ClusterRunsAlongAxis (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) x j := by
  obtain ⟨hnear, hnearCut, hinf⟩ := h
  exact ⟨L, fun t ht => Walls.bc_wiring_forces_open_eq_true ω j L t ht, hnear, hnearCut, hinf⟩

lemma craf_axisAssignment_of_insertion (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) (L : ℕ) (h : craf_AxisRoutingPremise ω x j L) :
    crr_AxisAssignment (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) x j :=
  craf_clusterRunsAlongAxis_of_insertion ω x j L h

lemma craf_clusterReachesRay_of_insertion (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) (L : ℕ) (h : craf_AxisRoutingPremise ω x j L) :
    lma_ClusterReachesRay (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) x j :=
  crr_clusterReachesRay_of_assignment (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) x j
    (craf_axisAssignment_of_insertion ω x j L h)

lemma craf_axisRoutingPremise_neighbour (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    (hinf : (cluster d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω))
      (hrHD_rayPt j 1)).Infinite) :
    craf_AxisRoutingPremise ω (hrHD_rayPt j 1) j L :=
  ⟨connected_rfl, connected_rfl, hinf⟩

lemma craf_axisAssignment_of_neighbour_insertion (ω : ConfigSpace (Sym2 (Site d)))
    (j : Fin d) (L : ℕ)
    (hinf : (cluster d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω))
      (hrHD_rayPt j 1)).Infinite) :
    crr_AxisAssignment (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) (hrHD_rayPt j 1) j :=
  craf_axisAssignment_of_insertion ω (hrHD_rayPt j 1) j L
    (craf_axisRoutingPremise_neighbour ω j L hinf)

end Percolation

end StatMech
