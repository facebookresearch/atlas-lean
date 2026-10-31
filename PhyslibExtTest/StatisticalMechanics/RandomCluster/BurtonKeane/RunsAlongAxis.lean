/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RunsAlongAxis

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RunsAlongAxis`

* non-vacuity: for the line configuration `line j` the cluster of `e_j` after opening the axis
  corridor and removing the origin is infinite (the positive half-line), so the hypothesis of the
  module is satisfiable;
* `rap_runsAlongAxis_ray`, `rap_clusterReachesRay_ray` and `rap_clusterMeetsCorridor_ray` applied to
  that instance;
* `rap_ray_open_edge_nonvacuous` on the all-closed configuration.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.RunsAlongAxis

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation

variable {d : ℕ}

open Classical in
/-- The configuration in which exactly the edges in coordinate direction `j` are open. -/
noncomputable def line (j : Fin d) : ConfigSpace (Sym2 (Site d)) :=
  fun e => decide (∃ z : Site d, e = s(z, z + Pi.single j 1))

/-- Each axis step is an open lattice edge of `line j`. -/
theorem line_adj (j : Fin d) (z : Site d) :
    (openSubgraph d (line j)).Adj z (z + Pi.single j 1) := by
  refine ⟨?_, ?_⟩
  · rw [hypercubicLattice_adj, Finset.sum_eq_single j]
    · simp
    · intro i _ hi; simp [hi]
    · simp
  · simp only [line, decide_eq_true_eq]; exact ⟨z, rfl⟩

open Classical in
/-- Opening the axis corridor does not change the line configuration along the same axis. -/
theorem forceOpen_line (j : Fin d) (L : ℕ) :
    forceOpenFinset (hrHD_corridorEdges j L) (line j) = line j := by
  funext e
  by_cases he : e ∈ hrHD_corridorEdges j L
  · rw [forceOpenFinset_of_mem he]
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp he
    exact (decide_eq_true ⟨hrHD_rayPt j t, by simp [hrHD_rayPt, ← Pi.single_add]⟩).symm
  · simp [forceOpenFinset, he]

/-- The positive half-line stays connected after the origin is removed. -/
theorem ray_connected (j : Fin d) (k : ℕ) :
    Connected d (removeSite 0 (line j)) (hrHD_rayPt j 1) (hrHD_rayPt j ((k : ℤ) + 1)) := by
  induction k with
  | zero => simpa using connected_refl _ _
  | succ k ih =>
    have hz : hrHD_rayPt j (((k + 1 : ℕ) : ℤ) + 1)
        = hrHD_rayPt j ((k : ℤ) + 1) + Pi.single j 1 := by
      rw [hrHD_rayPt, hrHD_rayPt, ← Pi.single_add]
      push_cast
      ring_nf
    have hmem : (0 : Site d) ∉ s(hrHD_rayPt j ((k : ℤ) + 1), hrHD_rayPt j ((k : ℤ) + 1)
        + Pi.single j 1) := by
      rw [Sym2.mem_iff, not_or]
      constructor <;> intro h <;> have := congrFun h j <;>
        simp only [hrHD_rayPt, Pi.zero_apply, Pi.add_apply, Pi.single_eq_same] at this <;> omega
    rw [hz]
    refine ih.trans (IsOpenEdge.connected ⟨(line_adj j _).1, ?_⟩)
    simp only [removeSite, hmem, ↓reduceIte]
    exact (line_adj j _).2

/-- So the cluster of `e_j` after removing the origin is infinite. -/
theorem ray_infinite (j : Fin d) (L : ℕ) :
    (cluster d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) (line j)))
      (hrHD_rayPt j 1)).Infinite := by
  rw [forceOpen_line]
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => hrHD_rayPt j ((k : ℤ) + 1))
    (fun a b h => ?_) (ray_connected j)
  have := congrFun h j
  simp only [hrHD_rayPt, Pi.single_eq_same] at this
  omega

-- The cluster runs along the axis in the line configuration.
example (j : Fin d) (L : ℕ) :
    crr_ClusterRunsAlongAxis (forceOpenFinset (hrHD_corridorEdges j (L + 1)) (line j))
      (hrHD_rayPt j 1) j :=
  (rap_runsAlongAxis_ray _ j L (ray_infinite j L)).2

-- It reaches the ray and meets the corridor.
example (j : Fin d) (L L' : ℕ) :
    lma_ClusterReachesRay (forceOpenFinset (hrHD_corridorEdges j (L + 1)) (line j))
        (hrHD_rayPt j 1) j ∧
      cnp_ClusterMeetsCorridor (forceOpenFinset (hrHD_corridorEdges j (L + 1)) (line j))
        (hrHD_rayPt j 1) j L' :=
  ⟨rap_clusterReachesRay_ray _ j L (ray_infinite j L),
    rap_clusterMeetsCorridor_ray _ j L L' (ray_infinite j L)⟩

-- The first corridor edge is open after forcing, even in the all-closed configuration.
example (j : Fin d) (L : ℕ) (hL : 1 ≤ L) :
    forceOpenFinset (hrHD_corridorEdges j (L + 1)) (fun _ => false)
      s(hrHD_rayPt j (((0 : ℕ) : ℤ) + 1), hrHD_rayPt j (((0 : ℕ) : ℤ) + 2)) = true :=
  rap_ray_open_edge_nonvacuous _ j L hL

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.RunsAlongAxis
