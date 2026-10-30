/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.LatticeMengerAttach
public import MathlibExt.Probability.Percolation.InfiniteClusterCount

/-!
# Clusters running along an axis

A cluster that contains the first sites of an axis ray, with the axis edges open, reaches the ray;
neighbours of the origin with infinite clusters run along their axis.

## i. Overview

An infinite cluster reaches sites with arbitrarily large coordinates, also without the origin. If
the axis edges between `e_j` and `(L + 1) e_j` are open, these sites are connected, also without the
origin. `crr_ClusterRunsAlongAxis ω x j` asks for such an `L` with `x` connected to `e_j` and the
far end of the segment having an infinite cluster without the origin. It gives
`lma_ClusterReachesRay`, and neighbours of the origin on the axis with infinite cut clusters satisfy
it. `crr_AxisAssignment` is the same condition.

## ii. Key results

- `crr_clusterReachesRay_of_runsAlongAxis` : reaching the ray from running along the axis.

## iii. Table of contents

- A. Far sites
- B. Open axis segments
- C. Running along an axis

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

/-! ## A. Far sites -/

lemma crr_infinite_reaches_far_coord (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinf : (cluster d ω x).Infinite) (n : ℕ) :
    ∃ y, (∃ i : Fin d, n < (y i).natAbs) ∧ Connected d ω x y := by
  obtain ⟨y, hyb, hyc⟩ := StatMech.Percolation.bka_far_witness ω x hinf n
  rw [mem_box] at hyb
  push Not at hyb
  obtain ⟨i, hi⟩ := hyb
  exact ⟨y, ⟨i, hi⟩, hyc⟩

lemma crr_removeSite_infinite_reaches_far (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinf : (cluster d (removeSite 0 ω) x).Infinite) (n : ℕ) :
    ∃ y, y ∉ box d n ∧ Connected d (removeSite 0 ω) x y :=
  (cluster_infinite_iff (removeSite 0 ω) x).mp hinf n

/-! ## B. Open axis segments -/

lemma crr_axisOpen_connected_in (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    (hopen : ∀ t : ℕ, t < L → ω s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)) = true)
    (m : ℕ) (hm : m ≤ L) :
    Connected d ω (hrHD_rayPt j 1) (hrHD_rayPt j ((m : ℤ) + 1)) := by
  induction m with
  | zero => simpa using connected_rfl
  | succ p ih =>
    have hpL : p < L := by omega
    have hadj := hrHD_adj_rayPt j ((p : ℤ) + 1)
    have he2 : ((p : ℤ) + 1 + 1) = ((p : ℤ) + 2) := by ring
    rw [he2] at hadj
    have hstep : IsOpenEdge d ω (hrHD_rayPt j ((p : ℤ) + 1)) (hrHD_rayPt j ((p : ℤ) + 2)) :=
      ⟨hadj, hopen p hpL⟩
    have hrec := ih (by omega)
    have hgoal := hrec.trans hstep.connected
    have he : ((p : ℤ) + 2) = (((p : ℕ) + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
    rwa [he] at hgoal

lemma crr_axisOpen_connected_removeSite (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    (hopen : ∀ t : ℕ, t < L → ω s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)) = true)
    (m : ℕ) (hm : m ≤ L) :
    Connected d (removeSite 0 ω) (hrHD_rayPt j 1) (hrHD_rayPt j ((m : ℤ) + 1)) := by
  induction m with
  | zero => simpa using connected_rfl
  | succ p ih =>
    have hpL : p < L := by omega
    have hadj := hrHD_adj_rayPt j ((p : ℤ) + 1)
    have he2 : ((p : ℤ) + 1 + 1) = ((p : ℤ) + 2) := by ring
    rw [he2] at hadj
    have hno0 : (0 : Site d) ∉ s(hrHD_rayPt j ((p : ℤ) + 1), hrHD_rayPt j ((p : ℤ) + 2)) := by
      simp only [Sym2.mem_iff]; push Not
      refine ⟨?_, ?_⟩
      · intro h; rw [eq_comm, hrHD_rayPt_eq_zero_iff] at h; omega
      · intro h; rw [eq_comm, hrHD_rayPt_eq_zero_iff] at h; omega
    have hcfg : (removeSite 0 ω) s(hrHD_rayPt j ((p : ℤ) + 1),
        hrHD_rayPt j ((p : ℤ) + 2)) = true := by
      rw [removeSite_apply_of_notMem hno0]; exact hopen p hpL
    have hstep : IsOpenEdge d (removeSite 0 ω) (hrHD_rayPt j ((p : ℤ) + 1)) (hrHD_rayPt j ((p : ℤ)
        + 2)) :=
      ⟨hadj, hcfg⟩
    have hrec := ih (by omega)
    have hgoal := hrec.trans hstep.connected
    have he : ((p : ℤ) + 2) = (((p : ℕ) + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
    rwa [he] at hgoal

lemma crr_corridor_internal (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) (j : Fin d) (L : ℕ)
    (hxe1 : Connected d ω x (hrHD_rayPt j 1))
    (hopen : ∀ t : ℕ, t < L → ω s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)) = true) :
    ∀ e ∈ lma_corridorEdges j L, ∀ p, p ∈ e → p ∈ cluster d ω x := by
  intro e he p hp
  rw [lma_corridorEdges, Finset.mem_image] at he
  obtain ⟨t, ht, rfl⟩ := he
  rw [Finset.mem_range] at ht
  rw [Sym2.mem_iff] at hp
  rw [mem_cluster]
  rcases hp with rfl | rfl
  · have hc := crr_axisOpen_connected_in ω j L hopen t (by omega)
    exact hxe1.trans hc
  · have hc := crr_axisOpen_connected_in ω j L hopen (t + 1) (by omega)
    have he : (((t : ℕ) + 1 : ℕ) : ℤ) + 1 = ((t : ℤ) + 2) := by push_cast; ring
    rw [he] at hc
    exact hxe1.trans hc

/-! ## C. Running along an axis -/

/-- The cluster of `x` runs along axis `j`: for some `L` the axis edges from `e_j` to `(L + 1) e_j`
are
open, `x` is connected to `e_j`, and `(L + 1) e_j` has an infinite cluster without the origin. -/
def crr_ClusterRunsAlongAxis (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) (j : Fin d) :
    Prop :=
  ∃ L : ℕ,
    (∀ t : ℕ, t < L → ω s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)) = true) ∧
    Connected d ω x (hrHD_rayPt j 1) ∧
    Connected d (removeSite 0 ω) x (hrHD_rayPt j 1) ∧
    (cluster d (removeSite 0 ω) x).Infinite

lemma crr_clusterReachesRay_of_runsAlongAxis (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) (h : crr_ClusterRunsAlongAxis ω x j) :
    lma_ClusterReachesRay ω x j := by
  obtain ⟨L, hopen, hxe1, hxe1', hinf⟩ := h
  refine ⟨L, ?_, crr_corridor_internal ω x j L hxe1 hopen, ?_, hinf⟩
  · rw [mem_cluster]; exact hxe1
  · have hfar : Connected d (removeSite 0 ω) (hrHD_rayPt j 1) (hrHD_rayPt j ((L : ℤ) + 1)) :=
      crr_axisOpen_connected_removeSite ω j L hopen L le_rfl
    exact (hxe1'.trans hfar).symm

lemma crr_runsAlongAxis_of_neighbour (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d)
    (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
    crr_ClusterRunsAlongAxis ω (hrHD_rayPt j 1) j := by
  refine ⟨0, ?_, connected_rfl, connected_rfl, hinf⟩
  intro t ht; omega

lemma crr_clusterReachesRay_of_neighbour' (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d)
    (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
    lma_ClusterReachesRay ω (hrHD_rayPt j 1) j :=
  crr_clusterReachesRay_of_runsAlongAxis ω (hrHD_rayPt j 1) j
    (crr_runsAlongAxis_of_neighbour ω j hinf)

/-- Axis assignment, defined as `crr_ClusterRunsAlongAxis`. -/
def crr_AxisAssignment (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) (j : Fin d) : Prop :=
  crr_ClusterRunsAlongAxis ω x j

lemma crr_clusterReachesRay_of_assignment (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) (h : crr_AxisAssignment ω x j) :
    lma_ClusterReachesRay ω x j :=
  crr_clusterReachesRay_of_runsAlongAxis ω x j h

end Percolation

end StatMech
