/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.EnclosedAreaWitness

/-!
# Anchored cycles from the winding of the exit orbit

For a configuration `ω` with finite origin cluster, take the boundary dart across the exit edge on
the positive horizontal axis (`exitBaseSub`) and the face loop of one period of its orbit. If this
loop is a cycle and the origin has odd ray count with respect to it (`acc_ExitDartWinds`), the loop
crosses the ray to the left of the origin, so it visits a face with first coordinate at most zero.
That is the anchored-cycle property used in the Peierls bound, and assuming it for every `ω` gives
`p_c(ℤ²) < 1`.

The input `acc_ExitDartWinds` is not proved here for general `ω`; it holds for the unit cell
(`acc_unitCell_winds`). It follows from a full turn of the orbit, no pinched faces, the inclusion
of the inside of the loop in the cluster, and connectivity of the cluster off the loop
(`acc_exitDartWinds_of_turning_interior`).

## Main definitions

* `StatMech.Lattice.acc_exitFaceLoop hfin`: the face loop of the exit orbit, based at the upper exit
  face.
* `StatMech.Lattice.acc_ExitDartWinds ω hfin`: the exit face loop is a cycle and the origin has odd
  ray count.

## Main results

* `StatMech.Lattice.acc_cycleHasLeftFace_of_oddOrigin`: a winding cycle visits a face left of the
  origin.
* `StatMech.Lattice.acc_anchoredCycleExists_of_exitDartWinds`: `acc_ExitDartWinds` gives an anchored
  cycle.
* `StatMech.Lattice.acc_pc_lt_one_of_exitDartWinds`: `p_c(ℤ²) < 1`, assuming `acc_ExitDartWinds`
  for every configuration with finite origin cluster.
* `StatMech.Lattice.acc_exitDartWinds_of_turning_interior`: `acc_ExitDartWinds` from turning,
  no-pinch, interior and connectivity hypotheses.

## References

* R. Peierls, *On Ising's model of ferromagnetism*, Proc. Cambridge Philos. Soc. 32 (1936).
* G. Grimmett, *Percolation*, 2nd ed., Springer (1999), Section 1.4.
-/

@[expose] public section

open Finset Set SimpleGraph Function

namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}

/-- If a closed walk crosses the ray of `z` at least once, it visits a site whose first coordinate
is at most `z 0 - 1`. -/
theorem acc_oddRay_mem_support {u : Site 2} {z : Site 2}
    (c : (hypercubicLattice 2).Walk u u) (hpos : 0 < jec_rayCount z c) :
    ∃ f ∈ c.support, f 0 ≤ z 0 - 1 := by
  classical
  rw [jec_rayCount] at hpos
  obtain ⟨e, hmem, hpred⟩ := List.countP_pos_iff.mp hpos
  rw [decide_eq_true_eq] at hpred
  obtain ⟨f, g⟩ := e
  rw [jec_rayEdge_mk] at hpred
  refine ⟨f, c.fst_mem_support_of_mem_edges hmem, ?_⟩
  exact hpred.1.2

/-- The same as `acc_oddRay_mem_support` for a closed walk in a subgraph of the square lattice. -/
theorem acc_oddRay_mem_support_subgraph {G : SimpleGraph (Site 2)} (hle : G ≤ hypercubicLattice 2)
    {u : Site 2} {z : Site 2} (c : G.Walk u u)
    (hpos : 0 < jec_rayCount z (c.mapLe hle)) :
    ∃ f ∈ c.support, f 0 ≤ z 0 - 1 := by
  obtain ⟨f, hf, hcol⟩ := acc_oddRay_mem_support (c.mapLe hle) hpos
  rw [SimpleGraph.Walk.support_mapLe_eq_support] at hf
  exact ⟨f, hf, hcol⟩

/-- The face loop of one period of the exit orbit, as a closed walk in the face-boundary graph of
the origin cluster based at the upper exit face. -/
noncomputable def acc_exitFaceLoop (hfin : (cluster 2 ω (origin 2)).Finite) :
    (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk
      (exitFaceUp (ω := ω) hfin) (exitFaceUp (ω := ω) hfin) :=
  (mpl_orbitFaceLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)).copy
    (dartFace_exitDart (ω := ω) hfin) (dartFace_exitDart (ω := ω) hfin)

/-- The exit face loop is a cycle when the orbit face loop is. -/
theorem acc_exitFaceLoop_isCycle (hfin : (cluster 2 ω (origin 2)).Finite)
    (hcyc : (mpl_orbitFaceLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)).IsCycle) :
    (acc_exitFaceLoop (ω := ω) hfin).IsCycle := by
  unfold acc_exitFaceLoop
  exact (SimpleGraph.Walk.isCycle_copy _ _).mpr hcyc

theorem acc_exitFaceLoop_support (hfin : (cluster 2 ω (origin 2)).Finite) :
    (acc_exitFaceLoop (ω := ω) hfin).support
      = (mpl_orbitFaceLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)).support := by
  unfold acc_exitFaceLoop
  exact SimpleGraph.Walk.support_copy _ _ _

/-- The exit face loop and the orbit loop have the same ray counts. -/
theorem acc_rayCount_exitFaceLoop (hfin : (cluster 2 ω (origin 2)).Finite) (z : Site 2) :
    jec_rayCount z ((acc_exitFaceLoop (ω := ω) hfin).mapLe (faceBoundaryGraph_le _))
      = jec_rayCount z (mpl_orbitLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)) := by
  classical
  unfold acc_exitFaceLoop mpl_orbitLoop
  rw [jec_rayCount, jec_rayCount]
  congr 1
  rw [SimpleGraph.Walk.edges_mapLe_eq_edges, SimpleGraph.Walk.edges_mapLe_eq_edges]
  exact SimpleGraph.Walk.edges_copy _ _ _

/-- If the exit face loop is a cycle and the origin has odd ray count, the loop is a cycle based at
the upper exit face visiting a face with first coordinate at most zero (`CycleHasLeftFace`). -/
theorem acc_cycleHasLeftFace_of_oddOrigin (hfin : (cluster 2 ω (origin 2)).Finite)
    (hcyc : (mpl_orbitFaceLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)).IsCycle)
    (hodd : ¬ Even (jec_rayCount (origin 2)
      (mpl_orbitLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)))) :
    CycleHasLeftFace ω hfin := by
  classical
  have hpos0 : 0 < jec_rayCount (origin 2)
      (mpl_orbitLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)) := by
    rcases Nat.eq_zero_or_pos
        (jec_rayCount (origin 2)
          (mpl_orbitLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))) with h | h
    · exact absurd (by rw [h]; exact Nat.even_iff.mpr rfl) hodd
    · exact h
  have hpos : 0 < jec_rayCount (origin 2)
      ((acc_exitFaceLoop (ω := ω) hfin).mapLe (faceBoundaryGraph_le _)) := by
    rw [acc_rayCount_exitFaceLoop (ω := ω) hfin]; exact hpos0
  obtain ⟨f, hf, hcol⟩ :=
    acc_oddRay_mem_support_subgraph (faceBoundaryGraph_le _) (acc_exitFaceLoop (ω := ω) hfin) hpos
  have horig0 : (origin 2) 0 = 0 := rfl
  have hf0 : f 0 ≤ 0 := by rw [horig0] at hcol; omega
  exact ⟨acc_exitFaceLoop (ω := ω) hfin, acc_exitFaceLoop_isCycle (ω := ω) hfin hcyc, f, hf, hf0⟩

/-- Under the same hypotheses as `acc_cycleHasLeftFace_of_oddOrigin`, an anchored cycle exists. -/
theorem acc_anchoredCycleExists_of_oddOrigin (hfin : (cluster 2 ω (origin 2)).Finite)
    (hcyc : (mpl_orbitFaceLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)).IsCycle)
    (hodd : ¬ Even (jec_rayCount (origin 2)
      (mpl_orbitLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)))) :
    AnchoredCycleExists ω hfin :=
  anchoredCycleExists_of_leftFace (ω := ω) hfin
    (acc_cycleHasLeftFace_of_oddOrigin (ω := ω) hfin hcyc hodd)

/-- The face loop of the exit orbit of the origin cluster is a cycle, and the origin has odd ray
count with respect to it: the loop winds around the origin. -/
def acc_ExitDartWinds (ω : ConfigSpace (Sym2 (Site 2)))
    (hfin : (cluster 2 ω (origin 2)).Finite) : Prop :=
  (mpl_orbitFaceLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)).IsCycle ∧
    ¬ Even (jec_rayCount (origin 2)
      (mpl_orbitLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)))

/-- `acc_ExitDartWinds` gives an anchored cycle. -/
theorem acc_anchoredCycleExists_of_exitDartWinds (hfin : (cluster 2 ω (origin 2)).Finite)
    (h : acc_ExitDartWinds ω hfin) : AnchoredCycleExists ω hfin :=
  acc_anchoredCycleExists_of_oddOrigin (ω := ω) hfin h.1 h.2

/-- The anchored enclosure property, assuming `acc_ExitDartWinds` for every configuration with a
finite origin cluster. -/
theorem acc_pcAnchoredEnclosure_of_exitDartWinds
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        acc_ExitDartWinds ω hfin) :
    StatMech.Percolation.PcAnchoredEnclosure := by
  refine pcAnchoredEnclosure_of_cycleHasLeftFace (fun ω hfin => ?_)
  exact acc_cycleHasLeftFace_of_oddOrigin (ω := ω) hfin (h ω hfin).1 (h ω hfin).2

/-- **Peierls bound for bond percolation on `ℤ²`**, conditional form: `p_c(ℤ²) < 1`, assuming that
for every configuration with finite origin cluster the face loop of the exit orbit is a cycle
winding around the origin (`acc_ExitDartWinds`).

The literature result is unconditional (Peierls 1936; `p_c(ℤ²) = 1/2` by Kesten 1980). Here the
geometric input `acc_ExitDartWinds` is a hypothesis; it is not proved for general configurations.
See also `StatMech.Lattice.pc_lt_one_via_canonicalContour`, which assumes the weaker
`AnchoredCycleExists`. -/
theorem acc_pc_lt_one_of_exitDartWinds
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        acc_ExitDartWinds ω hfin) :
    StatMech.Percolation.pc 2 < 1 :=
  StatMech.Percolation.pc_lt_one_of_enclosure (acc_pcAnchoredEnclosure_of_exitDartWinds h)

/-- If the orbit loop is a cycle (period at least three, no pinched face), its inside lies in the
cluster, and every site of the cluster is joined off the loop to every cluster site of odd ray
count, then the origin has odd ray count. -/
theorem acc_oddOrigin_of_cycle_interior_intConn (hfin : (cluster 2 ω (origin 2)).Finite)
    (hp : 3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
    (hint : eaw_InteriorSubset (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
    (hIntConn : ∀ z, z ∈ cluster 2 ω (origin 2) →
      ∀ z0 : Site 2, z0 ∈ cluster 2 ω (origin 2) →
        ¬ Even (jec_rayCount z0
          (mpl_orbitLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))) →
        ∃ p : (hypercubicLattice 2).Walk z z0,
          (∀ w ∈ p.support,
            w ∉ (mpl_orbitLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)).support)) :
    ¬ Even (jec_rayCount (origin 2)
      (mpl_orbitLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))) := by
  have hcyc : (mpl_orbitLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)).IsCycle :=
    mpl_orbitLoop_isCycle (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin) hp
      (orbitFace_injOn_of_noPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin) hnp)
  obtain ⟨z0, hz0odd⟩ :=
    eaw_cycle_oddCell' (mpl_orbitLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)) hcyc
  have hz0K : z0 ∈ cluster 2 ω (origin 2) := hint z0 hz0odd
  obtain ⟨p, hp_supp⟩ :=
    hIntConn (origin 2) (self_mem_cluster ω (origin 2)) z0 hz0K hz0odd
  exact (ooi_odd_of_connected_to_odd
    (mpl_orbitLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)) p hp_supp hz0odd)

/-- `acc_ExitDartWinds` from period at least three, no pinched face, the inclusion of the inside of
the loop in the cluster, and connectivity of the cluster off the loop. -/
theorem acc_exitDartWinds_of_cycle_interior (hfin : (cluster 2 ω (origin 2)).Finite)
    (hp : 3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
    (hint : eaw_InteriorSubset (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
    (hIntConn : ∀ z, z ∈ cluster 2 ω (origin 2) →
      ∀ z0 : Site 2, z0 ∈ cluster 2 ω (origin 2) →
        ¬ Even (jec_rayCount z0
          (mpl_orbitLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))) →
        ∃ p : (hypercubicLattice 2).Walk z z0,
          (∀ w ∈ p.support,
            w ∉ (mpl_orbitLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)).support)) :
    acc_ExitDartWinds ω hfin := by
  refine ⟨?_, acc_oddOrigin_of_cycle_interior_intConn (ω := ω) hfin hp hnp hint hIntConn⟩
  exact mpl_orbitFaceLoop_isCycle (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin) hp
    (orbitFace_injOn_of_noPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin) hnp)

/-- An orbit turning by a full revolution has period at least three. -/
theorem acc_period_ge_three_of_fullRevolution (hfin : (cluster 2 ω (origin 2)).Finite)
    (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)) :
    3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin) := by
  have := orbitPeriod_ge_four_of_fullRevolution (cluster 2 ω (origin 2))
    (exitBaseSub (ω := ω) hfin) hturn
  omega

/-- `acc_ExitDartWinds` from a full turn of the exit orbit, no pinched face, the inclusion of the
inside of the loop in the cluster, and connectivity of the cluster off the loop. -/
theorem acc_exitDartWinds_of_turning_interior (hfin : (cluster 2 ω (origin 2)).Finite)
    (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
    (hint : eaw_InteriorSubset (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
    (hIntConn : ∀ z, z ∈ cluster 2 ω (origin 2) →
      ∀ z0 : Site 2, z0 ∈ cluster 2 ω (origin 2) →
        ¬ Even (jec_rayCount z0
          (mpl_orbitLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))) →
        ∃ p : (hypercubicLattice 2).Walk z z0,
          (∀ w ∈ p.support,
            w ∉ (mpl_orbitLoop (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)).support)) :
    acc_ExitDartWinds ω hfin :=
  acc_exitDartWinds_of_cycle_interior (ω := ω) hfin
    (acc_period_ge_three_of_fullRevolution (ω := ω) hfin hturn) hnp hint hIntConn

/-- The four faces of the unit cell orbit are distinct. -/
theorem acc_unitCell_faceInj :
    Set.InjOn (fun k => dartFace ((dartNext unitCell)^[k] ucBase.1))
      (Set.Iio (dartOrbitPeriod unitCell ucBase)) := by
  rw [unitCell_orbitPeriod_eq_four, show ucBase.1 = ucDart0 from rfl]
  exact unitCell_orbitFace_injOn

/-- The face loop of the unit cell is a cycle. -/
theorem acc_unitCell_faceLoop_isCycle : (mpl_orbitFaceLoop unitCell ucBase).IsCycle :=
  mpl_orbitFaceLoop_isCycle unitCell ucBase (by rw [unitCell_orbitPeriod_eq_four]; norm_num)
    acc_unitCell_faceInj

/-- The unit cell loop is a cycle winding around the origin. -/
theorem acc_unitCell_winds :
    (mpl_orbitFaceLoop unitCell ucBase).IsCycle ∧
      ¬ Even (jec_rayCount (origin 2) (mpl_orbitLoop unitCell ucBase)) := by
  refine ⟨acc_unitCell_faceLoop_isCycle, ?_⟩
  have horig : (origin 2) = (![0, 0] : Site 2) := by funext i; fin_cases i <;> rfl
  rw [horig, mpl_unitCell_rayCount_eq_one]
  decide

/-- The unit cell loop visits a face with first coordinate at most `-1`. -/
theorem acc_unitCell_hasLeftSupportFace :
    ∃ f ∈ (mpl_orbitLoop unitCell ucBase).support, f 0 ≤ -1 := by
  have hodd := acc_unitCell_winds.2
  have hpos : 0 < jec_rayCount (origin 2) (mpl_orbitLoop unitCell ucBase) := by
    rcases Nat.eq_zero_or_pos (jec_rayCount (origin 2) (mpl_orbitLoop unitCell ucBase)) with h | h
    · exact absurd (by rw [h]; exact Nat.even_iff.mpr rfl) hodd
    · exact h
  obtain ⟨f, hf, hcol⟩ := acc_oddRay_mem_support (mpl_orbitLoop unitCell ucBase) hpos
  have horig0 : (origin 2) 0 = 0 := rfl
  exact ⟨f, hf, by rw [horig0] at hcol; omega⟩

end Lattice

end StatMech
