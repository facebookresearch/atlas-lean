/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































import Mathlib
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual
import Code.Lattice.Clusters
import Code.Lattice.JordanZ2
import Code.Lattice.JordanEnclosure
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.PlanarTopology
import Code.Lattice.CrossingParity
import Code.Lattice.ContourAnchor
import Code.Lattice.EnclosingLength
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartInjective
import Code.Lattice.DartOrbit
import Code.Lattice.ContourLinksExits
import Code.Lattice.TurningNumber
import Code.Lattice.CornerBalance
import Code.Lattice.MinimalPeriodLoop
import Code.Lattice.Umlaufsatz
import Code.Lattice.UmlaufsatzSingleCycle
import Code.Lattice.OrbitExteriorEven
import Code.Lattice.OrbitInteriorOdd
import Code.Lattice.WindingEarInduction
import Code.Lattice.EnclosedAreaWitness
import Code.Percolation.PcUpperUncond

open Finset Set SimpleGraph Function

namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}











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





theorem acc_oddRay_mem_support_subgraph {G : SimpleGraph (Site 2)} (hle : G ≤ hypercubicLattice 2)
    {u : Site 2} {z : Site 2} (c : G.Walk u u)
    (hpos : 0 < jec_rayCount z (c.mapLe hle)) :
    ∃ f ∈ c.support, f 0 ≤ z 0 - 1 := by
  obtain ⟨f, hf, hcol⟩ := acc_oddRay_mem_support (c.mapLe hle) hpos
  rw [SimpleGraph.Walk.support_mapLe_eq_support] at hf
  exact ⟨f, hf, hcol⟩









noncomputable def acc_exitSub (hfin : (cluster 2 ω (origin 2)).Finite) :
    {e : Dart // IsBoundaryDart (cluster 2 ω (origin 2)) e} :=
  ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩





noncomputable def acc_exitFaceLoop (hfin : (cluster 2 ω (origin 2)).Finite) :
    (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk
      (exitFaceUp (ω := ω) hfin) (exitFaceUp (ω := ω) hfin) :=
  (mpl_orbitFaceLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).copy
    (dartFace_exitDart (ω := ω) hfin) (dartFace_exitDart (ω := ω) hfin)


theorem acc_isCycle_copy {V : Type*} {G : SimpleGraph V} {u u' : V} (c : G.Walk u u) (hu : u = u')
    (h : c.IsCycle) : (c.copy hu hu).IsCycle := by
  subst hu; rw [SimpleGraph.Walk.copy_rfl_rfl]; exact h



theorem acc_exitFaceLoop_isCycle (hfin : (cluster 2 ω (origin 2)).Finite)
    (hcyc : (mpl_orbitFaceLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).IsCycle) :
    (acc_exitFaceLoop (ω := ω) hfin).IsCycle := by
  unfold acc_exitFaceLoop
  exact acc_isCycle_copy _ (dartFace_exitDart (ω := ω) hfin) hcyc



theorem acc_exitFaceLoop_support (hfin : (cluster 2 ω (origin 2)).Finite) :
    (acc_exitFaceLoop (ω := ω) hfin).support
      = (mpl_orbitFaceLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).support := by
  unfold acc_exitFaceLoop
  rw [SimpleGraph.Walk.support_copy]





theorem acc_rayCount_exitFaceLoop (hfin : (cluster 2 ω (origin 2)).Finite) (z : Site 2) :
    jec_rayCount z ((acc_exitFaceLoop (ω := ω) hfin).mapLe (faceBoundaryGraph_le _))
      = jec_rayCount z (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)) := by
  classical
  unfold acc_exitFaceLoop mpl_orbitLoop
  rw [jec_rayCount, jec_rayCount]
  congr 1
  rw [SimpleGraph.Walk.edges_mapLe_eq_edges, SimpleGraph.Walk.edges_copy,
    SimpleGraph.Walk.edges_mapLe_eq_edges]















theorem acc_cycleHasLeftFace_of_oddOrigin (hfin : (cluster 2 ω (origin 2)).Finite)
    (hcyc : (mpl_orbitFaceLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).IsCycle)
    (hodd : ¬ Even (jec_rayCount (origin 2)
      (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)))) :
    CycleHasLeftFace ω hfin := by
  classical
  
  have hpos0 : 0 < jec_rayCount (origin 2)
      (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)) := by
    rcases Nat.eq_zero_or_pos
        (jec_rayCount (origin 2)
          (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))) with h | h
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













theorem acc_anchoredCycleExists_of_oddOrigin (hfin : (cluster 2 ω (origin 2)).Finite)
    (hcyc : (mpl_orbitFaceLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).IsCycle)
    (hodd : ¬ Even (jec_rayCount (origin 2)
      (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)))) :
    AnchoredCycleExists ω hfin :=
  anchoredCycleExists_of_leftFace (ω := ω) hfin
    (acc_cycleHasLeftFace_of_oddOrigin (ω := ω) hfin hcyc hodd)







def acc_ExitDartWinds (ω : ConfigSpace (Sym2 (Site 2)))
    (hfin : (cluster 2 ω (origin 2)).Finite) : Prop :=
  (mpl_orbitFaceLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).IsCycle ∧
    ¬ Even (jec_rayCount (origin 2)
      (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)))


theorem acc_anchoredCycleExists_of_exitDartWinds (hfin : (cluster 2 ω (origin 2)).Finite)
    (h : acc_ExitDartWinds ω hfin) : AnchoredCycleExists ω hfin :=
  acc_anchoredCycleExists_of_oddOrigin (ω := ω) hfin h.1 h.2




theorem acc_pcAnchoredEnclosure_of_exitDartWinds
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        acc_ExitDartWinds ω hfin) :
    StatMech.Percolation.PcAnchoredEnclosure := by
  refine pcAnchoredEnclosure_of_cycleHasLeftFace (fun ω hfin => ?_)
  exact acc_cycleHasLeftFace_of_oddOrigin (ω := ω) hfin (h ω hfin).1 (h ω hfin).2





theorem acc_pc_lt_one_of_exitDartWinds
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        acc_ExitDartWinds ω hfin) :
    StatMech.Percolation.pc 2 < 1 :=
  StatMech.Percolation.pc_lt_one_of_enclosure (acc_pcAnchoredEnclosure_of_exitDartWinds h)














theorem acc_origin_mem_cluster (_hfin : (cluster 2 ω (origin 2)).Finite) :
    (origin 2) ∈ cluster 2 ω (origin 2) :=
  self_mem_cluster ω (origin 2)













theorem acc_oddOrigin_of_cycle_interior_intConn (hfin : (cluster 2 ω (origin 2)).Finite)
    (hp : 3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hint : eaw_InteriorSubset (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hIntConn : ∀ z, z ∈ cluster 2 ω (origin 2) →
      ∀ z0 : Site 2, z0 ∈ cluster 2 ω (origin 2) →
        ¬ Even (jec_rayCount z0
          (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))) →
        ∃ p : (hypercubicLattice 2).Walk z z0,
          (∀ w ∈ p.support,
            w ∉ (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).support)) :
    ¬ Even (jec_rayCount (origin 2)
      (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))) := by
  
  have hcyc : (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).IsCycle :=
    mpl_orbitLoop_isCycle (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) hp
      (orbitFace_injOn_of_noPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) hnp)
  
  obtain ⟨z0, hz0odd⟩ :=
    eaw_cycle_oddCell' (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)) hcyc
  
  have hz0K : z0 ∈ cluster 2 ω (origin 2) := hint z0 hz0odd
  
  obtain ⟨p, hp_supp⟩ :=
    hIntConn (origin 2) (acc_origin_mem_cluster (ω := ω) hfin) z0 hz0K hz0odd
  
  exact (ooi_odd_of_connected_to_odd
    (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)) p hp_supp hz0odd)






theorem acc_exitDartWinds_of_cycle_interior (hfin : (cluster 2 ω (origin 2)).Finite)
    (hp : 3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hint : eaw_InteriorSubset (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hIntConn : ∀ z, z ∈ cluster 2 ω (origin 2) →
      ∀ z0 : Site 2, z0 ∈ cluster 2 ω (origin 2) →
        ¬ Even (jec_rayCount z0
          (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))) →
        ∃ p : (hypercubicLattice 2).Walk z z0,
          (∀ w ∈ p.support,
            w ∉ (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).support)) :
    acc_ExitDartWinds ω hfin := by
  refine ⟨?_, acc_oddOrigin_of_cycle_interior_intConn (ω := ω) hfin hp hnp hint hIntConn⟩
  exact mpl_orbitFaceLoop_isCycle (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) hp
    (orbitFace_injOn_of_noPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) hnp)














theorem acc_period_ge_three_of_fullRevolution (hfin : (cluster 2 ω (origin 2)).Finite)
    (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)) :
    3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) := by
  have := orbitPeriod_ge_four_of_fullRevolution (cluster 2 ω (origin 2))
    (acc_exitSub (ω := ω) hfin) hturn
  omega






theorem acc_exitDartWinds_of_turning_interior (hfin : (cluster 2 ω (origin 2)).Finite)
    (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hint : eaw_InteriorSubset (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hIntConn : ∀ z, z ∈ cluster 2 ω (origin 2) →
      ∀ z0 : Site 2, z0 ∈ cluster 2 ω (origin 2) →
        ¬ Even (jec_rayCount z0
          (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))) →
        ∃ p : (hypercubicLattice 2).Walk z z0,
          (∀ w ∈ p.support,
            w ∉ (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).support)) :
    acc_ExitDartWinds ω hfin :=
  acc_exitDartWinds_of_cycle_interior (ω := ω) hfin
    (acc_period_ge_three_of_fullRevolution (ω := ω) hfin hturn) hnp hint hIntConn











theorem acc_unitCell_faceInj :
    Set.InjOn (fun k => dartFace ((dartNext unitCell)^[k] ucBase.1))
      (Set.Iio (dartOrbitPeriod unitCell ucBase)) := by
  rw [unitCell_orbitPeriod_eq_four, show ucBase.1 = ucDart0 from rfl]
  exact unitCell_orbitFace_injOn


theorem acc_unitCell_faceLoop_isCycle : (mpl_orbitFaceLoop unitCell ucBase).IsCycle :=
  mpl_orbitFaceLoop_isCycle unitCell ucBase (by rw [unitCell_orbitPeriod_eq_four]; norm_num)
    acc_unitCell_faceInj






theorem acc_unitCell_winds :
    (mpl_orbitFaceLoop unitCell ucBase).IsCycle ∧
      ¬ Even (jec_rayCount (origin 2) (mpl_orbitLoop unitCell ucBase)) := by
  refine ⟨acc_unitCell_faceLoop_isCycle, ?_⟩
  have horig : (origin 2) = (![0, 0] : Site 2) := by funext i; fin_cases i <;> rfl
  rw [horig, mpl_unitCell_rayCount_eq_one]
  decide





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
