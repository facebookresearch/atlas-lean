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
import Code.Lattice.TurningNumber
import Code.Lattice.CornerBalance
import Code.Lattice.MinimalPeriodLoop
import Code.Lattice.Umlaufsatz
import Code.Lattice.UmlaufsatzSingleCycle
import Code.Lattice.OrbitExteriorEven
import Code.Lattice.JordanLeftRegionInterior
import Code.Lattice.EulerGeometricFaces
import Code.Lattice.EnclosedAreaWitness
import Code.Lattice.AnchoredCycleClose
import Code.Percolation.PcUpperUncond

open Finset Set SimpleGraph Function

namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}












theorem wwc2_odd_iff_mem_leftRegion {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (z : Site 2) :
    ¬ Even (jec_rayCount z Vc) ↔ z ∈ jec_leftRegion Vc := by
  rw [jec_mem_leftRegion]



theorem wwc2_odd_of_mem_leftRegion {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) {z : Site 2}
    (hz : z ∈ jec_leftRegion Vc) :
    ¬ Even (jec_rayCount z Vc) :=
  (wwc2_odd_iff_mem_leftRegion Vc z).mpr hz



theorem wwc2_far_not_mem_leftRegion {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {q : Site 2} (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1) :
    q ∉ jec_leftRegion Vc := by
  rw [jec_mem_leftRegion]; push Not
  exact jec_ray_even_far Vc q hq






theorem wwc2_even_of_connected_to_far {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z q : Site 2} (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
    (p : (hypercubicLattice 2).Walk z q) (hp : ∀ w ∈ p.support, w ∉ Vc.support) :
    Even (jec_rayCount z Vc) := by
  have hsame := jlri_sameRegion_along_offSupport_walk Vc p hp
  by_contra hodd
  have hzmem : z ∈ jec_leftRegion Vc := by rw [jec_mem_leftRegion]; exact hodd
  exact wwc2_far_not_mem_leftRegion Vc hq (hsame.mp hzmem)












theorem wwc2_cycle_enclosesCell {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hcyc : Vc.IsCycle) :
    ∃ z : Site 2, z ∈ jec_leftRegion Vc := by
  obtain ⟨z, hz⟩ := eaw_cycle_oddCell' Vc hcyc
  exact ⟨z, (wwc2_odd_iff_mem_leftRegion Vc z).mp hz⟩



theorem wwc2_leftRegion_nonempty {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hcyc : Vc.IsCycle) :
    (jec_leftRegion Vc).Nonempty :=
  wwc2_cycle_enclosesCell Vc hcyc





theorem wwc2_leftRegion_nonempty_finite {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hcyc : Vc.IsCycle) (R : ℕ) (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) :
    (jec_leftRegion Vc).Nonempty ∧ (jec_leftRegion Vc).Finite :=
  ⟨wwc2_leftRegion_nonempty Vc hcyc, egf_leftRegion_finite Vc R hsupp⟩











noncomputable def wwc2_exitLoop (hfin : (cluster 2 ω (origin 2)).Finite) :
    (hypercubicLattice 2).Walk
      (dartFace (acc_exitSub (ω := ω) hfin).1) (dartFace (acc_exitSub (ω := ω) hfin).1) :=
  mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)





def wwc2_OriginInside (ω : ConfigSpace (Sym2 (Site 2)))
    (hfin : (cluster 2 ω (origin 2)).Finite) : Prop :=
  origin 2 ∈ jec_leftRegion (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))




theorem wwc2_oddOrigin_of_originInside (hfin : (cluster 2 ω (origin 2)).Finite)
    (h : wwc2_OriginInside ω hfin) :
    ¬ Even (jec_rayCount (origin 2)
      (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))) :=
  wwc2_odd_of_mem_leftRegion _ h














theorem wwc2_exitDartWinds_of_turning_originInside (hfin : (cluster 2 ω (origin 2)).Finite)
    (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hinside : wwc2_OriginInside ω hfin) :
    acc_ExitDartWinds ω hfin := by
  refine ⟨?_, wwc2_oddOrigin_of_originInside (ω := ω) hfin hinside⟩
  have hp : 3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) :=
    acc_period_ge_three_of_fullRevolution (ω := ω) hfin hturn
  exact mpl_orbitFaceLoop_isCycle (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) hp
    (orbitFace_injOn_of_noPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) hnp)




theorem wwc2_exitDartWinds_of_cycle_originInside (hfin : (cluster 2 ω (origin 2)).Finite)
    (hp : 3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hinside : wwc2_OriginInside ω hfin) :
    acc_ExitDartWinds ω hfin := by
  refine ⟨?_, wwc2_oddOrigin_of_originInside (ω := ω) hfin hinside⟩
  exact mpl_orbitFaceLoop_isCycle (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) hp
    (orbitFace_injOn_of_noPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) hnp)



theorem wwc2_anchoredCycleExists_of_turning_originInside (hfin : (cluster 2 ω (origin 2)).Finite)
    (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hinside : wwc2_OriginInside ω hfin) :
    AnchoredCycleExists ω hfin :=
  acc_anchoredCycleExists_of_exitDartWinds (ω := ω) hfin
    (wwc2_exitDartWinds_of_turning_originInside (ω := ω) hfin hturn hnp hinside)






theorem wwc2_pc_lt_one_of_turning_originInside
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) ∧
          OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) ∧
          wwc2_OriginInside ω hfin) :
    StatMech.Percolation.pc 2 < 1 :=
  acc_pc_lt_one_of_exitDartWinds (fun ω hfin =>
    wwc2_exitDartWinds_of_turning_originInside (ω := ω) hfin (h ω hfin).1 (h ω hfin).2.1
      (h ω hfin).2.2)












theorem wwc2_unitCell_originInside :
    origin 2 ∈ jec_leftRegion (mpl_orbitLoop unitCell ucBase) := by
  rw [jec_mem_leftRegion]
  have horig : (origin 2) = (![0, 0] : Site 2) := by funext i; fin_cases i <;> rfl
  rw [horig, mpl_unitCell_rayCount_eq_one]
  decide




theorem wwc2_unitCell_oddOrigin :
    ¬ Even (jec_rayCount (origin 2) (mpl_orbitLoop unitCell ucBase)) :=
  wwc2_odd_of_mem_leftRegion (mpl_orbitLoop unitCell ucBase) wwc2_unitCell_originInside




theorem wwc2_unitCell_primalLoop_isCycle : (mpl_orbitLoop unitCell ucBase).IsCycle :=
  mpl_orbitLoop_isCycle unitCell ucBase (by rw [unitCell_orbitPeriod_eq_four]; norm_num)
    acc_unitCell_faceInj



theorem wwc2_unitCell_enclosesCell :
    (jec_leftRegion (mpl_orbitLoop unitCell ucBase)).Nonempty :=
  wwc2_leftRegion_nonempty (mpl_orbitLoop unitCell ucBase) wwc2_unitCell_primalLoop_isCycle

















theorem wwc2_exitLoop_isCycle_of_turning (hfin : (cluster 2 ω (origin 2)).Finite)
    (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)) :
    (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).IsCycle := by
  have hp : 3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) :=
    acc_period_ge_three_of_fullRevolution (ω := ω) hfin hturn
  exact mpl_orbitLoop_isCycle (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) hp
    (orbitFace_injOn_of_noPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) hnp)








theorem wwc2_turning_enclosesCell (hfin : (cluster 2 ω (origin 2)).Finite)
    (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)) :
    ∃ z₀ : Site 2,
      z₀ ∈ jec_leftRegion (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)) :=
  wwc2_cycle_enclosesCell _ (wwc2_exitLoop_isCycle_of_turning (ω := ω) hfin hturn hnp)



















theorem wwc2_originInside_of_reaches_enclosed (hfin : (cluster 2 ω (origin 2)).Finite)
    (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hreach : ∀ z₀ : Site 2,
      z₀ ∈ jec_leftRegion (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)) →
      ∃ p : (hypercubicLattice 2).Walk (origin 2) z₀,
        (∀ w ∈ p.support,
          w ∉ (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).support)) :
    wwc2_OriginInside ω hfin := by
  obtain ⟨z₀, hz₀⟩ := wwc2_turning_enclosesCell (ω := ω) hfin hturn hnp
  obtain ⟨p, hp⟩ := hreach z₀ hz₀
  
  have hodd0 : ¬ Even (jec_rayCount z₀
      (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))) :=
    (wwc2_odd_iff_mem_leftRegion _ z₀).mpr hz₀
  
  have hoddO : ¬ Even (jec_rayCount (origin 2)
      (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))) :=
    ooi_odd_of_connected_to_odd _ p hp hodd0
  exact (wwc2_odd_iff_mem_leftRegion _ (origin 2)).mp hoddO








theorem wwc2_exitDartWinds_of_turning_reaches (hfin : (cluster 2 ω (origin 2)).Finite)
    (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hreach : ∀ z₀ : Site 2,
      z₀ ∈ jec_leftRegion (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)) →
      ∃ p : (hypercubicLattice 2).Walk (origin 2) z₀,
        (∀ w ∈ p.support,
          w ∉ (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).support)) :
    acc_ExitDartWinds ω hfin :=
  wwc2_exitDartWinds_of_turning_originInside (ω := ω) hfin hturn hnp
    (wwc2_originInside_of_reaches_enclosed (ω := ω) hfin hturn hnp hreach)

















def wwc2_OriginReachesEnclosed (ω : ConfigSpace (Sym2 (Site 2)))
    (hfin : (cluster 2 ω (origin 2)).Finite) : Prop :=
  ∀ z₀ : Site 2,
    z₀ ∈ jec_leftRegion (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)) →
    ∃ p : (hypercubicLattice 2).Walk (origin 2) z₀,
      (∀ w ∈ p.support,
        w ∉ (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).support)




theorem wwc2_exitDartWinds_of_originReachesEnclosed (hfin : (cluster 2 ω (origin 2)).Finite)
    (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hreach : wwc2_OriginReachesEnclosed ω hfin) :
    acc_ExitDartWinds ω hfin :=
  wwc2_exitDartWinds_of_turning_reaches (ω := ω) hfin hturn hnp hreach


theorem wwc2_anchoredCycleExists_of_originReachesEnclosed (hfin : (cluster 2 ω (origin 2)).Finite)
    (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hreach : wwc2_OriginReachesEnclosed ω hfin) :
    AnchoredCycleExists ω hfin :=
  acc_anchoredCycleExists_of_exitDartWinds (ω := ω) hfin
    (wwc2_exitDartWinds_of_originReachesEnclosed (ω := ω) hfin hturn hnp hreach)







theorem wwc2_pc_lt_one_of_originReachesEnclosed
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) ∧
          OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) ∧
          wwc2_OriginReachesEnclosed ω hfin) :
    StatMech.Percolation.pc 2 < 1 :=
  acc_pc_lt_one_of_exitDartWinds (fun ω hfin =>
    wwc2_exitDartWinds_of_originReachesEnclosed (ω := ω) hfin (h ω hfin).1 (h ω hfin).2.1
      (h ω hfin).2.2)












theorem wwc2_origin_reaches_self_offSupport (hfin : (cluster 2 ω (origin 2)).Finite)
    (hO : origin 2 ∉ (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).support) :
    ∃ p : (hypercubicLattice 2).Walk (origin 2) (origin 2),
      (∀ w ∈ p.support,
        w ∉ (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).support) := by
  refine ⟨SimpleGraph.Walk.nil, ?_⟩
  intro w hw
  rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
  rw [hw]; exact hO






theorem wwc2_unitCell_originReachesEnclosed_witness :
    ∃ z₀ : Site 2, z₀ ∈ jec_leftRegion (mpl_orbitLoop unitCell ucBase) ∧
      ∃ p : (hypercubicLattice 2).Walk (origin 2) z₀,
        (∀ w ∈ p.support, w ∉ (mpl_orbitLoop unitCell ucBase).support) ∨ z₀ = origin 2 := by
  exact ⟨origin 2, wwc2_unitCell_originInside, SimpleGraph.Walk.nil, Or.inr rfl⟩







































































end Lattice

end StatMech
