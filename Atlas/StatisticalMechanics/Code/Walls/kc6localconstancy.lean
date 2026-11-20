/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.CrossingParity
import Code.Lattice.DartDef
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.MinimalPeriodLoop
import Code.Lattice.OrbitLoopBridge
import Code.Lattice.ExteriorConnected
import Code.Lattice.CornerBalance

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice











theorem kc6_loop_ray_wall_parity (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) :
    Even (jec_rayCount z Vc) ↔ Even (jec_wallCount z Vc) :=
  jec_loop_ray_wall_parity z Vc



























theorem kc6_localConstancy {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u ∉ Vc.support) (hv : v ∉ Vc.support) :
    (Even (jec_rayCount u Vc) ↔ Even (jec_rayCount v Vc)) := by
  
  have hadj' := hadj
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj'
  by_cases hc0 : u 0 = v 0
  · 
    have hc1 : u 1 = v 1 + 1 ∨ v 1 = u 1 + 1 := by omega
    rcases hc1 with h | h
    · 
      have hwall : jec_wallCount u Vc = jec_wallCount v Vc :=
        jec_wallCount_verticalStep v u (by omega) (by omega) Vc hv
      rw [kc6_loop_ray_wall_parity u Vc, kc6_loop_ray_wall_parity v Vc, hwall]
    · 
      have hwall : jec_wallCount v Vc = jec_wallCount u Vc :=
        jec_wallCount_verticalStep u v (by omega) (by omega) Vc hu
      rw [kc6_loop_ray_wall_parity u Vc, kc6_loop_ray_wall_parity v Vc, hwall]
  · 
    have hc0' : u 0 = v 0 + 1 ∨ v 0 = u 0 + 1 := by omega
    rcases hc0' with h | h
    · have hray : jec_rayCount u Vc = jec_rayCount v Vc :=
        jec_rayCount_horizontalStep v u (by omega) (by omega) Vc hv
      rw [hray]
    · have hray : jec_rayCount v Vc = jec_rayCount u Vc :=
        jec_rayCount_horizontalStep u v (by omega) (by omega) Vc hu
      rw [hray]



theorem kc6_localConstancy_mod {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u ∉ Vc.support) (hv : v ∉ Vc.support) :
    jec_rayCount u Vc % 2 = jec_rayCount v Vc % 2 := by
  have h := kc6_localConstancy Vc hadj hu hv
  rw [Nat.even_iff, Nat.even_iff] at h
  rcases Nat.mod_two_eq_zero_or_one (jec_rayCount u Vc) with hu0 | hu1
  · rw [hu0, (h.mp hu0).symm]
  · rcases Nat.mod_two_eq_zero_or_one (jec_rayCount v Vc) with hv0 | hv1
    · exact absurd (h.mpr hv0) (by rw [hu1]; decide)
    · rw [hu1, hv1]





theorem kc6_memLeftRegion_iff {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u ∉ Vc.support) (hv : v ∉ Vc.support) :
    u ∈ jec_leftRegion Vc ↔ v ∈ jec_leftRegion Vc := by
  simp only [jec_mem_leftRegion]
  rw [not_iff_not]
  exact kc6_localConstancy Vc hadj hu hv











theorem kc6_parityFlip_imp_onContour {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hflip : ¬ (Even (jec_rayCount u Vc) ↔ Even (jec_rayCount v Vc))) :
    u ∈ Vc.support ∨ v ∈ Vc.support := by
  by_contra hcon
  push Not at hcon
  exact hflip (kc6_localConstancy Vc hadj hcon.1 hcon.2)















theorem kc6_leftRegion_bdEdge_onSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (jec_leftRegion Vc) s(u, v)) :
    u ∈ Vc.support ∨ v ∈ Vc.support := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hu, hv⟩ := hcon
  rw [bdEdge_mk] at hbd
  simp only [jec_mem_leftRegion] at hbd
  
  have hpar := kc6_localConstancy Vc hadj hu hv
  tauto




theorem kc6_leftRegion_bdEdge_onSupport_eq_jec {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (jec_leftRegion Vc) s(u, v)) :
    u ∈ Vc.support ∨ v ∈ Vc.support :=
  jec_leftRegion_bdEdge_support Vc hadj hbd













theorem kc6_mpl_localConstancy (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u ∉ (mpl_orbitLoop K a).support) (hv : v ∉ (mpl_orbitLoop K a).support) :
    (Even (jec_rayCount u (mpl_orbitLoop K a)) ↔ Even (jec_rayCount v (mpl_orbitLoop K a))) :=
  kc6_localConstancy (mpl_orbitLoop K a) hadj hu hv



theorem kc6_mpl_memLeftRegion_iff (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u ∉ (mpl_orbitLoop K a).support) (hv : v ∉ (mpl_orbitLoop K a).support) :
    u ∈ jec_leftRegion (mpl_orbitLoop K a) ↔ v ∈ jec_leftRegion (mpl_orbitLoop K a) :=
  kc6_memLeftRegion_iff (mpl_orbitLoop K a) hadj hu hv





theorem kc6_mpl_leftRegion_bdEdge_onSupport (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) {u v : Site 2}
    (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (jec_leftRegion (mpl_orbitLoop K a)) s(u, v)) :
    u ∈ (mpl_orbitLoop K a).support ∨ v ∈ (mpl_orbitLoop K a).support :=
  kc6_leftRegion_bdEdge_onSupport (mpl_orbitLoop K a) hadj hbd





theorem kc6_olb_localConstancy (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u ∉ (olb_orbitLoop K hK e he).support)
    (hv : v ∉ (olb_orbitLoop K hK e he).support) :
    (Even (jec_rayCount u (olb_orbitLoop K hK e he)) ↔
      Even (jec_rayCount v (olb_orbitLoop K hK e he))) :=
  kc6_localConstancy (olb_orbitLoop K hK e he) hadj hu hv




theorem kc6_olb_leftRegion_bdEdge_onSupport (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (jec_leftRegion (olb_orbitLoop K hK e he)) s(u, v)) :
    u ∈ (olb_orbitLoop K hK e he).support ∨ v ∈ (olb_orbitLoop K hK e he).support :=
  kc6_leftRegion_bdEdge_onSupport (olb_orbitLoop K hK e he) hadj hbd


















theorem kc6_localConstancy_node :
    
    (∀ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a) (u v : Site 2),
        (hypercubicLattice 2).Adj u v → u ∉ Vc.support → v ∉ Vc.support →
        (Even (jec_rayCount u Vc) ↔ Even (jec_rayCount v Vc)))
    ∧ (∀ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a) (u v : Site 2),
        (hypercubicLattice 2).Adj u v → bdEdge (jec_leftRegion Vc) s(u, v) →
        u ∈ Vc.support ∨ v ∈ Vc.support)
    
    ∧ (∀ (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) (u v : Site 2),
        (hypercubicLattice 2).Adj u v →
        u ∉ (mpl_orbitLoop K a).support → v ∉ (mpl_orbitLoop K a).support →
        (Even (jec_rayCount u (mpl_orbitLoop K a)) ↔ Even (jec_rayCount v (mpl_orbitLoop K a))))
    ∧ (∀ (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) (u v : Site 2),
        (hypercubicLattice 2).Adj u v → bdEdge (jec_leftRegion (mpl_orbitLoop K a)) s(u, v) →
        u ∈ (mpl_orbitLoop K a).support ∨ v ∈ (mpl_orbitLoop K a).support)
    
    ∧ (∀ (K : Set (Site 2)) (hK : K.Finite) (e : Dart) (he : IsBoundaryDart K e) (u v : Site 2),
        (hypercubicLattice 2).Adj u v →
        u ∉ (olb_orbitLoop K hK e he).support → v ∉ (olb_orbitLoop K hK e he).support →
        (Even (jec_rayCount u (olb_orbitLoop K hK e he)) ↔
          Even (jec_rayCount v (olb_orbitLoop K hK e he))))
    ∧ (∀ (K : Set (Site 2)) (hK : K.Finite) (e : Dart) (he : IsBoundaryDart K e) (u v : Site 2),
        (hypercubicLattice 2).Adj u v →
        bdEdge (jec_leftRegion (olb_orbitLoop K hK e he)) s(u, v) →
        u ∈ (olb_orbitLoop K hK e he).support ∨ v ∈ (olb_orbitLoop K hK e he).support) :=
  ⟨fun _ Vc _ _ hadj hu hv => kc6_localConstancy Vc hadj hu hv,
   fun _ Vc _ _ hadj hbd => kc6_leftRegion_bdEdge_onSupport Vc hadj hbd,
   fun K a _ _ hadj hu hv => kc6_mpl_localConstancy K a hadj hu hv,
   fun K a _ _ hadj hbd => kc6_mpl_leftRegion_bdEdge_onSupport K a hadj hbd,
   fun K hK e he _ _ hadj hu hv => kc6_olb_localConstancy K hK e he hadj hu hv,
   fun K hK e he _ _ hadj hbd => kc6_olb_leftRegion_bdEdge_onSupport K hK e he hadj hbd⟩















theorem kc6_unitCell_offSupport_localConstancy :
    ∃ (R : ℕ) (u v : Site 2),
      ({z | z ∈ (mpl_orbitLoop unitCell ucBase).support} : Set (Site 2)) ⊆ box 2 R ∧
      (hypercubicLattice 2).Adj u v ∧
      u ∉ (mpl_orbitLoop unitCell ucBase).support ∧
      v ∉ (mpl_orbitLoop unitCell ucBase).support ∧
      (Even (jec_rayCount u (mpl_orbitLoop unitCell ucBase)) ↔
        Even (jec_rayCount v (mpl_orbitLoop unitCell ucBase))) := by
  obtain ⟨R, hR⟩ := exc_exists_loopSupportBox unitCell ucBase
  set F : Set (Site 2) := {z | z ∈ (mpl_orbitLoop unitCell ucBase).support} with hF
  have hxext : (![(R : ℤ) + 1, 0] : Site 2) ∈ exterior 2 R := ⟨0, by
    simp only [Matrix.cons_val_zero]; omega⟩
  have hyext : (![(R : ℤ) + 2, 0] : Site 2) ∈ exterior 2 R := ⟨0, by
    simp only [Matrix.cons_val_zero]; omega⟩
  have hxoff : (![(R : ℤ) + 1, 0] : Site 2) ∉ (mpl_orbitLoop unitCell ucBase).support :=
    exterior_subset_compl F R hR hxext
  have hyoff : (![(R : ℤ) + 2, 0] : Site 2) ∉ (mpl_orbitLoop unitCell ucBase).support :=
    exterior_subset_compl F R hR hyext
  have hadj : (hypercubicLattice 2).Adj (![(R : ℤ) + 1, 0] : Site 2) ![(R : ℤ) + 2, 0] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  exact ⟨R, ![(R : ℤ) + 1, 0], ![(R : ℤ) + 2, 0], hR, hadj, hxoff, hyoff,
    kc6_mpl_localConstancy unitCell ucBase hadj hxoff hyoff⟩




























end Walls

end StatMech
