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

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice













theorem jc10_loop_ray_wall_parity (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) :
    Even (jec_rayCount z Vc) ↔ Even (jec_wallCount z Vc) :=
  jec_loop_ray_wall_parity z Vc



























theorem jc10_localConstancy {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
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
      rw [jc10_loop_ray_wall_parity u Vc, jc10_loop_ray_wall_parity v Vc, hwall]
    · 
      have hwall : jec_wallCount v Vc = jec_wallCount u Vc :=
        jec_wallCount_verticalStep u v (by omega) (by omega) Vc hu
      rw [jc10_loop_ray_wall_parity u Vc, jc10_loop_ray_wall_parity v Vc, hwall]
  · 
    have hc0' : u 0 = v 0 + 1 ∨ v 0 = u 0 + 1 := by omega
    rcases hc0' with h | h
    · have hray : jec_rayCount u Vc = jec_rayCount v Vc :=
        jec_rayCount_horizontalStep v u (by omega) (by omega) Vc hv
      rw [hray]
    · have hray : jec_rayCount v Vc = jec_rayCount u Vc :=
        jec_rayCount_horizontalStep u v (by omega) (by omega) Vc hu
      rw [hray]





theorem jc10_localConstancy_eq_jec {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u ∉ Vc.support) (hv : v ∉ Vc.support) :
    (Even (jec_rayCount u Vc) ↔ Even (jec_rayCount v Vc)) :=
  jec_localConstancy Vc hadj hu hv











theorem jc10_leftRegion_bdEdge_support {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (jec_leftRegion Vc) s(u, v)) :
    u ∈ Vc.support ∨ v ∈ Vc.support := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hu, hv⟩ := hcon
  rw [bdEdge_mk] at hbd
  simp only [jec_mem_leftRegion] at hbd
  have hpar := jc10_localConstancy Vc hadj hu hv
  tauto













theorem jc10_mpl_localConstancy (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u ∉ (mpl_orbitLoop K a).support) (hv : v ∉ (mpl_orbitLoop K a).support) :
    (Even (jec_rayCount u (mpl_orbitLoop K a)) ↔ Even (jec_rayCount v (mpl_orbitLoop K a))) :=
  jc10_localConstancy (mpl_orbitLoop K a) hadj hu hv





theorem jc10_olb_localConstancy (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u ∉ (olb_orbitLoop K hK e he).support)
    (hv : v ∉ (olb_orbitLoop K hK e he).support) :
    (Even (jec_rayCount u (olb_orbitLoop K hK e he)) ↔
      Even (jec_rayCount v (olb_orbitLoop K hK e he))) :=
  jc10_localConstancy (olb_orbitLoop K hK e he) hadj hu hv
























end Walls

end StatMech
