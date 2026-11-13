/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































import Mathlib
import Code.Walls.bc7nocrossing
import Code.Walls.bc8distinctcutclusters

open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation

namespace StatMech

namespace Walls

variable {d : ℕ}















theorem bc8_clusters_disjoint {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d}
    (h : ¬ Connected d (removeSite 0 ω) x y) :
    Disjoint (cluster d (removeSite 0 ω) x) (cluster d (removeSite 0 ω) y) := by
  rw [Set.disjoint_left]
  intro w hwx hwy
  rw [mem_cluster] at hwx hwy
  exact h (hwx.trans hwy.symm)



theorem bc8_connected_of_not_disjoint {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d}
    (h : ¬ Disjoint (cluster d (removeSite 0 ω) x) (cluster d (removeSite 0 ω) y)) :
    Connected d (removeSite 0 ω) x y := by
  rw [Set.not_disjoint_iff] at h
  obtain ⟨w, hwx, hwy⟩ := h
  rw [mem_cluster] at hwx hwy
  exact hwx.trans hwy.symm



theorem bc8_cut_disjoint_iff_disconnected {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d} :
    Disjoint (cluster d (removeSite 0 ω) x) (cluster d (removeSite 0 ω) y) ↔
      ¬ Connected d (removeSite 0 ω) x y :=
  ⟨fun hdisj hconn => (Set.disjoint_left.mp hdisj
      (self_mem_cluster _ x) (mem_cluster.mpr hconn.symm)),
   bc8_clusters_disjoint⟩




theorem bc8_cut_ne_iff_disconnected {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d} :
    cluster d (removeSite 0 ω) x ≠ cluster d (removeSite 0 ω) y ↔
      ¬ Connected d (removeSite 0 ω) x y := by
  constructor
  · intro hne hconn
    exact hne (cluster_eq_of_connected hconn)
  · intro hdis heq
    
    have hy : y ∈ cluster d (removeSite 0 ω) x := by
      rw [heq]; exact self_mem_cluster _ y
    exact hdis (mem_cluster.mp hy)



theorem bc8_cut_ne_iff_disjoint {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d} :
    cluster d (removeSite 0 ω) x ≠ cluster d (removeSite 0 ω) y ↔
      Disjoint (cluster d (removeSite 0 ω) x) (cluster d (removeSite 0 ω) y) :=
  bc8_cut_ne_iff_disconnected.trans bc8_cut_disjoint_iff_disconnected.symm



theorem bc8_disjoint_of_cut_ne {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d}
    (hne : cluster d (removeSite 0 ω) x ≠ cluster d (removeSite 0 ω) y) :
    Disjoint (cluster d (removeSite 0 ω) x) (cluster d (removeSite 0 ω) y) :=
  bc8_cut_ne_iff_disjoint.mp hne












theorem bc8_cut_no_crossing {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d}
    (hne : cluster d (removeSite 0 ω) x ≠ cluster d (removeSite 0 ω) y) :
    ∀ ⦃u : Site d⦄, u ∈ cluster d (removeSite 0 ω) x →
      ∀ ⦃v : Site d⦄, v ∈ cluster d (removeSite 0 ω) y →
        ¬ IsOpenEdge d (removeSite 0 ω) u v :=
  bc7_cut_no_crossing hne



theorem bc8_cut_no_crossing_of_disconnected {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d}
    (h : ¬ Connected d (removeSite 0 ω) x y) :
    ∀ ⦃u : Site d⦄, u ∈ cluster d (removeSite 0 ω) x →
      ∀ ⦃v : Site d⦄, v ∈ cluster d (removeSite 0 ω) y →
        ¬ IsOpenEdge d (removeSite 0 ω) u v :=
  bc8_cut_no_crossing (bc8_cut_ne_iff_disconnected.mpr h)
















def bc8_NoCrossing (ω : ConfigSpace (Sym2 (Site d))) (x y : Site d) : Prop :=
  (cluster d (removeSite 0 ω) x ≠ cluster d (removeSite 0 ω) y ↔
      ¬ Connected d (removeSite 0 ω) x y) ∧
    (Disjoint (cluster d (removeSite 0 ω) x) (cluster d (removeSite 0 ω) y) ↔
      ¬ Connected d (removeSite 0 ω) x y) ∧
    (cluster d (removeSite 0 ω) x ≠ cluster d (removeSite 0 ω) y →
      ∀ ⦃u : Site d⦄, u ∈ cluster d (removeSite 0 ω) x →
        ∀ ⦃v : Site d⦄, v ∈ cluster d (removeSite 0 ω) y →
          ¬ IsOpenEdge d (removeSite 0 ω) u v)







theorem bc8_noCrossing (ω : ConfigSpace (Sym2 (Site d))) (x y : Site d) :
    bc8_NoCrossing ω x y :=
  ⟨bc8_cut_ne_iff_disconnected, bc8_cut_disjoint_iff_disconnected, bc8_cut_no_crossing⟩
















theorem bc8_threeArms_pairwiseDisjoint (n : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    (hω : ω ∈ threeMeetBox d n) :
    ∃ x₁' x₂' x₃' : Site d,
      (cluster d (removeSite 0 ω) x₁').Infinite ∧
      (cluster d (removeSite 0 ω) x₂').Infinite ∧
      (cluster d (removeSite 0 ω) x₃').Infinite ∧
      Disjoint (cluster d (removeSite 0 ω) x₁') (cluster d (removeSite 0 ω) x₂') ∧
      Disjoint (cluster d (removeSite 0 ω) x₁') (cluster d (removeSite 0 ω) x₃') ∧
      Disjoint (cluster d (removeSite 0 ω) x₂') (cluster d (removeSite 0 ω) x₃') ∧
      (∀ ⦃u : Site d⦄, u ∈ cluster d (removeSite 0 ω) x₁' →
        ∀ ⦃v : Site d⦄, v ∈ cluster d (removeSite 0 ω) x₂' →
          ¬ IsOpenEdge d (removeSite 0 ω) u v) ∧
      (∀ ⦃u : Site d⦄, u ∈ cluster d (removeSite 0 ω) x₁' →
        ∀ ⦃v : Site d⦄, v ∈ cluster d (removeSite 0 ω) x₃' →
          ¬ IsOpenEdge d (removeSite 0 ω) u v) ∧
      (∀ ⦃u : Site d⦄, u ∈ cluster d (removeSite 0 ω) x₂' →
        ∀ ⦃v : Site d⦄, v ∈ cluster d (removeSite 0 ω) x₃' →
          ¬ IsOpenEdge d (removeSite 0 ω) u v) := by
  obtain ⟨x₁', x₂', x₃', hinf₁, hinf₂, hinf₃, hd12, hd13, hd23⟩ :=
    bc8_threeArmClusters_distinct n ω hω
  exact ⟨x₁', x₂', x₃', hinf₁, hinf₂, hinf₃,
    bc8_disjoint_of_cut_ne hd12, bc8_disjoint_of_cut_ne hd13, bc8_disjoint_of_cut_ne hd23,
    bc8_cut_no_crossing hd12, bc8_cut_no_crossing hd13, bc8_cut_no_crossing hd23⟩







theorem bc8_threeArms_noCrossing (n : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    (hω : ω ∈ threeMeetBox d n) :
    ∃ x₁' x₂' x₃' : Site d,
      (cluster d (removeSite 0 ω) x₁').Infinite ∧
      (cluster d (removeSite 0 ω) x₂').Infinite ∧
      (cluster d (removeSite 0 ω) x₃').Infinite ∧
      bc8_NoCrossing ω x₁' x₂' ∧ bc8_NoCrossing ω x₁' x₃' ∧ bc8_NoCrossing ω x₂' x₃' := by
  obtain ⟨x₁', x₂', x₃', hinf₁, hinf₂, hinf₃, _hd12, _hd13, _hd23⟩ :=
    bc8_threeArmClusters_distinct n ω hω
  exact ⟨x₁', x₂', x₃', hinf₁, hinf₂, hinf₃,
    bc8_noCrossing ω x₁' x₂', bc8_noCrossing ω x₁' x₃', bc8_noCrossing ω x₂' x₃'⟩





section AxiomAudit


#guard_msgs in
#print axioms bc8_noCrossing


#guard_msgs in
#print axioms bc8_threeArms_pairwiseDisjoint


#guard_msgs in
#print axioms bc8_threeArms_noCrossing

end AxiomAudit

end Walls

end StatMech
