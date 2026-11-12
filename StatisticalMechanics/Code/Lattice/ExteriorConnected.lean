/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.UniqueInfiniteComponent
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.MinimalPeriodLoop
import Code.Lattice.OrbitExteriorEven
import Code.Lattice.InteriorOrientation
import Code.Lattice.EnclosedAreaWitness

open Set SimpleGraph

namespace StatMech

namespace Lattice













theorem exc_unitCell_offK_on_support :
    (![0, -1] : Site 2) ∈ (mpl_orbitLoop unitCell ucBase).support := by
  rw [mpl_orbitLoop_support]
  have hedge : s((![0, 0] : Site 2), ![0, -1]) ∈ (mpl_orbitFaceLoop unitCell ucBase).edges := by
    rw [mpl_unitCell_faceLoop_edges]; simp
  exact (mpl_orbitFaceLoop unitCell ucBase).snd_mem_support_of_mem_edges hedge


theorem exc_unitCell_offK_notMem : (![0, -1] : Site 2) ∉ unitCell := by
  rw [unitCell, Set.mem_singleton_iff]
  intro hh
  have := congrFun hh 1
  simp at this







theorem exc_oldExteriorConnected_false : ¬ ior_ExteriorConnected unitCell ucBase := by
  intro h
  obtain ⟨z0, p, hp, _⟩ := h _ exc_unitCell_offK_notMem
  exact hp _ p.start_mem_support exc_unitCell_offK_on_support













theorem exc_reachable_compl_to_offSupport_walk (F : Set (Site 2)) {x y : Site 2}
    (hx : x ∈ Fᶜ) (hy : y ∈ Fᶜ)
    (h : ((hypercubicLattice 2).induce Fᶜ).Reachable ⟨x, hx⟩ ⟨y, hy⟩) :
    ∃ p : (hypercubicLattice 2).Walk x y, ∀ w ∈ p.support, w ∉ F := by
  obtain ⟨q⟩ := h
  refine ⟨q.map (SimpleGraph.Embedding.induce (G := hypercubicLattice 2) Fᶜ).toHom, ?_⟩
  intro w hw
  have hw2 : w ∈ List.map (⇑(SimpleGraph.Embedding.induce (G := hypercubicLattice 2) Fᶜ).toHom)
      q.support := by rwa [← SimpleGraph.Walk.support_map]
  obtain ⟨v, _, hvw⟩ := List.mem_map.mp hw2
  rw [← hvw]; exact v.2










theorem exc_farLeft_mem_exterior (R : ℕ) : (![-((R : ℤ) + 1), 0] : Site 2) ∈ exterior 2 R := by
  refine ⟨0, ?_⟩
  change R < ((-((R : ℤ) + 1))).natAbs
  rw [show (-((R : ℤ) + 1)).natAbs = R + 1 by rw [Int.natAbs_eq_iff]; right; push_cast; ring]
  omega






theorem exc_exterior_reaches_farLeft (F : Set (Site 2)) (R : ℕ) (hR : F ⊆ box 2 R)
    (z : Site 2) (hz : z ∈ exterior 2 R) :
    ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ F) ∧ (∀ q ∈ F, z0 0 ≤ q 0) := by
  set z0 : Site 2 := ![-((R : ℤ) + 1), 0] with hz0
  have hz0ext : z0 ∈ exterior 2 R := exc_farLeft_mem_exterior R
  have hsub : exterior 2 R ⊆ Fᶜ := exterior_subset_compl F R hR
  have hreach := box_exterior_connected R (by norm_num) z z0 hz hz0ext
  have hreachF : ((hypercubicLattice 2).induce Fᶜ).Reachable ⟨z, hsub hz⟩ ⟨z0, hsub hz0ext⟩ := by
    have := hreach.map ((hypercubicLattice 2).induceHomOfLE hsub).toHom
    simpa using this
  obtain ⟨p, hp⟩ := exc_reachable_compl_to_offSupport_walk F (hsub hz) (hsub hz0ext) hreachF
  refine ⟨z0, p, hp, ?_⟩
  intro qq hqq
  have hqbox := hR hqq
  rw [mem_box] at hqbox
  simp only [hz0, Matrix.cons_val_zero]
  have hnat : (qq 0).natAbs ≤ R := hqbox 0
  have h2 : |qq 0| ≤ (R : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hnat
  rw [abs_le] at h2; omega





theorem exc_loopSupport_finite (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)).Finite := by
  apply Set.Finite.subset (mpl_orbitLoop K a).support.toFinset.finite_toSet
  intro x hx; simpa using hx


theorem exc_exists_loopSupportBox (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    ∃ R : ℕ, ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R :=
  finite_subset_box _ (exc_loopSupport_finite K a)




















def exc_OffSupportReachesExterior (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    Prop :=
  ∃ R : ℕ, ∃ hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R,
    ∀ z, z ∉ K → z ∉ (mpl_orbitLoop K a).support →
      ∃ hz : z ∈ ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2))ᶜ,
        ∃ e : Site 2, ∃ he : e ∈ exterior 2 R,
          ((hypercubicLattice 2).induce
              ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2))ᶜ).Reachable
            ⟨z, hz⟩ ⟨e, exterior_subset_compl _ R hRbox he⟩





theorem exc_offSupport_of_reaches (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (h : exc_OffSupportReachesExterior K a) :
    ∀ z, z ∉ K → z ∉ (mpl_orbitLoop K a).support →
      ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
        (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧
        (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0) := by
  obtain ⟨R, hRbox, hreach⟩ := h
  intro z hzK hzsupp
  set F : Set (Site 2) := {z | z ∈ (mpl_orbitLoop K a).support} with hF
  obtain ⟨hz, e, he, hreach_ze⟩ := hreach z hzK hzsupp
  obtain ⟨p1, hp1⟩ := exc_reachable_compl_to_offSupport_walk F hz
    (exterior_subset_compl _ R hRbox he) hreach_ze
  obtain ⟨z0, p2, hp2, hfar⟩ := exc_exterior_reaches_farLeft F R hRbox e he
  refine ⟨z0, p1.append p2, ?_, ?_⟩
  · intro w hw
    rw [SimpleGraph.Walk.mem_support_append_iff] at hw
    rcases hw with h | h
    · exact hp1 w h
    · exact hp2 w h
  · exact hfar










def exc_SupportOddInK (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  ∀ z ∈ (mpl_orbitLoop K a).support, ¬ Even (jec_rayCount z (mpl_orbitLoop K a)) → z ∈ K
















theorem exc_interiorSubset_of_reaches_and_support (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hoff : exc_OffSupportReachesExterior K a)
    (hsupp : exc_SupportOddInK K a) :
    eaw_InteriorSubset K a := by
  intro z hodd
  by_cases hzsupp : z ∈ (mpl_orbitLoop K a).support
  · exact hsupp z hzsupp hodd
  · by_contra hzK
    obtain ⟨z0, p, hp, hfar⟩ := exc_offSupport_of_reaches K a hoff z hzK hzsupp
    have hbase : Even (jec_rayCount z0 (mpl_orbitLoop K a)) := by
      rw [jec_rayCount_eq_zero_of_right z0 (mpl_orbitLoop K a) (fun q hq => hfar q hq)]
      exact Nat.even_iff.mpr rfl
    exact hodd ((oee_rayParity_const_along_walk (mpl_orbitLoop K a) p hp).mpr hbase)















theorem exc_unitCell_supportOddInK : exc_SupportOddInK unitCell ucBase := by
  intro z _ hodd
  exact eaw_unitCell_interiorSubset z hodd





theorem exc_exterior_self_reachable (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (R : ℕ) (hR : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
    (z : Site 2) (hz : z ∈ exterior 2 R) :
    ((hypercubicLattice 2).induce
        ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2))ᶜ).Reachable
      ⟨z, exterior_subset_compl _ R hR hz⟩ ⟨z, exterior_subset_compl _ R hR hz⟩ :=
  SimpleGraph.Reachable.refl _

end Lattice

end StatMech
