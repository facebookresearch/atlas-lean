/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.CrossingParity
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.MinimalPeriodLoop
import Code.Lattice.OutsideConnected
import Code.Lattice.UniqueInfiniteComponent
import Code.Lattice.ExteriorConnected

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice

















theorem kc4_localConstancy {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u ∉ Vc.support) (hv : v ∉ Vc.support) :
    (Even (jec_rayCount u Vc) ↔ Even (jec_rayCount v Vc)) :=
  jec_localConstancy Vc hadj hu hv



theorem kc4_localConstancy_mod {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u ∉ Vc.support) (hv : v ∉ Vc.support) :
    jec_rayCount u Vc % 2 = jec_rayCount v Vc % 2 := by
  have h := kc4_localConstancy Vc hadj hu hv
  rw [Nat.even_iff, Nat.even_iff] at h
  rcases Nat.mod_two_eq_zero_or_one (jec_rayCount u Vc) with hu0 | hu1
  · rw [hu0, (h.mp hu0).symm]
  · rcases Nat.mod_two_eq_zero_or_one (jec_rayCount v Vc) with hv0 | hv1
    · exact absurd (h.mpr hv0) (by rw [hu1]; decide)
    · rw [hu1, hv1]





theorem kc4_memLeftRegion_iff {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u ∉ Vc.support) (hv : v ∉ Vc.support) :
    u ∈ jec_leftRegion Vc ↔ v ∈ jec_leftRegion Vc := by
  simp only [jec_mem_leftRegion]
  rw [not_iff_not]
  exact kc4_localConstancy Vc hadj hu hv













theorem kc4_parityFlip_imp_onContour {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hflip : ¬ (Even (jec_rayCount u Vc) ↔ Even (jec_rayCount v Vc))) :
    u ∈ Vc.support ∨ v ∈ Vc.support := by
  by_contra hcon
  push Not at hcon
  exact hflip (kc4_localConstancy Vc hadj hcon.1 hcon.2)





theorem kc4_offContour_pair_noFlip {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v) :
    (u ∈ Vc.support ∨ v ∈ Vc.support) ∨
      (Even (jec_rayCount u Vc) ↔ Even (jec_rayCount v Vc)) := by
  by_cases hu : u ∈ Vc.support
  · exact Or.inl (Or.inl hu)
  · by_cases hv : v ∈ Vc.support
    · exact Or.inl (Or.inr hv)
    · exact Or.inr (kc4_localConstancy Vc hadj hu hv)






theorem kc4_leftRegion_bdEdge_onContour {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (jec_leftRegion Vc) s(u, v)) :
    u ∈ Vc.support ∨ v ∈ Vc.support :=
  jec_leftRegion_bdEdge_support Vc hadj hbd












theorem kc4_orbitLoop_localConstancy (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) {u v : Site 2}
    (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u ∉ (mpl_orbitLoop K a).support) (hv : v ∉ (mpl_orbitLoop K a).support) :
    (Even (jec_rayCount u (mpl_orbitLoop K a)) ↔ Even (jec_rayCount v (mpl_orbitLoop K a))) :=
  kc4_localConstancy (mpl_orbitLoop K a) hadj hu hv



theorem kc4_orbitLoop_localConstancy_mod (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) {u v : Site 2}
    (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u ∉ (mpl_orbitLoop K a).support) (hv : v ∉ (mpl_orbitLoop K a).support) :
    jec_rayCount u (mpl_orbitLoop K a) % 2 = jec_rayCount v (mpl_orbitLoop K a) % 2 :=
  kc4_localConstancy_mod (mpl_orbitLoop K a) hadj hu hv



theorem kc4_orbitLoop_memLeftRegion_iff (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) {u v : Site 2}
    (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u ∉ (mpl_orbitLoop K a).support) (hv : v ∉ (mpl_orbitLoop K a).support) :
    u ∈ jec_leftRegion (mpl_orbitLoop K a) ↔ v ∈ jec_leftRegion (mpl_orbitLoop K a) :=
  kc4_memLeftRegion_iff (mpl_orbitLoop K a) hadj hu hv




theorem kc4_orbitLoop_parityFlip_imp_onContour (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) {u v : Site 2}
    (hadj : (hypercubicLattice 2).Adj u v)
    (hflip : ¬ (Even (jec_rayCount u (mpl_orbitLoop K a)) ↔
      Even (jec_rayCount v (mpl_orbitLoop K a)))) :
    u ∈ (mpl_orbitLoop K a).support ∨ v ∈ (mpl_orbitLoop K a).support :=
  kc4_parityFlip_imp_onContour (mpl_orbitLoop K a) hadj hflip




theorem kc4_orbitLoop_leftRegion_bdEdge_onContour (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) {u v : Site 2}
    (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (jec_leftRegion (mpl_orbitLoop K a)) s(u, v)) :
    u ∈ (mpl_orbitLoop K a).support ∨ v ∈ (mpl_orbitLoop K a).support :=
  kc4_leftRegion_bdEdge_onContour (mpl_orbitLoop K a) hadj hbd




theorem kc4_supportSet_localConstancy (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) {u v : Site 2}
    (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u ∉ oc_supportSet (mpl_orbitLoop K a))
    (hv : v ∉ oc_supportSet (mpl_orbitLoop K a)) :
    (Even (jec_rayCount u (mpl_orbitLoop K a)) ↔ Even (jec_rayCount v (mpl_orbitLoop K a))) :=
  kc4_localConstancy (mpl_orbitLoop K a) hadj hu hv
















theorem kc4_localConstancy_node :
    
    (∀ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a) (u v : Site 2),
        (hypercubicLattice 2).Adj u v → u ∉ Vc.support → v ∉ Vc.support →
        (Even (jec_rayCount u Vc) ↔ Even (jec_rayCount v Vc)))
    ∧ (∀ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a) (u v : Site 2),
        (hypercubicLattice 2).Adj u v →
        ¬ (Even (jec_rayCount u Vc) ↔ Even (jec_rayCount v Vc)) →
        u ∈ Vc.support ∨ v ∈ Vc.support)
    
    ∧ (∀ (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) (u v : Site 2),
        (hypercubicLattice 2).Adj u v →
        u ∉ (mpl_orbitLoop K a).support → v ∉ (mpl_orbitLoop K a).support →
        (Even (jec_rayCount u (mpl_orbitLoop K a)) ↔ Even (jec_rayCount v (mpl_orbitLoop K a))))
    ∧ (∀ (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) (u v : Site 2),
        (hypercubicLattice 2).Adj u v →
        ¬ (Even (jec_rayCount u (mpl_orbitLoop K a)) ↔
            Even (jec_rayCount v (mpl_orbitLoop K a))) →
        u ∈ (mpl_orbitLoop K a).support ∨ v ∈ (mpl_orbitLoop K a).support) :=
  ⟨fun _ Vc _ _ hadj hu hv => kc4_localConstancy Vc hadj hu hv,
   fun _ Vc _ _ hadj hflip => kc4_parityFlip_imp_onContour Vc hadj hflip,
   fun K a _ _ hadj hu hv => kc4_orbitLoop_localConstancy K a hadj hu hv,
   fun K a _ _ hadj hflip => kc4_orbitLoop_parityFlip_imp_onContour K a hadj hflip⟩
















theorem kc4_unitCell_offContour_localConstancy :
    ∃ (R : ℕ) (u v : Site 2),
      ({z | z ∈ (mpl_orbitLoop unitCell ucBase).support} : Set (Site 2)) ⊆ box 2 R ∧
      (hypercubicLattice 2).Adj u v ∧
      u ∉ (mpl_orbitLoop unitCell ucBase).support ∧
      v ∉ (mpl_orbitLoop unitCell ucBase).support ∧
      (Even (jec_rayCount u (mpl_orbitLoop unitCell ucBase)) ↔
        Even (jec_rayCount v (mpl_orbitLoop unitCell ucBase))) := by
  obtain ⟨R, hR⟩ := exc_exists_loopSupportBox unitCell ucBase
  
  set F : Set (Site 2) := {z | z ∈ (mpl_orbitLoop unitCell ucBase).support} with hF
  
  refine ⟨R, ![(R : ℤ) + 1, 0], ![(R : ℤ) + 2, 0], hR, ?_, ?_, ?_, ?_⟩
  · 
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  · 
    have hext : (![(R : ℤ) + 1, 0] : Site 2) ∈ exterior 2 R := by
      refine ⟨0, ?_⟩
      simp only [Matrix.cons_val_zero]; omega
    have hcompl := exterior_subset_compl F R hR hext
    exact hcompl
  · 
    have hext : (![(R : ℤ) + 2, 0] : Site 2) ∈ exterior 2 R := by
      refine ⟨0, ?_⟩
      simp only [Matrix.cons_val_zero]; omega
    have hcompl := exterior_subset_compl F R hR hext
    exact hcompl
  · 
    have hu : (![(R : ℤ) + 1, 0] : Site 2) ∉ (mpl_orbitLoop unitCell ucBase).support := by
      have hext : (![(R : ℤ) + 1, 0] : Site 2) ∈ exterior 2 R := by
        refine ⟨0, ?_⟩
        simp only [Matrix.cons_val_zero]; omega
      exact exterior_subset_compl F R hR hext
    have hv : (![(R : ℤ) + 2, 0] : Site 2) ∉ (mpl_orbitLoop unitCell ucBase).support := by
      have hext : (![(R : ℤ) + 2, 0] : Site 2) ∈ exterior 2 R := by
        refine ⟨0, ?_⟩
        simp only [Matrix.cons_val_zero]; omega
      exact exterior_subset_compl F R hR hext
    have hadj : (hypercubicLattice 2).Adj (![(R : ℤ) + 1, 0] : Site 2) ![(R : ℤ) + 2, 0] := by
      simp [hypercubicLattice_adj, Fin.sum_univ_two]
    exact kc4_orbitLoop_localConstancy unitCell ucBase hadj hu hv

end Walls

end StatMech
