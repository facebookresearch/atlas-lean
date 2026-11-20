/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































































import Mathlib
import Code.Lattice.EulerComponentCount
import Code.Lattice.InsideCoveringClose
import Code.Ising.PeierlsPlanarAssembly

open Set SimpleGraph Function


set_option linter.unusedSectionVars false

namespace StatMech

namespace Ising

open StatMech.Lattice


















variable {W : Type*} {G : SimpleGraph W}






theorem paa_reach_a_or_b {a b : W} {s x : W} (p : G.Walk s x)
    (h : (G.deleteEdges {s(a, b)}).Reachable a s ∨ (G.deleteEdges {s(a, b)}).Reachable b s) :
    ((G.deleteEdges {s(a, b)}).Reachable a x ∨ (G.deleteEdges {s(a, b)}).Reachable b x) := by
  classical
  induction p with
  | nil => exact h
  | @cons u v w huv q ih =>
    apply ih
    by_cases hed : s(u, v) = s(a, b)
    · rw [Sym2.eq_iff] at hed
      rcases hed with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · right; exact Reachable.refl _
      · left; exact Reachable.refl _
    · have hadj1 : (G.deleteEdges {s(a, b)}).Adj u v := by
        rw [deleteEdges_adj]; exact ⟨huv, by simpa using hed⟩
      rcases h with hu | hu
      · left; exact hu.trans hadj1.reachable
      · right; exact hu.trans hadj1.reachable





theorem paa_sup_edge_deleteEdges_eq {a b : W} (hnotin : s(a, b) ∉ G.edgeSet) :
    (G ⊔ edge a b).deleteEdges {s(a, b)} = G := by
  ext x y
  simp only [deleteEdges_adj, sup_adj, edge_adj, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h | ⟨hc, _⟩, hne2⟩
    · exact h
    · exact absurd (by rw [Sym2.eq_iff]; tauto) hne2
  · intro hxy
    refine ⟨Or.inl hxy, ?_⟩
    intro hc
    rw [Sym2.eq_iff] at hc
    apply hnotin
    rw [SimpleGraph.mem_edgeSet]
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hxy
    · exact hxy.symm

















theorem paa_two_components_count_sup {a b : W}
    (hnotin : s(a, b) ∉ G.edgeSet)
    (hconn : (G ⊔ edge a b).Connected)
    (hbridge : ¬ G.Reachable a b) :
    Nat.card G.ConnectedComponent = 2 := by
  classical
  have hGeq : G = (G ⊔ edge a b).deleteEdges {s(a, b)} := (paa_sup_edge_deleteEdges_eq hnotin).symm
  set G₁ := (G ⊔ edge a b).deleteEdges {s(a, b)} with hG1
  have hbridge' : ¬ G₁.Reachable a b := by rw [← hGeq]; exact hbridge
  let f : G₁.ConnectedComponent → Bool :=
    ConnectedComponent.lift (fun v => decide (G₁.Reachable a v)) (by
      intro u v p _
      have hreach : G₁.Reachable u v := ⟨p⟩
      simp only [decide_eq_decide]
      exact ⟨fun h => h.trans hreach, fun h => h.trans hreach.symm⟩)
  have hf_mk : ∀ v : W, f (G₁.connectedComponentMk v) = decide (G₁.Reachable a v) := fun _ => rfl
  have hevery : ∀ x : W, G₁.Reachable a x ∨ G₁.Reachable b x := by
    intro x
    obtain ⟨p⟩ := hconn.preconnected a x
    exact paa_reach_a_or_b p (Or.inl (Reachable.refl a))
  have hbij : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · refine ConnectedComponent.ind₂ ?_
      intro u v huv
      rw [hf_mk, hf_mk, decide_eq_decide] at huv
      rw [ConnectedComponent.eq]
      by_cases hau : G₁.Reachable a u
      · exact hau.symm.trans (huv.mp hau)
      · have hav : ¬ G₁.Reachable a v := fun h => hau (huv.mpr h)
        have hbu : G₁.Reachable b u := (hevery u).resolve_left hau
        have hbv : G₁.Reachable b v := (hevery v).resolve_left hav
        exact hbu.symm.trans hbv
    · intro c
      cases c with
      | true => exact ⟨G₁.connectedComponentMk a, by rw [hf_mk]; simp⟩
      | false => exact ⟨G₁.connectedComponentMk b, by rw [hf_mk]; simp [hbridge']⟩
  rw [hGeq, Nat.card_eq_of_bijective f hbij, Nat.card_eq_fintype_card, Fintype.card_bool]

















variable {V : Type*} [Finite V] [DecidableEq V]





def paa_ArcNoSeparation (A : SimpleGraph V) (B' : Set (Sym2 V)) : Prop :=
  (A.deleteEdges B').Connected






theorem paa_two_components_of_arcNoSeparation (A : SimpleGraph V) (B' : Set (Sym2 V)) {a b : V}
    (h1 : paa_ArcNoSeparation A B')
    (he : s(a, b) ∈ (A.deleteEdges B').edgeSet)
    (h2 : ¬ ((A.deleteEdges B').deleteEdges {s(a, b)}).Reachable a b) :
    Nat.card ((A.deleteEdges B').deleteEdges {s(a, b)}).ConnectedComponent = 2 :=
  ecc_two_components_tree_plus_bridge A B' h1 he h2








theorem paa_bridge_of_separation (A : SimpleGraph V) (B' : Set (Sym2 V)) {a b : V}
    (hsep : ¬ ((A.deleteEdges B').deleteEdges {s(a, b)}).Reachable a b) :
    ¬ ((A.deleteEdges B').deleteEdges {s(a, b)}).Reachable a b :=
  hsep






theorem paa_dualModel_of_arcNoSeparation (A : SimpleGraph V) (B' : Set (Sym2 V)) {a b : V}
    (h1 : paa_ArcNoSeparation A B')
    (he : s(a, b) ∈ (A.deleteEdges B').edgeSet)
    (hsep : ¬ ((A.deleteEdges B').deleteEdges {s(a, b)}).Reachable a b) :
    ecc_DualCutModel A B' a b :=
  ⟨h1, he, hsep⟩



theorem paa_two_components_of_dualModel (A : SimpleGraph V) (B' : Set (Sym2 V)) {a b : V}
    (h1 : paa_ArcNoSeparation A B')
    (he : s(a, b) ∈ (A.deleteEdges B').edgeSet)
    (hsep : ¬ ((A.deleteEdges B').deleteEdges {s(a, b)}).Reachable a b) :
    Nat.card ((A.deleteEdges B').deleteEdges {s(a, b)}).ConnectedComponent = 2 :=
  ecc_two_components_of_dualModel A B' (paa_dualModel_of_arcNoSeparation A B' h1 he hsep)


























def paa_ArcNoSeparationOff (Vc : (hypercubicLattice 2).Walk a a)
    (a' b' : {z : Site 2 // z ∉ Vc.support}) : Prop :=
  s(a', b') ∉ (icc_offComplGraph Vc).edgeSet ∧
    (icc_offComplGraph Vc ⊔ edge a' b').Connected












theorem paa_iccCount_of_arcNoSeparation (Vc : (hypercubicLattice 2).Walk a a)
    {a' b' : {z : Site 2 // z ∉ Vc.support}}
    (h1 : paa_ArcNoSeparationOff Vc a' b')
    (hsep : ¬ (icc_offComplGraph Vc).Reachable a' b') :
    Nat.card (icc_offComplGraph Vc).ConnectedComponent = 2 :=
  paa_two_components_count_sup h1.1 h1.2 hsep








theorem paa_separation_of_seeds (Vc : (hypercubicLattice 2).Walk a a)
    {a' b' : {z : Site 2 // z ∉ Vc.support}}
    (hInMem : (a' : Site 2) ∈ jec_leftRegion Vc) (hOutMem : (b' : Site 2) ∉ jec_leftRegion Vc) :
    ¬ (icc_offComplGraph Vc).Reachable a' b' := by
  intro hreach
  have hne : (icc_offComplGraph Vc).connectedComponentMk a' ≠
      (icc_offComplGraph Vc).connectedComponentMk b' :=
    icc_components_distinct Vc hInMem hOutMem
  exact hne (ConnectedComponent.eq.mpr hreach)




















theorem paa_covers_of_arcNoSeparation (Vc : (hypercubicLattice 2).Walk a a)
    {sIn sOut : Site 2} (hInOff : sIn ∉ Vc.support) (hOutOff : sOut ∉ Vc.support)
    (h1 : paa_ArcNoSeparationOff Vc ⟨sIn, hInOff⟩ ⟨sOut, hOutOff⟩)
    (hInMem : sIn ∈ jec_leftRegion Vc) (hOutMem : sOut ∉ jec_leftRegion Vc)
    (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support) :
    jec_leftRegion Vc ⊆ offSupportComponent Vc sIn :=
  icc_covers_of_two_components Vc
    (paa_iccCount_of_arcNoSeparation Vc h1 (paa_separation_of_seeds Vc hInMem hOutMem))
    hInMem hInOff hOutMem hOutOff hoffIn





theorem paa_hInOff_of_arcNoSeparation (Vc : (hypercubicLattice 2).Walk a a)
    {sIn sOut : Site 2} (hInOff : sIn ∉ Vc.support) (hOutOff : sOut ∉ Vc.support)
    (h1 : paa_ArcNoSeparationOff Vc ⟨sIn, hInOff⟩ ⟨sOut, hOutOff⟩)
    (hInMem : sIn ∈ jec_leftRegion Vc) (hOutMem : sOut ∉ jec_leftRegion Vc)
    (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support) :
    ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
      ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support :=
  icc_hInOff_of_two_components Vc
    (paa_iccCount_of_arcNoSeparation Vc h1 (paa_separation_of_seeds Vc hInMem hOutMem))
    hInMem hInOff hOutMem hOutOff hoffIn






















theorem paa_two_components_of_arcNoSeparation_jlri (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    {p q : Site 2} (hp : ¬ Even (jec_rayCount p Vc))
    (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
    {sIn sOut : Site 2} (hInOff : sIn ∉ Vc.support) (hOutOff : sOut ∉ Vc.support)
    (h1 : paa_ArcNoSeparationOff Vc ⟨sIn, hInOff⟩ ⟨sOut, hOutOff⟩)
    (hInMem : sIn ∈ jec_leftRegion Vc) (hOutMem : sOut ∉ jec_leftRegion Vc)
    (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
    (hOut : oc_OutsideReachesExterior Vc R) :
    Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 :=
  icc_two_components_of_count Vc R hsupp hp hq
    (paa_iccCount_of_arcNoSeparation Vc h1 (paa_separation_of_seeds Vc hInMem hOutMem))
    hInMem hInOff hOutMem hOutOff hoffIn hOut








theorem paa_peierls_long_range_order_of_planarConnectivity
    (hConn : ∀ n : ℕ, PlanarConnectivity n) :
    ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β →
      plusMeasure 2 n β 0 ≠ minusMeasure 2 n β 0 :=
  peierls_long_range_order_of_planarConnectivity hConn















theorem paa_count_nonvacuous_hyps :
    s((0 : Fin 2), 1) ∉ (⊥ : SimpleGraph (Fin 2)).edgeSet ∧
      ((⊥ : SimpleGraph (Fin 2)) ⊔ edge 0 1).Connected ∧
      ¬ (⊥ : SimpleGraph (Fin 2)).Reachable 0 1 := by
  refine ⟨by decide, ?_, by decide⟩
  rw [connected_iff_exists_forall_reachable]
  refine ⟨0, fun v => ?_⟩
  fin_cases v
  · exact Reachable.refl _
  · refine Adj.reachable ?_
    rw [sup_adj]; right; rw [edge_adj]; exact ⟨Or.inl ⟨rfl, rfl⟩, by decide⟩







theorem paa_count_nonvacuous :
    Nat.card (⊥ : SimpleGraph (Fin 2)).ConnectedComponent = 2 := by
  obtain ⟨hnotin, hconn, hbridge⟩ := paa_count_nonvacuous_hyps
  exact paa_two_components_count_sup hnotin hconn hbridge

end Ising

end StatMech
