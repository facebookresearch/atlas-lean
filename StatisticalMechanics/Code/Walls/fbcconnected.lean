/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























































import Mathlib
import Code.Lattice.JordanEnclosure
import Code.Lattice.PeierlsSingleCircuit
import Code.Lattice.PeierlsBoundaryConnected
import Code.Walls.pc2boundaryconn

open Finset Set SimpleGraph

namespace StatMech

namespace Walls

open StatMech.Lattice
open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable










theorem fbc_connected_of_common_reach {K : Set (Site 2)} {T : Finset (Site 2)}
    {a₀ : Site 2} (ha₀ : a₀ ∈ T)
    (hwalk : ∀ f ∈ T, ∃ p : (faceBoundaryGraph K).Walk a₀ f, ∀ v ∈ p.support, v ∈ T) :
    FaceBoundaryConnected K T :=
  pc2_faceBoundaryConnected_of_anchor ha₀ hwalk




theorem fbc_connected_of_pairwise_reach {K : Set (Site 2)} {T : Finset (Site 2)}
    (hne : T.Nonempty)
    (hwalk : ∀ f ∈ T, ∀ g ∈ T, ∃ p : (faceBoundaryGraph K).Walk f g,
        ∀ v ∈ p.support, v ∈ T) :
    FaceBoundaryConnected K T :=
  faceBoundaryConnected_of_walks hne hwalk
















theorem fbc_walk_support_in_boundarySupport {K : Set (Site 2)} (hK : K.Finite)
    {f g : Site 2} (p : (faceBoundaryGraph K).Walk f g)
    (hf : f ∈ (boundarySupport hK : Set (Site 2))) (hg : g ∈ (boundarySupport hK : Set (Site 2)))
    (v : Site 2) (hv : v ∈ p.support) : v ∈ boundarySupport hK := by
  
  induction p with
  | nil =>
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
    subst hv; exact hf
  | @cons a b c hab q ih =>
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · 
      exact hf
    · 
      have hbmem : b ∈ (boundarySupport hK : Set (Site 2)) :=
        boundarySupport_spec hK hab.symm.mem_support_left
      exact ih hbmem hg hv






theorem fbc_connected_of_reachable {K : Set (Site 2)} (hK : K.Finite)
    (hne : (boundarySupport hK).Nonempty)
    (hreach : ∀ f ∈ (boundarySupport hK : Set (Site 2)), ∀ g ∈ (boundarySupport hK : Set (Site 2)),
      (faceBoundaryGraph K).Reachable f g) :
    FaceBoundaryConnected K (boundarySupport hK) := by
  apply fbc_connected_of_pairwise_reach hne
  intro f hf g hg
  obtain ⟨p⟩ := hreach f (by exact_mod_cast hf) g (by exact_mod_cast hg)
  refine ⟨p, ?_⟩
  intro v hv
  have := fbc_walk_support_in_boundarySupport hK p (by exact_mod_cast hf) (by exact_mod_cast hg) v hv
  exact_mod_cast this























def fbc_BoundaryReachable (K : Set (Site 2)) : Prop :=
  ∀ f g : Site 2, f ∈ (faceBoundaryGraph K).support → g ∈ (faceBoundaryGraph K).support →
    (faceBoundaryGraph K).Reachable f g






def fbc_AttachStep : Prop :=
  ∀ (K : Finset (Site 2)) (c : Site 2), c ∉ K →
    IsConnectedCluster K → pc2_HoleFree (↑K : Set (Site 2)) →
    fbc_BoundaryReachable (↑K : Set (Site 2)) →
    IsConnectedCluster (insert c K) → pc2_HoleFree (↑(insert c K) : Set (Site 2)) →
    fbc_BoundaryReachable (↑(insert c K) : Set (Site 2))





def fbc_HasRemovableCell : Prop :=
  ∀ (K : Finset (Site 2)), 2 ≤ K.card → IsConnectedCluster K → pc2_HoleFree (↑K : Set (Site 2)) →
    ∃ c ∈ K, c ≠ origin 2 ∧ IsConnectedCluster (K.erase c) ∧
      pc2_HoleFree (↑(K.erase c) : Set (Site 2))











theorem fbc_boundaryReachable_of_faceBoundaryConnected {K : Set (Site 2)} {T : Finset (Site 2)}
    (hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2)))
    (hconn : FaceBoundaryConnected K T) :
    fbc_BoundaryReachable K := by
  intro f g hf hg
  have hfT : f ∈ (T : Set (Site 2)) := hsupp hf
  have hgT : g ∈ (T : Set (Site 2)) := hsupp hg
  
  have hr := (hconn.preconnected ⟨f, hfT⟩ ⟨g, hgT⟩)
  obtain ⟨p⟩ := hr
  
  refine ⟨(p.map (SimpleGraph.Embedding.induce (T : Set (Site 2))).toHom)⟩





theorem fbc_support_nonempty {K : Finset (Site 2)} (hne : K.Nonempty) :
    ((faceBoundaryGraph (↑K : Set (Site 2))).support).Nonempty := by
  classical
  
  obtain ⟨x, hxK, hxmax⟩ := K.exists_max_image (fun p => p 0) hne
  
  have hright : (![x 0 + 1, x 1] : Site 2) ∉ (↑K : Set (Site 2)) := by
    intro hmem
    rw [Finset.mem_coe] at hmem
    have := hxmax _ hmem
    simp only [Matrix.cons_val_zero] at this
    omega
  have hxeq : x = ![x 0, x 1] := by funext i; fin_cases i <;> rfl
  
  
  
  
  have hadj : (faceBoundaryGraph (↑K : Set (Site 2))).Adj ![x 0, x 1 - 1] ![x 0, x 1] := by
    rw [faceBoundaryGraph_adj]
    refine ⟨?_, ?_⟩
    · have := latAdj_top (x 0) (x 1 - 1); rwa [show x 1 - 1 + 1 = x 1 from by ring] at this
    · have h := sharedPrimalEdge_top (x 0) (x 1 - 1)
      rw [show x 1 - 1 + 1 = x 1 from by ring] at h
      rw [h]; unfold faceCorner01 faceCorner11
      rw [show x 1 - 1 + 1 = x 1 from by ring]
      
      rw [bdEdge_mk]
      constructor
      · intro _; exact hright
      · intro _; rw [Finset.mem_coe, ← hxeq]; exact hxK
  exact ⟨_, hadj.symm.mem_support_left⟩




























theorem fbc_faceBoundaryConnected_false_of_isolated {K : Set (Site 2)} {T : Finset (Site 2)}
    {w : Site 2} (hwT : w ∈ T) (hiso : w ∉ (faceBoundaryGraph K).support)
    {s : Site 2} (hsT : s ∈ T) (hs : s ∈ (faceBoundaryGraph K).support) (hws : w ≠ s) :
    ¬ FaceBoundaryConnected K T := by
  intro hconn
  
  
  
  have hr := hconn.preconnected ⟨w, by exact_mod_cast hwT⟩ ⟨s, by exact_mod_cast hsT⟩
  obtain ⟨p⟩ := hr
  cases p with
  | nil =>
    
    exact hws rfl
  | cons hab q =>
    
    exact hiso ((SimpleGraph.Embedding.induce (T : Set (Site 2))).toHom.map_adj hab).mem_support_left










theorem fbc_boundaryReachable_singleton :
    fbc_BoundaryReachable (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) :=
  fbc_boundaryReachable_of_faceBoundaryConnected support_singletonOrigin_subset
    singletonOrigin_faceBoundaryConnected



theorem fbc_card_one_eq_singleton {K : Finset (Site 2)} (hconn : IsConnectedCluster K)
    (hcard : K.card = 1) : K = {origin 2} := by
  obtain ⟨ho, _⟩ := hconn
  rw [Finset.card_eq_one] at hcard
  obtain ⟨a, ha⟩ := hcard
  rw [ha] at ho ⊢
  rw [Finset.mem_singleton] at ho
  rw [ho]







theorem fbc_boundaryReachable_of_inputs (hattach : fbc_AttachStep) (hrem : fbc_HasRemovableCell)
    (K : Finset (Site 2)) (hconn : IsConnectedCluster K) (hhf : pc2_HoleFree (↑K : Set (Site 2))) :
    fbc_BoundaryReachable (↑K : Set (Site 2)) := by
  
  induction hn : K.card using Nat.strong_induction_on generalizing K with
  | _ n ih =>
    subst hn
    
    have hne : K.Nonempty := ⟨origin 2, hconn.1⟩
    have hpos : 1 ≤ K.card := Finset.card_pos.mpr hne
    rcases Nat.lt_or_ge K.card 2 with h1 | h2
    · 
      have hc1 : K.card = 1 := by omega
      rw [fbc_card_one_eq_singleton hconn hc1]
      exact fbc_boundaryReachable_singleton
    · 
      obtain ⟨c, hcK, _hcorigin, hconn', hhf'⟩ := hrem K h2 hconn hhf
      
      have hcard' : (K.erase c).card < K.card := by
        rw [Finset.card_erase_of_mem hcK]; omega
      
      have hreach' : fbc_BoundaryReachable (↑(K.erase c) : Set (Site 2)) :=
        ih (K.erase c).card hcard' (K.erase c) hconn' hhf' rfl
      
      have hins : insert c (K.erase c) = K := Finset.insert_erase hcK
      have hcnotin : c ∉ K.erase c := Finset.notMem_erase c K
      have := hattach (K.erase c) c hcnotin hconn' hhf' hreach'
        (by rw [hins]; exact hconn) (by rw [hins]; exact hhf)
      rwa [hins] at this













def fbc_BoundaryConnResidue : Prop :=
  ∀ (K : Finset (Site 2)), IsConnectedCluster K → pc2_HoleFree (↑K : Set (Site 2)) →
    fbc_BoundaryReachable (↑K : Set (Site 2))


theorem fbc_residue_of_inputs (hattach : fbc_AttachStep) (hrem : fbc_HasRemovableCell) :
    fbc_BoundaryConnResidue :=
  fun K hconn hhf => fbc_boundaryReachable_of_inputs hattach hrem K hconn hhf




noncomputable def fbc_tightSupport {K : Set (Site 2)} (hK : K.Finite) : Finset (Site 2) :=
  (boundarySupport hK).filter (fun f => f ∈ (faceBoundaryGraph K).support)

theorem fbc_mem_tightSupport {K : Set (Site 2)} (hK : K.Finite) {f : Site 2} :
    f ∈ fbc_tightSupport hK ↔ f ∈ (faceBoundaryGraph K).support := by
  unfold fbc_tightSupport
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  exact boundarySupport_spec hK h

theorem fbc_tightSupport_covers {K : Set (Site 2)} (hK : K.Finite) :
    (faceBoundaryGraph K).support ⊆ (fbc_tightSupport hK : Set (Site 2)) := by
  intro f hf
  rw [Finset.mem_coe, fbc_mem_tightSupport]; exact hf






theorem fbc_faceBoundaryConnected_tight {K : Finset (Site 2)} (hne : K.Nonempty)
    (hfin : (↑K : Set (Site 2)).Finite)
    (hreach : fbc_BoundaryReachable (↑K : Set (Site 2))) :
    FaceBoundaryConnected (↑K : Set (Site 2)) (fbc_tightSupport hfin) := by
  obtain ⟨s, hs⟩ := fbc_support_nonempty hne
  apply fbc_connected_of_pairwise_reach ⟨s, (fbc_mem_tightSupport hfin).mpr hs⟩
  intro f hf g hg
  rw [fbc_mem_tightSupport] at hf hg
  obtain ⟨p⟩ := hreach f g hf hg
  refine ⟨p, ?_⟩
  
  clear hs s
  
  suffices hsuff : ∀ v ∈ p.support, v ∈ (faceBoundaryGraph (↑K : Set (Site 2))).support by
    intro v hv; rw [fbc_mem_tightSupport]; exact hsuff v hv
  induction p with
  | nil =>
    intro v hv
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv; subst hv; exact hf
  | @cons a b c hab q ih =>
    intro v hv
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact hf
    · exact ih hab.symm.mem_support_left hg v hv






theorem fbc_single_dualCircuit_of_residue (h : fbc_BoundaryConnResidue)
    (K : Finset (Site 2)) (hconn : IsConnectedCluster K)
    (hhf : pc2_HoleFree (↑K : Set (Site 2))) (hfin : (↑K : Set (Site 2)).Finite)
    {f₀ : Site 2} (hf₀ : f₀ ∈ (fbc_tightSupport hfin : Set (Site 2))) :
    ∃ c : (faceBoundaryGraph (↑K : Set (Site 2))).Walk f₀ f₀,
      c.IsTrail ∧ ∀ e ∈ (faceBoundaryGraph (↑K : Set (Site 2))).edgeSet, e ∈ c.edges := by
  have hne : K.Nonempty := ⟨origin 2, hconn.1⟩
  have hreach := h K hconn hhf
  exact faceBoundaryGraph_single_dualCircuit (fbc_tightSupport_covers hfin)
    (fbc_faceBoundaryConnected_tight hne hfin hreach) hf₀











theorem fbc_boundaryReachable_box (m n : ℕ) :
    fbc_BoundaryReachable (↑(boxCluster m n) : Set (Site 2)) :=
  fbc_boundaryReachable_of_faceBoundaryConnected (support_boxCluster_subset_frame m n)
    (pc2_box_faceBoundaryConnected m n)





theorem fbc_nonvacuous :
    fbc_BoundaryReachable (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) ∧
      ∀ m n : ℕ, fbc_BoundaryReachable (↑(boxCluster m n) : Set (Site 2)) :=
  ⟨fbc_boundaryReachable_singleton, fbc_boundaryReachable_box⟩








































end Walls

end StatMech
