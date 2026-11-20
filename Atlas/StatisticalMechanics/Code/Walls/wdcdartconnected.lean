/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































import Mathlib
import Code.Walls.wotsorbitsurj

open SimpleGraph Function

namespace StatMech

namespace Wots

open StatMech.Lattice





def wdc_boundaryLayer (K : Set (Site 2)) : Set (Site 2) :=
  {v | v ∉ K ∧ ∃ s : Site 2, (hypercubicLattice 2).Adj s v ∧ s ∈ K}


theorem wdc_layer_not_mem {K : Set (Site 2)} {v : Site 2} (hv : v ∈ wdc_boundaryLayer K) :
    v ∉ K := hv.1


theorem wdc_head_mem_layer (K : Set (Site 2)) (d : {e : Dart // IsBoundaryDart K e}) :
    d.1.head ∈ wdc_boundaryLayer K :=
  ⟨d.2.2, d.1.tail, d.1.adj, d.2.1⟩


theorem wdc_layer_isHead (K : Set (Site 2)) {v : Site 2} (hv : v ∈ wdc_boundaryLayer K) :
    ∃ d : {e : Dart // IsBoundaryDart K e}, d.1.head = v := by
  obtain ⟨hvK, s, hadj, hsK⟩ := hv
  exact ⟨⟨⟨s, v, hadj⟩, hsK, hvK⟩, rfl⟩






def wdc_layerGraph (K : Set (Site 2)) : SimpleGraph {v : Site 2 // v ∈ wdc_boundaryLayer K} where
  Adj a b := KingAdj (a : Site 2) (b : Site 2) ∧
    ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Reachable
      ⟨a.1, a.2.1⟩ ⟨b.1, b.2.1⟩
  symm := by
    intro a b h
    exact ⟨h.1.symm, h.2.symm⟩
  loopless := ⟨fun a h => h.1.1 rfl⟩

theorem wdc_layerGraph_adj (K : Set (Site 2)) (a b : {v : Site 2 // v ∈ wdc_boundaryLayer K}) :
    (wdc_layerGraph K).Adj a b ↔
      KingAdj (a : Site 2) (b : Site 2) ∧
      ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Reachable
        ⟨a.1, a.2.1⟩ ⟨b.1, b.2.1⟩ := Iff.rfl





theorem wdc_wots_adj_of_kingAdj_heads (K : Set (Site 2))
    (d1 d2 : {e : Dart // IsBoundaryDart K e})
    (hk : KingAdj d1.1.head d2.1.head)
    (hr : ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Reachable
      ⟨d1.1.head, d1.2.2⟩ ⟨d2.1.head, d2.2.2⟩) :
    (wots_dartGraph K).Adj d1 d2 := by
  refine ⟨?_, Or.inl hk, hr⟩
  intro h
  exact hk.1 (by rw [h])



theorem wdc_wots_adj_of_eq_heads (K : Set (Site 2))
    (d1 d2 : {e : Dart // IsBoundaryDart K e})
    (hne : d1 ≠ d2) (heq : d1.1.head = d2.1.head) :
    (wots_dartGraph K).Adj d1 d2 := by
  refine ⟨hne, Or.inr heq, ?_⟩
  have : (⟨d1.1.head, d1.2.2⟩ : (Kᶜ : Set (Site 2))) = ⟨d2.1.head, d2.2.2⟩ := Subtype.ext heq
  rw [this]





noncomputable def wdc_pick (K : Set (Site 2)) (v : {x : Site 2 // x ∈ wdc_boundaryLayer K}) :
    {e : Dart // IsBoundaryDart K e} :=
  (wdc_layer_isHead K v.2).choose

@[simp] theorem wdc_pick_head (K : Set (Site 2)) (v : {x : Site 2 // x ∈ wdc_boundaryLayer K}) :
    (wdc_pick K v).1.head = v.1 :=
  (wdc_layer_isHead K v.2).choose_spec







theorem wdc_pick_reachable_of_layerReachable (K : Set (Site 2))
    {a b : {x : Site 2 // x ∈ wdc_boundaryLayer K}}
    (h : (wdc_layerGraph K).Reachable a b) :
    (wots_dartGraph K).Reachable (wdc_pick K a) (wdc_pick K b) := by
  obtain ⟨p⟩ := h
  suffices H : ∀ (u v : {x : Site 2 // x ∈ wdc_boundaryLayer K}), (wdc_layerGraph K).Walk u v →
      (wots_dartGraph K).Reachable (wdc_pick K u) (wdc_pick K v) from H a b p
  intro u v q
  induction q with
  | nil => exact Reachable.refl _
  | @cons u w v hadj q' ih =>
    refine Reachable.trans ?_ ih
    
    have hk : KingAdj (wdc_pick K u).1.head (wdc_pick K w).1.head := by
      rw [wdc_pick_head, wdc_pick_head]; exact hadj.1
    have hr : ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Reachable
        ⟨(wdc_pick K u).1.head, (wdc_pick K u).2.2⟩ ⟨(wdc_pick K w).1.head, (wdc_pick K w).2.2⟩ := by
      have e1 : (⟨(wdc_pick K u).1.head, (wdc_pick K u).2.2⟩ : (Kᶜ : Set (Site 2)))
          = ⟨u.1, u.2.1⟩ := Subtype.ext (wdc_pick_head K u)
      have e2 : (⟨(wdc_pick K w).1.head, (wdc_pick K w).2.2⟩ : (Kᶜ : Set (Site 2)))
          = ⟨w.1, w.2.1⟩ := Subtype.ext (wdc_pick_head K w)
      rw [e1, e2]; exact hadj.2
    exact (wdc_wots_adj_of_kingAdj_heads K _ _ hk hr).reachable












def wdc_LayerConnected (K : Set (Site 2)) : Prop :=
  ∀ a b : {x : Site 2 // x ∈ wdc_boundaryLayer K},
    ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Reachable ⟨a.1, a.2.1⟩ ⟨b.1, b.2.1⟩ →
    (wdc_layerGraph K).Reachable a b







theorem wdc_dartConnected_of_layerConnected (K : Set (Site 2))
    (h : wdc_LayerConnected K) : wots_DartConnected K := by
  intro d1 d2 hreach
  set a : {x : Site 2 // x ∈ wdc_boundaryLayer K} := ⟨d1.1.head, wdc_head_mem_layer K d1⟩ with ha
  set b : {x : Site 2 // x ∈ wdc_boundaryLayer K} := ⟨d2.1.head, wdc_head_mem_layer K d2⟩ with hb
  
  have g1 : (wots_dartGraph K).Reachable d1 (wdc_pick K a) := by
    by_cases hd : d1 = wdc_pick K a
    · rw [hd]
    · exact (wdc_wots_adj_of_eq_heads K d1 (wdc_pick K a) hd (by rw [wdc_pick_head])).reachable
  
  have g2 : (wots_dartGraph K).Reachable (wdc_pick K b) d2 := by
    by_cases hd : wdc_pick K b = d2
    · rw [hd]
    · exact (wdc_wots_adj_of_eq_heads K (wdc_pick K b) d2 hd (by rw [wdc_pick_head])).reachable
  
  have hlayer : (wdc_layerGraph K).Reachable a b := h a b hreach
  have hmid : (wots_dartGraph K).Reachable (wdc_pick K a) (wdc_pick K b) :=
    wdc_pick_reachable_of_layerReachable K hlayer
  exact (g1.trans hmid).trans g2











end Wots

end StatMech
