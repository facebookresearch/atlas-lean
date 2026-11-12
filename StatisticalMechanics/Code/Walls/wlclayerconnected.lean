/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































import Mathlib
import Code.Walls.wdcdartconnected

open SimpleGraph Function

namespace StatMech

namespace Wots

open StatMech.Lattice





def wlc_layerCell (K : Set (Site 2)) (d : {e : Dart // IsBoundaryDart K e}) :
    {v : Site 2 // v ∈ wdc_boundaryLayer K} :=
  ⟨d.1.head, wdc_head_mem_layer K d⟩

@[simp] theorem wlc_layerCell_val (K : Set (Site 2)) (d : {e : Dart // IsBoundaryDart K e}) :
    (wlc_layerCell K d).1 = d.1.head := rfl









theorem wlc_layerReachable_step (K : Set (Site 2)) (d : {e : Dart // IsBoundaryDart K e}) :
    (wdc_layerGraph K).Reachable (wlc_layerCell K d) (wlc_layerCell K (dartNextSub K d)) := by
  
  have hso : SameOrbit K d.1 (dartNextSub K d).1 := ⟨1, by rw [dartNextSub_val]; rfl⟩
  have hr : ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Reachable
      ⟨(wlc_layerCell K d).1, (wlc_layerCell K d).2.1⟩
      ⟨(wlc_layerCell K (dartNextSub K d)).1, (wlc_layerCell K (dartNextSub K d)).2.1⟩ := by
    have h := sameComponent_of_sameOrbit K d.2 (dartNextSub K d).2 hso
    
    have e1 : (⟨d.1.head, d.2.2⟩ : (Kᶜ : Set (Site 2)))
        = ⟨(wlc_layerCell K d).1, (wlc_layerCell K d).2.1⟩ := Subtype.ext rfl
    have e2 : (⟨(dartNextSub K d).1.head, (dartNextSub K d).2.2⟩ : (Kᶜ : Set (Site 2)))
        = ⟨(wlc_layerCell K (dartNextSub K d)).1, (wlc_layerCell K (dartNextSub K d)).2.1⟩ :=
      Subtype.ext rfl
    rw [← e1, ← e2]; exact h
  
  rcases kf_dartNext_head_kingAdj_or_eq K d.1 with heq | hking
  · 
    have : wlc_layerCell K d = wlc_layerCell K (dartNextSub K d) := by
      apply Subtype.ext
      simp only [wlc_layerCell_val, dartNextSub_val, heq]
    rw [this]
  · 
    have hadj : (wdc_layerGraph K).Adj (wlc_layerCell K d) (wlc_layerCell K (dartNextSub K d)) := by
      refine ⟨?_, hr⟩
      simpa only [wlc_layerCell_val, dartNextSub_val] using hking
    exact hadj.reachable





theorem wlc_layerReachable_of_sameOrbit (K : Set (Site 2))
    {d1 d2 : {e : Dart // IsBoundaryDart K e}} (h : SameOrbit K d1.1 d2.1) :
    (wdc_layerGraph K).Reachable (wlc_layerCell K d1) (wlc_layerCell K d2) := by
  obtain ⟨n, hn⟩ := h
  have hval : ((dartNextSub K)^[n] d1).1 = d2.1 := by rw [dartNextSub_iterate_val]; exact hn
  have hsub : (dartNextSub K)^[n] d1 = d2 := Subtype.ext hval
  rw [← hsub]
  clear hsub hval hn
  induction n with
  | zero => exact Reachable.refl _
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (wlc_layerReachable_step K _)








theorem wlc_layerConnected_of_orbitTraceSurjective (K : Set (Site 2))
    (hOTS : OrbitTraceSurjective K) : wdc_LayerConnected K := by
  intro a b hreach
  
  set da := wdc_pick K a with hda
  set db := wdc_pick K b with hdb
  have hha : da.1.head = a.1 := wdc_pick_head K a
  have hhb : db.1.head = b.1 := wdc_pick_head K b
  
  have hr : ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Reachable
      ⟨da.1.head, da.2.2⟩ ⟨db.1.head, db.2.2⟩ := by
    have e1 : (⟨da.1.head, da.2.2⟩ : (Kᶜ : Set (Site 2))) = ⟨a.1, a.2.1⟩ := Subtype.ext hha
    have e2 : (⟨db.1.head, db.2.2⟩ : (Kᶜ : Set (Site 2))) = ⟨b.1, b.2.1⟩ := Subtype.ext hhb
    rw [e1, e2]; exact hreach
  
  have hso : SameOrbit K da.1 db.1 := hOTS da.1 db.1 da.2 db.2 hr
  have hlayer := wlc_layerReachable_of_sameOrbit K hso
  
  have ea : wlc_layerCell K da = a := Subtype.ext hha
  have eb : wlc_layerCell K db = b := Subtype.ext hhb
  rw [ea, eb] at hlayer
  exact hlayer





theorem wlc_dartConnected_of_orbitTraceSurjective (K : Set (Site 2))
    (hOTS : OrbitTraceSurjective K) : wots_DartConnected K :=
  wdc_dartConnected_of_layerConnected K (wlc_layerConnected_of_orbitTraceSurjective K hOTS)












theorem wlc_orbitTraceSurjective_iff (K : Set (Site 2)) :
    OrbitTraceSurjective K ↔ (wots_LocalStepSameOrbit K ∧ wdc_LayerConnected K) := by
  constructor
  · intro h
    exact ⟨wots_localStep_of_orbitTraceSurjective K h,
      wlc_layerConnected_of_orbitTraceSurjective K h⟩
  · rintro ⟨hstep, hlayer⟩
    exact wots_orbitTraceSurjective_of_reduction K hstep
      (wdc_dartConnected_of_layerConnected K hlayer)






theorem wlc_layerConnected_singleton (c : Site 2) :
    wdc_LayerConnected ({c} : Set (Site 2)) :=
  wlc_layerConnected_of_orbitTraceSurjective ({c} : Set (Site 2))
    (ifg_orbitTraceSurjective_singleton c)

end Wots

end StatMech
