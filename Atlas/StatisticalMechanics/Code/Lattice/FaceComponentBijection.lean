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
import Code.Lattice.JordanContour
import Code.Lattice.JordanCycleSpace
import Code.Lattice.FloodFillConnected
import Code.Lattice.InsideConnected

open Set SimpleGraph Function

namespace StatMech

namespace Lattice














noncomputable def fcb_offComplGraph {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    SimpleGraph {z : Site 2 // z ∉ Vc.support} :=
  (ffc_offSupportLattice {z | z ∈ Vc.support}).induce {z : Site 2 | z ∉ Vc.support}

@[simp] theorem fcb_offComplGraph_adj {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (x y : {z : Site 2 // z ∉ Vc.support}) :
    (fcb_offComplGraph Vc).Adj x y ↔
      (ffc_offSupportLattice {z | z ∈ Vc.support}).Adj (x : Site 2) (y : Site 2) :=
  Iff.rfl











theorem fcb_induce_reachable_to_ambient {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : {z : Site 2 // z ∉ Vc.support}}
    (h : (fcb_offComplGraph Vc).Reachable x y) :
    (ffc_offSupportLattice {z | z ∈ Vc.support}).Reachable (x : Site 2) (y : Site 2) := by
  
  obtain ⟨w⟩ := h
  exact ⟨w.map (Hom.comap (Function.Embedding.subtype
    fun z => z ∈ ({z : Site 2 | z ∉ Vc.support} : Set (Site 2)))
    (ffc_offSupportLattice {z | z ∈ Vc.support}))⟩





theorem fcb_ambient_reachable_to_induce {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : {z : Site 2 // z ∉ Vc.support}}
    (h : (ffc_offSupportLattice {z | z ∈ Vc.support}).Reachable (x : Site 2) (y : Site 2)) :
    (fcb_offComplGraph Vc).Reachable x y := by
  
  have hx : (x : Site 2) ∉ ({z | z ∈ Vc.support} : Set (Site 2)) := x.2
  obtain ⟨p, hp⟩ := (ffc_reachable_iff_offSupportWalk hx).mp h
  
  have hlift : (ffc_offSupportLattice {z | z ∈ Vc.support}).Reachable (x : Site 2) (y : Site 2) :=
    ⟨ffc_lift_walk p hp⟩
  obtain ⟨w⟩ := hlift
  
  have hwoff : ∀ z ∈ w.support, z ∉ ({z | z ∈ Vc.support} : Set (Site 2)) :=
    ffc_offSupportWalk_support w hx
  exact walk_induce_reachable (ffc_offSupportLattice {z | z ∈ Vc.support})
    {z : Site 2 | z ∉ Vc.support} w (fun z hz => hwoff z hz) x.2 y.2





theorem fcb_induce_reachable_iff {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : {z : Site 2 // z ∉ Vc.support}} :
    (fcb_offComplGraph Vc).Reachable x y ↔
      ∃ p : (hypercubicLattice 2).Walk (x : Site 2) (y : Site 2),
        ∀ z ∈ p.support, z ∉ Vc.support := by
  constructor
  · intro h
    have hx : (x : Site 2) ∉ ({z | z ∈ Vc.support} : Set (Site 2)) := x.2
    exact (ffc_reachable_iff_offSupportWalk hx).mp (fcb_induce_reachable_to_ambient Vc h)
  · rintro ⟨p, hp⟩
    have hx : (x : Site 2) ∉ ({z | z ∈ Vc.support} : Set (Site 2)) := x.2
    exact fcb_ambient_reachable_to_induce Vc ((ffc_reachable_iff_offSupportWalk hx).mpr ⟨p, hp⟩)













theorem fcb_offCompl_sameSide {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : {z : Site 2 // z ∉ Vc.support}}
    (h : (fcb_offComplGraph Vc).Reachable x y) :
    ((x : Site 2) ∈ jec_leftRegion Vc ↔ (y : Site 2) ∈ jec_leftRegion Vc) := by
  obtain ⟨p, hp⟩ := (fcb_induce_reachable_iff Vc).mp h
  exact jlri_sameRegion_along_offSupport_walk Vc p hp


























theorem fcb_two_components_of_sides {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (hxin : x ∈ jec_leftRegion Vc) (hxoff : x ∉ Vc.support)
    (hyout : y ∉ jec_leftRegion Vc) (hyoff : y ∉ Vc.support)
    (hin : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        s ∉ Vc.support → t ∉ Vc.support →
        ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support)
    (hout : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc →
        s ∉ Vc.support → t ∉ Vc.support →
        ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support) :
    Nat.card (fcb_offComplGraph Vc).ConnectedComponent = 2 := by
  classical
  set L := fcb_offComplGraph Vc with hL
  
  let f : L.ConnectedComponent → Bool :=
    ConnectedComponent.lift (fun v => decide ((v : Site 2) ∈ jec_leftRegion Vc)) (by
      intro u v p _
      have hreach : L.Reachable u v := ⟨p⟩
      have := fcb_offCompl_sameSide Vc hreach
      simp only [decide_eq_decide]; exact this)
  have hf_mk : ∀ v : {z : Site 2 // z ∉ Vc.support},
      f (L.connectedComponentMk v) = decide ((v : Site 2) ∈ jec_leftRegion Vc) := fun _ => rfl
  have hbij : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · 
      refine ConnectedComponent.ind₂ ?_
      intro u v huv
      rw [hf_mk, hf_mk, decide_eq_decide] at huv
      rw [ConnectedComponent.eq]
      by_cases huS : (u : Site 2) ∈ jec_leftRegion Vc
      · 
        have hvS : (v : Site 2) ∈ jec_leftRegion Vc := huv.mp huS
        obtain ⟨p, hp⟩ := hin (u : Site 2) (v : Site 2) huS hvS u.2 v.2
        exact (fcb_induce_reachable_iff Vc).mpr ⟨p, hp⟩
      · 
        have hvS : (v : Site 2) ∉ jec_leftRegion Vc := fun hvS => huS (huv.mpr hvS)
        obtain ⟨p, hp⟩ := hout (u : Site 2) (v : Site 2) huS hvS u.2 v.2
        exact (fcb_induce_reachable_iff Vc).mpr ⟨p, hp⟩
    · 
      intro c
      cases c with
      | true =>
        refine ⟨L.connectedComponentMk ⟨x, hxoff⟩, ?_⟩
        rw [hf_mk]; simp [hxin]
      | false =>
        refine ⟨L.connectedComponentMk ⟨y, hyoff⟩, ?_⟩
        rw [hf_mk]; simp [hyout]
  rw [Nat.card_eq_of_bijective f hbij, Nat.card_eq_fintype_card, Fintype.card_bool]




















theorem fcb_offComplComponentCount_eq_faceCount {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {V : Type*} {G : SimpleGraph V} {v : V} (c : G.Walk v v) (hc : c.IsCycle)
    {x y : Site 2} (hxin : x ∈ jec_leftRegion Vc) (hxoff : x ∉ Vc.support)
    (hyout : y ∉ jec_leftRegion Vc) (hyoff : y ∉ Vc.support)
    (hin : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        s ∉ Vc.support → t ∉ Vc.support →
        ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support)
    (hout : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc →
        s ∉ Vc.support → t ∉ Vc.support →
        ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support) :
    Nat.card (fcb_offComplGraph Vc).ConnectedComponent = faceCount c.toSubgraph.coe := by
  rw [fcb_two_components_of_sides Vc hxin hxoff hyout hyoff hin hout,
    jcs_cycle_faceCount_eq_two c hc]












theorem fcb_inside_conn_of_covers {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hoff : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
    {sIn : Site 2} (hcovIn : jec_leftRegion Vc ⊆ offSupportComponent Vc sIn) :
    ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        s ∉ Vc.support → t ∉ Vc.support →
      ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support := by
  intro s t hs ht _ _
  exact hInOff_of_covers Vc hoff hcovIn s t hs ht




theorem fcb_outside_conn_of_covers {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {sOut : Site 2} (hcovOut : (jec_leftRegion Vc)ᶜ ⊆ offSupportComponent Vc sOut) :
    ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc →
        s ∉ Vc.support → t ∉ Vc.support →
      ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support := by
  intro s t hs ht hsoff _
  have hubOut : ∀ r : Site 2, r ∉ jec_leftRegion Vc → (offSupport Vc).Reachable sOut r :=
    fun r hr => (mem_offSupportComponent Vc).mp (hcovOut hr)
  have hconn : (offSupport Vc).Reachable s t := ((hubOut s hs).symm).trans (hubOut t ht)
  exact offSupport_reachable_to_offSupportWalk Vc hconn hsoff








theorem fcb_offComplComponentCount_eq_two_of_covers {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a)
    (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
    (hoffOut : ∀ s ∉ jec_leftRegion Vc, s ∉ Vc.support)
    {x y : Site 2} (hxin : x ∈ jec_leftRegion Vc) (hyout : y ∉ jec_leftRegion Vc)
    {sIn sOut : Site 2}
    (hcovIn : jec_leftRegion Vc ⊆ offSupportComponent Vc sIn)
    (hcovOut : (jec_leftRegion Vc)ᶜ ⊆ offSupportComponent Vc sOut) :
    Nat.card (fcb_offComplGraph Vc).ConnectedComponent = 2 :=
  fcb_two_components_of_sides Vc hxin (hoffIn x hxin) hyout (hoffOut y hyout)
    (fcb_inside_conn_of_covers Vc hoffIn hcovIn)
    (fcb_outside_conn_of_covers Vc hcovOut)














def fcb_OffComplJordanRegion {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  (∃ x, x ∈ jec_leftRegion Vc ∧ x ∉ Vc.support) ∧
    (∃ y, y ∉ jec_leftRegion Vc ∧ y ∉ Vc.support) ∧
    (∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        s ∉ Vc.support → t ∉ Vc.support →
        ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support) ∧
    (∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc →
        s ∉ Vc.support → t ∉ Vc.support →
        ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support)








theorem fcb_offComplJordanRegion_of_covers {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
    (hoffOut : ∀ s ∉ jec_leftRegion Vc, s ∉ Vc.support)
    {x y : Site 2} (hxin : x ∈ jec_leftRegion Vc) (hyout : y ∉ jec_leftRegion Vc)
    {sIn sOut : Site 2}
    (hcovIn : jec_leftRegion Vc ⊆ offSupportComponent Vc sIn)
    (hcovOut : (jec_leftRegion Vc)ᶜ ⊆ offSupportComponent Vc sOut) :
    fcb_OffComplJordanRegion Vc :=
  ⟨⟨x, hxin, hoffIn x hxin⟩, ⟨y, hyout, hoffOut y hyout⟩,
    fcb_inside_conn_of_covers Vc hoffIn hcovIn,
    fcb_outside_conn_of_covers Vc hcovOut⟩



theorem fcb_two_components_of_region {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (h : fcb_OffComplJordanRegion Vc) :
    Nat.card (fcb_offComplGraph Vc).ConnectedComponent = 2 := by
  obtain ⟨⟨x, hxin, hxoff⟩, ⟨y, hyout, hyoff⟩, hin, hout⟩ := h
  exact fcb_two_components_of_sides Vc hxin hxoff hyout hyoff hin hout










theorem fcb_offComplComponentCount_eq_faceCount_of_jordanRegion {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (h : fcb_OffComplJordanRegion Vc)
    {V : Type*} {G : SimpleGraph V} {v : V} (c : G.Walk v v) (hc : c.IsCycle) :
    Nat.card (fcb_offComplGraph Vc).ConnectedComponent = faceCount c.toSubgraph.coe := by
  rw [fcb_two_components_of_region Vc h, jcs_cycle_faceCount_eq_two c hc]













theorem fcb_self_component_side {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (v : {z : Site 2 // z ∉ Vc.support}) :
    ((v : Site 2) ∈ jec_leftRegion Vc ↔ (v : Site 2) ∈ jec_leftRegion Vc) :=
  Iff.rfl





theorem fcb_adj_sameSide {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u ∉ Vc.support) (hv : v ∉ Vc.support) :
    (u ∈ jec_leftRegion Vc ↔ v ∈ jec_leftRegion Vc) := by
  have hadj' : (fcb_offComplGraph Vc).Adj ⟨u, hu⟩ ⟨v, hv⟩ := ⟨hadj, hu, hv⟩
  exact fcb_offCompl_sameSide Vc hadj'.reachable

end Lattice

end StatMech
