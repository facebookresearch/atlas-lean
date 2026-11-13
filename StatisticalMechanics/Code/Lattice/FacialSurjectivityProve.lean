/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartInjective
import Code.Lattice.DartOrbit
import Code.Lattice.InterfaceOrbit
import Code.Lattice.InterfaceConnected
import Code.Lattice.InterfaceConnectedProof
import Code.Lattice.InsideConnected
import Code.Lattice.FaceComponentBijection
import Code.Lattice.RotationSystemFaces
import Code.Lattice.FacialSurjectivity

open Set SimpleGraph Function

namespace StatMech

namespace Lattice
















theorem fsp_canonicalCount_eq_componentCount {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    Nat.card (fsv_canonicalFamily Vc) = Nat.card (fcb_offComplGraph Vc).ConnectedComponent :=
  (fsv_componentCount_eq_canonicalCount Vc).symm






theorem fsp_canonicalCount_eq_two {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (h : fcb_OffComplJordanRegion Vc) :
    Nat.card (fsv_canonicalFamily Vc) = 2 := by
  rw [fsp_canonicalCount_eq_componentCount Vc, fcb_two_components_of_region Vc h]














theorem fsp_canonicalCount_eq_faceCount {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (h : fcb_OffComplJordanRegion Vc)
    {V : Type*} {G : SimpleGraph V} {v : V} (c : G.Walk v v) (hc : c.IsCycle) :
    Nat.card (fsv_canonicalFamily Vc) = faceCount c.toSubgraph.coe := by
  rw [fsp_canonicalCount_eq_componentCount Vc,
    fcb_offComplComponentCount_eq_faceCount_of_jordanRegion Vc h c hc]
















theorem fsp_offSupportComponent_inside_ne_outside {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (hxin : x ∈ jec_leftRegion Vc)
    (hyout : y ∉ jec_leftRegion Vc) (hyoff : y ∉ Vc.support) :
    offSupportComponent Vc x ≠ offSupportComponent Vc y := by
  intro heq
  have hx : x ∈ offSupportComponent Vc x := seed_mem_offSupportComponent Vc x
  rw [heq] at hx
  exact (offSupportComponent_subset_exterior Vc hyout hyoff hx) hxin








theorem fsp_inside_outside_facialOrbit_ne {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (hxin : x ∈ jec_leftRegion Vc) (hxoff : x ∉ Vc.support)
    (hyout : y ∉ jec_leftRegion Vc) (hyoff : y ∉ Vc.support) :
    {d : Dart | IsBoundaryDart (offSupportComponent Vc x) d} ≠
      {d : Dart | IsBoundaryDart (offSupportComponent Vc y) d} := by
  have hne : offSupportComponent Vc x ≠ offSupportComponent Vc y :=
    fsp_offSupportComponent_inside_ne_outside Vc hxin hyout hyoff
  have hdisj := rsf_disjoint_boundaryDarts_of_ne Vc hne
  obtain ⟨e, he⟩ := rsf_offSupportComponent_exists_boundaryDart Vc hxoff
  intro heqset
  have heU : e ∈ {d : Dart | IsBoundaryDart (offSupportComponent Vc x) d} := he
  have heV : e ∈ {d : Dart | IsBoundaryDart (offSupportComponent Vc y) d} := heqset ▸ heU
  exact (Set.disjoint_left.mp hdisj) heU heV







theorem fsp_facialOrbit_has_incident_cell {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z : Site 2} (hz : z ∉ Vc.support) :
    ∃ e : Dart, e ∈ {d : Dart | IsBoundaryDart (offSupportComponent Vc z) d} ∧
      e.tail ∈ offSupportComponent Vc z := by
  obtain ⟨e, he⟩ := rsf_offSupportComponent_exists_boundaryDart Vc hz
  exact ⟨e, he, he.1⟩
















theorem fsp_offSupportComponent_eq_inside_or_outside {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (hxin : x ∈ jec_leftRegion Vc) (hxoff : x ∉ Vc.support)
    (hyout : y ∉ jec_leftRegion Vc) (hyoff : y ∉ Vc.support)
    (hin : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        s ∉ Vc.support → t ∉ Vc.support →
        ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support)
    (hout : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc →
        s ∉ Vc.support → t ∉ Vc.support →
        ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support)
    {z : Site 2} (hz : z ∉ Vc.support) :
    offSupportComponent Vc z = offSupportComponent Vc x ∨
      offSupportComponent Vc z = offSupportComponent Vc y := by
  by_cases hzin : z ∈ jec_leftRegion Vc
  · left
    obtain ⟨p, hp⟩ := hin z x hzin hxin hz hxoff
    have hr : (offSupport Vc).Reachable z x := offSupportWalk_to_offSupport_reachable Vc p hp
    ext w
    rw [mem_offSupportComponent, mem_offSupportComponent]
    exact ⟨fun hzw => hr.symm.trans hzw, fun hxw => hr.trans hxw⟩
  · right
    obtain ⟨p, hp⟩ := hout z y hzin hyout hz hyoff
    have hr : (offSupport Vc).Reachable z y := offSupportWalk_to_offSupport_reachable Vc p hp
    ext w
    rw [mem_offSupportComponent, mem_offSupportComponent]
    exact ⟨fun hzw => hr.symm.trans hzw, fun hyw => hr.trans hyw⟩













theorem fsp_canonicalFamily_eq_pair {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (hxin : x ∈ jec_leftRegion Vc) (hxoff : x ∉ Vc.support)
    (hyout : y ∉ jec_leftRegion Vc) (hyoff : y ∉ Vc.support)
    (hin : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        s ∉ Vc.support → t ∉ Vc.support →
        ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support)
    (hout : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc →
        s ∉ Vc.support → t ∉ Vc.support →
        ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support) :
    fsv_canonicalFamily Vc =
      {{d : Dart | IsBoundaryDart (offSupportComponent Vc x) d},
       {d : Dart | IsBoundaryDart (offSupportComponent Vc y) d}} := by
  ext D
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases fsp_offSupportComponent_eq_inside_or_outside Vc hxin hxoff hyout hyoff hin hout hz
      with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h]; rfl)
  · rintro (rfl | rfl)
    · exact ⟨x, hxoff, rfl⟩
    · exact ⟨y, hyoff, rfl⟩







theorem fsp_canonicalFamily_eq_pair_of_jordanRegion {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (h : fcb_OffComplJordanRegion Vc) :
    ∃ x y : Site 2, x ∈ jec_leftRegion Vc ∧ x ∉ Vc.support ∧
      y ∉ jec_leftRegion Vc ∧ y ∉ Vc.support ∧
      fsv_canonicalFamily Vc =
        {{d : Dart | IsBoundaryDart (offSupportComponent Vc x) d},
         {d : Dart | IsBoundaryDart (offSupportComponent Vc y) d}} := by
  obtain ⟨⟨x, hxin, hxoff⟩, ⟨y, hyout, hyoff⟩, hin, hout⟩ := h
  exact ⟨x, y, hxin, hxoff, hyout, hyoff,
    fsp_canonicalFamily_eq_pair Vc hxin hxoff hyout hyoff hin hout⟩








theorem fsp_canonical_isPair {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (hxin : x ∈ jec_leftRegion Vc) (hxoff : x ∉ Vc.support)
    (hyout : y ∉ jec_leftRegion Vc) (hyoff : y ∉ Vc.support)
    (hin : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        s ∉ Vc.support → t ∉ Vc.support →
        ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support)
    (hout : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc →
        s ∉ Vc.support → t ∉ Vc.support →
        ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support) :
    Nat.card (fsv_canonicalFamily Vc) = 2 := by
  rw [fsp_canonicalFamily_eq_pair Vc hxin hxoff hyout hyoff hin hout]
  rw [Nat.card_coe_set_eq, Set.ncard_pair
    (fsp_inside_outside_facialOrbit_ne Vc hxin hxoff hyout hyoff)]

end Lattice

end StatMech
