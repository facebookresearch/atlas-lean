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
import Code.Lattice.InsideConnected
import Code.Lattice.FaceComponentBijection

open Set SimpleGraph Function

namespace StatMech

namespace Lattice










theorem rsf_boundaryDart_tail_mem (C : Set (Site 2)) {e : Dart} (he : IsBoundaryDart C e) :
    e.tail ∈ C := he.1


theorem rsf_boundaryDart_head_not_mem (C : Set (Site 2)) {e : Dart} (he : IsBoundaryDart C e) :
    e.head ∉ C := he.2










theorem rsf_no_shared_boundaryDart {C C' : Set (Site 2)} (hCC' : Disjoint C C')
    {e : Dart} (he : IsBoundaryDart C e) (he' : IsBoundaryDart C' e) : False := by
  exact (Set.disjoint_left.mp hCC') he.1 he'.1




theorem rsf_disjoint_boundaryDarts_of_disjoint {C C' : Set (Site 2)} (hCC' : Disjoint C C') :
    Disjoint {e : Dart | IsBoundaryDart C e} {e : Dart | IsBoundaryDart C' e} := by
  rw [Set.disjoint_left]
  intro e he he'
  exact rsf_no_shared_boundaryDart hCC' he he'











theorem rsf_orbit_isBoundaryDart (C : Set (Site 2)) {e : Dart} (he : IsBoundaryDart C e)
    (k : ℕ) : IsBoundaryDart C ((dartNext C)^[k] e) := by
  induction k with
  | zero => exact he
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact dartNext_isBoundaryDart C ((dartNext C)^[n] e) ih




theorem rsf_orbit_tail_mem (C : Set (Site 2)) {e : Dart} (he : IsBoundaryDart C e) (k : ℕ) :
    ((dartNext C)^[k] e).tail ∈ C :=
  (rsf_orbit_isBoundaryDart C he k).1


theorem rsf_orbit_head_not_mem (C : Set (Site 2)) {e : Dart} (he : IsBoundaryDart C e) (k : ℕ) :
    ((dartNext C)^[k] e).head ∉ C :=
  (rsf_orbit_isBoundaryDart C he k).2










noncomputable def rsf_facialOrbit (C : Set (Site 2)) (e : {d : Dart // IsBoundaryDart C d}) :
    (dartSuccGraph C).ConnectedComponent :=
  (dartSuccGraph C).connectedComponentMk e



theorem rsf_facialOrbit_next (C : Set (Site 2)) (e : {d : Dart // IsBoundaryDart C d}) :
    rsf_facialOrbit C (dartNextSub C e) = rsf_facialOrbit C e := by
  unfold rsf_facialOrbit
  rw [ConnectedComponent.eq]
  exact (dartSuccGraph_adj_next C e).symm.reachable












theorem rsf_offSupportComponent_eq_of_mem {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed z : Site 2} (hz : z ∈ offSupportComponent Vc seed) :
    offSupportComponent Vc z = offSupportComponent Vc seed := by
  rw [mem_offSupportComponent] at hz
  ext w
  rw [mem_offSupportComponent, mem_offSupportComponent]
  exact ⟨fun h => hz.trans h, fun h => hz.symm.trans h⟩



theorem rsf_offSupportComponent_eq_or_disjoint {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (s t : Site 2) :
    offSupportComponent Vc s = offSupportComponent Vc t ∨
      Disjoint (offSupportComponent Vc s) (offSupportComponent Vc t) := by
  by_cases h : (offSupportComponent Vc s ∩ offSupportComponent Vc t).Nonempty
  · left
    obtain ⟨z, hzs, hzt⟩ := h
    rw [← rsf_offSupportComponent_eq_of_mem Vc hzs, ← rsf_offSupportComponent_eq_of_mem Vc hzt]
  · right
    rw [Set.disjoint_iff_inter_eq_empty, Set.not_nonempty_iff_eq_empty] at *
    exact h




theorem rsf_componentBoundaryDart_determines_component {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) {seed : Site 2}
    {e : Dart} (he : IsBoundaryDart (offSupportComponent Vc seed) e) :
    offSupportComponent Vc e.tail = offSupportComponent Vc seed :=
  rsf_offSupportComponent_eq_of_mem Vc he.1














theorem rsf_disjoint_boundaryDarts_of_ne {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {s t : Site 2} (hne : offSupportComponent Vc s ≠ offSupportComponent Vc t) :
    Disjoint {e : Dart | IsBoundaryDart (offSupportComponent Vc s) e}
      {e : Dart | IsBoundaryDart (offSupportComponent Vc t) e} := by
  rcases rsf_offSupportComponent_eq_or_disjoint Vc s t with h | h
  · exact absurd h hne
  · exact rsf_disjoint_boundaryDarts_of_disjoint h





theorem rsf_boundaryDart_unique_component {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {s t : Site 2} {e : Dart}
    (hs : IsBoundaryDart (offSupportComponent Vc s) e)
    (ht : IsBoundaryDart (offSupportComponent Vc t) e) :
    offSupportComponent Vc s = offSupportComponent Vc t := by
  rw [← rsf_componentBoundaryDart_determines_component Vc hs,
    ← rsf_componentBoundaryDart_determines_component Vc ht]











theorem rsf_reach_axis_le (x : Site 2) (j : Fin 2) (a : ℤ) (n : ℕ) :
    (hypercubicLattice 2).Reachable (Function.update x j a) (Function.update x j (a + n)) := by
  induction n with
  | zero => simp
  | succ m ih =>
    refine ih.trans (SimpleGraph.Adj.reachable ?_)
    rw [hypercubicLattice_adj, Finset.sum_eq_single j]
    · simp only [Function.update_self]
      have : a + ((m : ℕ) : ℤ) - (a + ((m + 1 : ℕ) : ℤ)) = -1 := by push_cast; ring
      rw [this]; rfl
    · intro b _ hb; rw [Function.update_of_ne hb, Function.update_of_ne hb]; simp
    · intro h; exact absurd (Finset.mem_univ j) h



theorem rsf_reach_axis (x : Site 2) (j : Fin 2) (a b : ℤ) :
    (hypercubicLattice 2).Reachable (Function.update x j a) (Function.update x j b) := by
  rcases le_total a b with hab | hab
  · obtain ⟨n, rfl⟩ := Int.le.dest hab; exact rsf_reach_axis_le x j a n
  · obtain ⟨n, rfl⟩ := Int.le.dest hab; exact (rsf_reach_axis_le x j b n).symm




theorem rsf_reach_all (x y : Site 2) : (hypercubicLattice 2).Reachable x y := by
  have h1 : (hypercubicLattice 2).Reachable x (Function.update x 0 (y 0)) := by
    have := rsf_reach_axis x 0 (x 0) (y 0); rwa [Function.update_eq_self] at this
  set z := Function.update x 0 (y 0) with hz
  have h2 : (hypercubicLattice 2).Reachable z (Function.update z 1 (y 1)) := by
    have := rsf_reach_axis z 1 (z 1) (y 1); rwa [Function.update_eq_self] at this
  have hzy : Function.update z 1 (y 1) = y := by funext i; fin_cases i <;> simp [hz]
  rw [hzy] at h2; exact h1.trans h2




theorem rsf_walk_crosses (C : Set (Site 2)) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (hx : x ∈ C) (hy : y ∉ C) :
    ∃ e : Dart, IsBoundaryDart C e := by
  induction w with
  | nil => exact absurd hx hy
  | @cons u v z huv w ih =>
    by_cases hv : v ∈ C
    · exact ih hv hy
    · exact ⟨⟨u, v, huv⟩, hx, hv⟩




theorem rsf_exists_boundaryDart (C : Set (Site 2)) {c z : Site 2} (hc : c ∈ C) (hz : z ∉ C) :
    ∃ e : Dart, IsBoundaryDart C e := by
  obtain ⟨w⟩ := rsf_reach_all c z
  exact rsf_walk_crosses C w hc hz





theorem rsf_offSupportComponent_exists_boundaryDart {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) {seed : Site 2} (hseed : seed ∉ Vc.support) :
    ∃ e : Dart, IsBoundaryDart (offSupportComponent Vc seed) e := by
  have ha_supp : a ∈ Vc.support := Vc.start_mem_support
  have ha_notin : a ∉ offSupportComponent Vc seed := fun hin =>
    offSupportComponent_offSupport Vc hseed hin ha_supp
  exact rsf_exists_boundaryDart _ (seed_mem_offSupportComponent Vc seed) ha_notin















theorem rsf_fcb_reachable_offSupportComponent_eq {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : {z : Site 2 // z ∉ Vc.support}} (h : (fcb_offComplGraph Vc).Reachable x y) :
    offSupportComponent Vc (x : Site 2) = offSupportComponent Vc (y : Site 2) := by
  obtain ⟨p, hp⟩ := (fcb_induce_reachable_iff Vc).mp h
  have hr : (offSupport Vc).Reachable (x : Site 2) (y : Site 2) :=
    offSupportWalk_to_offSupport_reachable Vc p hp
  ext w
  rw [mem_offSupportComponent, mem_offSupportComponent]
  exact ⟨fun hx => hr.symm.trans hx, fun hy => hr.trans hy⟩





theorem rsf_fcb_reachable_of_offSupportComponent_eq {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) {u v : {z : Site 2 // z ∉ Vc.support}}
    (heq : offSupportComponent Vc (u : Site 2) = offSupportComponent Vc (v : Site 2)) :
    (fcb_offComplGraph Vc).Reachable u v := by
  have hv : (v : Site 2) ∈ offSupportComponent Vc (u : Site 2) := by
    rw [heq]; exact seed_mem_offSupportComponent Vc _
  rw [mem_offSupportComponent] at hv
  obtain ⟨p, hp⟩ := offSupport_reachable_to_offSupportWalk Vc hv u.2
  exact (fcb_induce_reachable_iff Vc).mpr ⟨p, hp⟩





noncomputable def rsf_componentDarts {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    (fcb_offComplGraph Vc).ConnectedComponent → Set Dart :=
  ConnectedComponent.lift
    (fun v => {e : Dart | IsBoundaryDart (offSupportComponent Vc (v : Site 2)) e})
    (by
      intro u v p _
      simp only
      rw [rsf_fcb_reachable_offSupportComponent_eq Vc ⟨p⟩])

@[simp] theorem rsf_componentDarts_mk {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (v : {z : Site 2 // z ∉ Vc.support}) :
    rsf_componentDarts Vc ((fcb_offComplGraph Vc).connectedComponentMk v)
      = {e : Dart | IsBoundaryDart (offSupportComponent Vc (v : Site 2)) e} := rfl








theorem rsf_componentDarts_injective {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    Function.Injective (rsf_componentDarts Vc) := by
  refine ConnectedComponent.ind₂ ?_
  intro u v huv
  rw [rsf_componentDarts_mk, rsf_componentDarts_mk] at huv
  rw [ConnectedComponent.eq]
  apply rsf_fcb_reachable_of_offSupportComponent_eq Vc
  
  obtain ⟨e, he⟩ := rsf_offSupportComponent_exists_boundaryDart Vc u.2
  have heU : e ∈ {e : Dart | IsBoundaryDart (offSupportComponent Vc (u : Site 2)) e} := he
  rw [huv] at heU
  exact rsf_boundaryDart_unique_component Vc he heU















theorem rsf_componentCount_le_facialOrbitRange {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    Nat.card (fcb_offComplGraph Vc).ConnectedComponent
      = Nat.card (Set.range (rsf_componentDarts Vc)) :=
  (Nat.card_range_of_injective (rsf_componentDarts_injective Vc)).symm









def rsf_FacialOrbitsCoverComponents {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (𝓕 : Set (Set Dart)) : Prop :=
  Set.range (rsf_componentDarts Vc) = 𝓕













theorem rsf_componentCount_eq_facialOrbitCount {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {𝓕 : Set (Set Dart)} (hcov : rsf_FacialOrbitsCoverComponents Vc 𝓕) :
    Nat.card (fcb_offComplGraph Vc).ConnectedComponent = Nat.card 𝓕 := by
  rw [rsf_componentCount_le_facialOrbitRange Vc]
  unfold rsf_FacialOrbitsCoverComponents at hcov
  rw [hcov]












theorem rsf_componentDarts_nonempty {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (c : (fcb_offComplGraph Vc).ConnectedComponent) :
    (rsf_componentDarts Vc c).Nonempty := by
  refine ConnectedComponent.ind ?_ c
  intro v
  rw [rsf_componentDarts_mk]
  obtain ⟨e, he⟩ := rsf_offSupportComponent_exists_boundaryDart Vc v.2
  exact ⟨e, he⟩





theorem rsf_facialOrbitRange_nonempty {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z : Site 2} (hz : z ∉ Vc.support) :
    (Set.range (rsf_componentDarts Vc)).Nonempty :=
  ⟨rsf_componentDarts Vc ((fcb_offComplGraph Vc).connectedComponentMk ⟨z, hz⟩),
    Set.mem_range_self _⟩

end Lattice

end StatMech
