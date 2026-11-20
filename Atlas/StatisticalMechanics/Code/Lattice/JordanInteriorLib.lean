/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.SegmentConn
import Code.Lattice.CrossingParity
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.OrbitExteriorEven
import Code.Lattice.JordanLeftRegionInterior
import Code.Lattice.FloodFillConnected

open Set SimpleGraph Function

namespace StatMech

namespace Lattice













theorem jil_floodFill_stepRight (B : Set (Site 2)) {seed : Site 2} {x y : ℤ}
    (hz : (![x, y] : Site 2) ∈ ffc_floodFill B seed)
    (hzB : (![x, y] : Site 2) ∉ B) (hwB : (![x + 1, y] : Site 2) ∉ B) :
    (![x + 1, y] : Site 2) ∈ ffc_floodFill B seed := by
  refine ffc_floodFill_step hz ?_ hzB hwB
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  simp




theorem jil_floodFill_run_right (B : Set (Site 2)) {seed : Site 2} {x₀ y : ℤ} (k : ℕ)
    (h0 : (![x₀, y] : Site 2) ∈ ffc_floodFill B seed)
    (hoff : ∀ t : ℕ, t ≤ k → (![x₀ + (t : ℤ), y] : Site 2) ∉ B) :
    (![x₀ + (k : ℤ), y] : Site 2) ∈ ffc_floodFill B seed := by
  induction k with
  | zero => simpa using h0
  | succ m ih =>
    have hm : (![x₀ + (m : ℤ), y] : Site 2) ∈ ffc_floodFill B seed :=
      ih (fun t ht => hoff t (ht.trans (Nat.le_succ m)))
    have hmB : (![x₀ + (m : ℤ), y] : Site 2) ∉ B := hoff m (Nat.le_succ m)
    have hsB : (![x₀ + ((m : ℤ) + 1), y] : Site 2) ∉ B := by
      have := hoff (m + 1) le_rfl
      simpa [Nat.cast_succ, add_comm, add_left_comm, add_assoc] using this
    have hstep := jil_floodFill_stepRight B hm hmB (by
      simpa [add_assoc] using hsB)
    simpa [Nat.cast_succ, add_assoc] using hstep











theorem jil_localConstancy {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u ∉ Vc.support) (hv : v ∉ Vc.support) :
    (Even (jec_rayCount u Vc) ↔ Even (jec_rayCount v Vc)) :=
  jec_localConstancy Vc hadj hu hv






theorem jil_floodFill_sameParity {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseed : seed ∉ Vc.support)
    {z : Site 2} (hz : z ∈ ffc_floodFill {p | p ∈ Vc.support} seed) :
    (Even (jec_rayCount seed Vc) ↔ Even (jec_rayCount z Vc)) := by
  obtain ⟨p, hp⟩ := ffc_floodFill_self_offSupport_walk hseed hz
  exact oee_rayParity_const_along_walk Vc p (by
    intro w hw; exact hp w hw)






theorem jil_floodFill_subset_leftRegion {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseed : seed ∉ Vc.support) (hseedIn : seed ∈ jec_leftRegion Vc) :
    ffc_floodFill {p | p ∈ Vc.support} seed ⊆ jec_leftRegion Vc := by
  intro z hz
  rw [jec_mem_leftRegion] at hseedIn ⊢
  have hpar := jil_floodFill_sameParity Vc hseed hz
  exact fun h => hseedIn (hpar.mpr h)





theorem jil_floodFill_subset_exterior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseed : seed ∉ Vc.support) (hseedOut : seed ∉ jec_leftRegion Vc) :
    ffc_floodFill {p | p ∈ Vc.support} seed ⊆ (jec_leftRegion Vc)ᶜ := by
  intro z hz
  rw [jec_mem_leftRegion, not_not] at hseedOut
  rw [Set.mem_compl_iff, jec_mem_leftRegion, not_not]
  have hpar := jil_floodFill_sameParity Vc hseed hz
  exact hpar.mp hseedOut












theorem jil_hsegment_mem_floodFill (B : Set (Site 2)) {lo hi y x : ℤ}
    (hxlo : lo ≤ x) (hxhi : x ≤ hi)
    (hoff : ∀ t : ℤ, lo ≤ t → t ≤ hi → (![t, y] : Site 2) ∉ B) :
    (![x, y] : Site 2) ∈ ffc_floodFill B (![lo, y] : Site 2) := by
  
  set k : ℕ := (x - lo).toNat with hk
  have hxk : x = lo + (k : ℤ) := by rw [hk]; omega
  rw [hxk]
  refine jil_floodFill_run_right B k ?_ ?_
  · exact ffc_seed_mem_floodFill B (![lo, y] : Site 2)
  · intro t ht
    refine hoff (lo + (t : ℤ)) (by omega) ?_
    have : (t : ℤ) ≤ (k : ℤ) := by exact_mod_cast ht
    omega




theorem jil_hsegment_reachable_offSupport (B : Set (Site 2)) {lo hi y x₁ x₂ : ℤ}
    (hloB : (![lo, y] : Site 2) ∉ B)
    (hx₁lo : lo ≤ x₁) (hx₁hi : x₁ ≤ hi) (hx₂lo : lo ≤ x₂) (hx₂hi : x₂ ≤ hi)
    (hoff : ∀ t : ℤ, lo ≤ t → t ≤ hi → (![t, y] : Site 2) ∉ B) :
    ∃ p : (hypercubicLattice 2).Walk (![x₁, y] : Site 2) ![x₂, y],
      ∀ z ∈ p.support, z ∉ B := by
  have h1 : (![x₁, y] : Site 2) ∈ ffc_floodFill B (![lo, y] : Site 2) :=
    jil_hsegment_mem_floodFill B hx₁lo hx₁hi hoff
  have h2 : (![x₂, y] : Site 2) ∈ ffc_floodFill B (![lo, y] : Site 2) :=
    jil_hsegment_mem_floodFill B hx₂lo hx₂hi hoff
  exact ffc_floodFill_path_connected_offSupport hloB h1 h2










theorem jil_hsegment_sameParity {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {lo hi y x : ℤ} (hloB : (![lo, y] : Site 2) ∉ Vc.support)
    (hxlo : lo ≤ x) (hxhi : x ≤ hi)
    (hoff : ∀ t : ℤ, lo ≤ t → t ≤ hi → (![t, y] : Site 2) ∉ Vc.support) :
    (Even (jec_rayCount (![lo, y] : Site 2) Vc) ↔ Even (jec_rayCount (![x, y] : Site 2) Vc)) := by
  have hmem : (![x, y] : Site 2) ∈ ffc_floodFill {p | p ∈ Vc.support} (![lo, y] : Site 2) :=
    jil_hsegment_mem_floodFill {p | p ∈ Vc.support} hxlo hxhi
      (by intro t ht ht'; exact hoff t ht ht')
  exact jil_floodFill_sameParity Vc hloB hmem





theorem jil_hsegment_subset_leftRegion {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {lo hi y x₀ x : ℤ}
    (hx₀lo : lo ≤ x₀) (hx₀hi : x₀ ≤ hi) (hxlo : lo ≤ x) (hxhi : x ≤ hi)
    (hoff : ∀ t : ℤ, lo ≤ t → t ≤ hi → (![t, y] : Site 2) ∉ Vc.support)
    (hin : (![x₀, y] : Site 2) ∈ jec_leftRegion Vc) :
    (![x, y] : Site 2) ∈ jec_leftRegion Vc := by
  have hloB : (![lo, y] : Site 2) ∉ Vc.support := hoff lo le_rfl (le_trans hx₀lo hx₀hi)
  rw [jec_mem_leftRegion] at hin ⊢
  
  have hpx₀ := jil_hsegment_sameParity Vc hloB hx₀lo hx₀hi hoff
  have hpx := jil_hsegment_sameParity Vc hloB hxlo hxhi hoff
  intro h
  exact hin (hpx₀.mp (hpx.mpr h))













def jil_offSupportInterior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) : Set (Site 2) :=
  {z | z ∉ Vc.support ∧ z ∈ jec_leftRegion Vc}

@[simp] theorem jil_mem_offSupportInterior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (z : Site 2) :
    z ∈ jil_offSupportInterior Vc ↔ z ∉ Vc.support ∧ z ∈ jec_leftRegion Vc := Iff.rfl




theorem jil_floodFill_subset_offSupportInterior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseed : seed ∉ Vc.support) (hseedIn : seed ∈ jec_leftRegion Vc) :
    ffc_floodFill {p | p ∈ Vc.support} seed ⊆ jil_offSupportInterior Vc := by
  intro z hz
  rw [jil_mem_offSupportInterior]
  refine ⟨?_, jil_floodFill_subset_leftRegion Vc hseed hseedIn hz⟩
  have := ffc_floodFill_offSupport (B := {p | p ∈ Vc.support}) (by
    simpa using hseed) hz
  simpa using this









def jil_RowLinked {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (seed : Site 2) : Prop :=
  ∀ z ∈ jil_offSupportInterior Vc,
    ∃ p : (hypercubicLattice 2).Walk z seed, ∀ w ∈ p.support, w ∉ Vc.support




theorem jil_offSupportInterior_subset_floodFill {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hlink : jil_RowLinked Vc seed) :
    jil_offSupportInterior Vc ⊆ ffc_floodFill {p | p ∈ Vc.support} seed := by
  intro z hz
  obtain ⟨p, hp⟩ := hlink z hz
  
  have hzB : z ∉ ({p | p ∈ Vc.support} : Set (Site 2)) := by
    simpa using (jil_mem_offSupportInterior Vc z |>.mp hz).1
  have hreach : (ffc_offSupportLattice {p | p ∈ Vc.support}).Reachable z seed :=
    (ffc_reachable_iff_offSupportWalk hzB).mpr ⟨p, by intro w hw; simpa using hp w hw⟩
  exact hreach.symm







theorem jil_offSupportInterior_eq_floodFill {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseed : seed ∉ Vc.support) (hseedIn : seed ∈ jec_leftRegion Vc)
    (hlink : jil_RowLinked Vc seed) :
    jil_offSupportInterior Vc = ffc_floodFill {p | p ∈ Vc.support} seed :=
  Set.Subset.antisymm (jil_offSupportInterior_subset_floodFill Vc hlink)
    (jil_floodFill_subset_offSupportInterior Vc hseed hseedIn)






















def jil_interiorStepGraph {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    SimpleGraph (jil_offSupportInterior Vc) :=
  (hypercubicLattice 2).induce (jil_offSupportInterior Vc)





theorem jil_stepGraph_walk_offSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : jil_offSupportInterior Vc}
    (w : (jil_interiorStepGraph Vc).Walk x y) :
    ∃ p : (hypercubicLattice 2).Walk (x : Site 2) (y : Site 2), ∀ z ∈ p.support, z ∉ Vc.support := by
  classical
  induction w with
  | @nil u => exact ⟨SimpleGraph.Walk.nil, by
      intro z hz
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      subst hz
      exact (jil_mem_offSupportInterior Vc (u : Site 2) |>.mp u.2).1⟩
  | @cons u v t hadj q ih =>
    obtain ⟨p, hp⟩ := ih
    have hadj' : (hypercubicLattice 2).Adj (u : Site 2) (v : Site 2) := by
      rw [jil_interiorStepGraph] at hadj
      exact SimpleGraph.induce_adj.mp hadj
    have huoff : (u : Site 2) ∉ Vc.support :=
      (jil_mem_offSupportInterior Vc (u : Site 2) |>.mp u.2).1
    refine ⟨SimpleGraph.Walk.cons hadj' p, ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with h | h
    · subst h; exact huoff
    · exact hp z h






theorem jil_rowLinked_of_stepReachable {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseedI : seed ∈ jil_offSupportInterior Vc)
    (hstep : ∀ z : jil_offSupportInterior Vc,
      (jil_interiorStepGraph Vc).Reachable z ⟨seed, hseedI⟩) :
    jil_RowLinked Vc seed := by
  intro z hz
  obtain ⟨w⟩ := hstep ⟨z, hz⟩
  exact jil_stepGraph_walk_offSupport Vc w




theorem jil_stepGraph_horizontal_adj {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : ℤ} (hu : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hv : (![x + 1, y] : Site 2) ∈ jil_offSupportInterior Vc) :
    (jil_interiorStepGraph Vc).Adj ⟨![x, y], hu⟩ ⟨![x + 1, y], hv⟩ := by
  rw [jil_interiorStepGraph, SimpleGraph.induce_adj]
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp





theorem jil_stepGraph_vertical_adj {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : ℤ} (hu : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hv : (![x, y + 1] : Site 2) ∈ jil_offSupportInterior Vc) :
    (jil_interiorStepGraph Vc).Adj ⟨![x, y], hu⟩ ⟨![x, y + 1], hv⟩ := by
  rw [jil_interiorStepGraph, SimpleGraph.induce_adj]
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp

end Lattice

end StatMech
