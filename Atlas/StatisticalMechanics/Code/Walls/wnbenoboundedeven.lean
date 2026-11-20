/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



























import Mathlib
import Code.Lattice.InsideConnected
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.StraightWalk

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

variable {a : Site 2}




theorem wnbe_component_offSupport (Vc : (hypercubicLattice 2).Walk a a) {seed z : Site 2}
    (hseed : seed ∉ Vc.support) (hz : z ∈ offSupportComponent Vc seed) : z ∉ Vc.support := by
  rw [mem_offSupportComponent] at hz
  obtain ⟨p⟩ := hz
  exact offSupport_walk_support_offSupport Vc p hseed z p.end_mem_support






theorem wnbe_component_boundary_onSupport (Vc : (hypercubicLattice 2).Walk a a)
    {seed z w : Site 2} (hseed : seed ∉ Vc.support)
    (hz : z ∈ offSupportComponent Vc seed)
    (hadj : (hypercubicLattice 2).Adj z w) (hw : w ∉ offSupportComponent Vc seed) :
    w ∈ Vc.support := by
  by_contra hwoff
  apply hw
  have hzoff : z ∉ Vc.support := wnbe_component_offSupport Vc hseed hz
  have hadj' : (offSupport Vc).Adj z w := ⟨hadj, hzoff, hwoff⟩
  rw [mem_offSupportComponent] at hz ⊢
  exact hz.trans hadj'.reachable



theorem wnbe_neighbour_dichotomy (Vc : (hypercubicLattice 2).Walk a a)
    {seed z w : Site 2} (hseed : seed ∉ Vc.support)
    (hz : z ∈ offSupportComponent Vc seed) (hadj : (hypercubicLattice 2).Adj z w) :
    w ∈ offSupportComponent Vc seed ∨ w ∈ Vc.support := by
  by_cases hw : w ∈ offSupportComponent Vc seed
  · exact Or.inl hw
  · exact Or.inr (wnbe_component_boundary_onSupport Vc hseed hz hadj hw)





theorem wnbe_adjacent_same_component (Vc : (hypercubicLattice 2).Walk a a)
    {seed z w : Site 2} (hseed : seed ∉ Vc.support)
    (hz : z ∈ offSupportComponent Vc seed) (hadj : (hypercubicLattice 2).Adj z w)
    (hwoff : w ∉ Vc.support) : w ∈ offSupportComponent Vc seed := by
  have hzoff : z ∉ Vc.support := wnbe_component_offSupport Vc hseed hz
  have hadj' : (offSupport Vc).Adj z w := ⟨hadj, hzoff, hwoff⟩
  rw [mem_offSupportComponent] at hz ⊢
  exact hz.trans hadj'.reachable





theorem wnbe_distinct_components_support_separated (Vc : (hypercubicLattice 2).Walk a a)
    {s₁ s₂ z w : Site 2} (h₁ : s₁ ∉ Vc.support) (h₂ : s₂ ∉ Vc.support)
    (hz : z ∈ offSupportComponent Vc s₁) (hw : w ∈ offSupportComponent Vc s₂)
    (hadj : (hypercubicLattice 2).Adj z w) (hwoff : w ∉ Vc.support)
    (hne : offSupportComponent Vc s₁ ≠ offSupportComponent Vc s₂) : False := by
  have hwin : w ∈ offSupportComponent Vc s₁ := wnbe_adjacent_same_component Vc h₁ hz hadj hwoff
  
  apply hne
  ext u
  simp only [mem_offSupportComponent] at hz hw hwin ⊢
  constructor
  · intro hu; exact hw.trans (hwin.symm.trans hu)
  · intro hu; exact hwin.trans (hw.symm.trans hu)













theorem wnbe_rayEdge_cells {z x y : Site 2} (h : jec_rayEdge z s(x, y)) :
    x 0 = y 0 ∧ x 0 ≤ z 0 - 1 ∧
      ((x 1 = z 1 - 1 ∧ y 1 = z 1) ∨ (x 1 = z 1 ∧ y 1 = z 1 - 1)) := by
  rw [jec_rayEdge_mk] at h
  obtain ⟨⟨h0, hle⟩, hcase⟩ := h
  refine ⟨h0, hle, ?_⟩
  rcases hcase with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · exact Or.inl ⟨hx, hy⟩
  · exact Or.inr ⟨hx, hy⟩





theorem wnbe_rayCount_zero_of_noLeftSupport (Vc : (hypercubicLattice 2).Walk a a) {z : Site 2}
    (hno : ∀ c : ℤ, c < z 0 →
      (![c, z 1] : Site 2) ∉ Vc.support ∧ (![c, z 1 - 1] : Site 2) ∉ Vc.support) :
    jec_rayCount z Vc = 0 := by
  classical
  rw [jec_rayCount, List.countP_eq_zero]
  intro e he
  simp only [decide_eq_true_eq]
  induction e with
  | h x y =>
    intro hray
    have hcells := wnbe_rayEdge_cells hray
    obtain ⟨h0, hle, hcase⟩ := hcells
    have hx : x ∈ Vc.support := Vc.fst_mem_support_of_mem_edges he
    have hy : y ∈ Vc.support := Vc.snd_mem_support_of_mem_edges he
    have hc : x 0 < z 0 := by omega
    rcases hcase with ⟨hx1, hy1⟩ | ⟨hx1, hy1⟩
    · 
      have hyeq : y = ![x 0, z 1] := by
        funext i; fin_cases i
        · simpa using h0.symm
        · simpa using hy1
      exact (hno (x 0) hc).1 (hyeq ▸ hy)
    · 
      have hxeq : x = ![x 0, z 1] := by
        funext i; fin_cases i
        · simp
        · simpa using hx1
      exact (hno (x 0) hc).1 (hxeq ▸ hx)




theorem wnbe_notInterior_of_noLeftSupport (Vc : (hypercubicLattice 2).Walk a a) {z : Site 2}
    (hno : ∀ c : ℤ, c < z 0 →
      (![c, z 1] : Site 2) ∉ Vc.support ∧ (![c, z 1 - 1] : Site 2) ∉ Vc.support) :
    z ∉ jec_leftRegion Vc := by
  rw [jec_mem_leftRegion, not_not]
  rw [wnbe_rayCount_zero_of_noLeftSupport Vc hno]
  exact ⟨0, rfl⟩




theorem wnbe_interior_hasLeftSupport (Vc : (hypercubicLattice 2).Walk a a) {z : Site 2}
    (hz : z ∈ jec_leftRegion Vc) :
    ∃ c : ℤ, c < z 0 ∧
      ((![c, z 1] : Site 2) ∈ Vc.support ∨ (![c, z 1 - 1] : Site 2) ∈ Vc.support) := by
  by_contra hcon
  push_neg at hcon
  exact wnbe_notInterior_of_noLeftSupport Vc hcon hz










theorem wnbe_horizRun_reachable (Vc : (hypercubicLattice 2).Walk a a) (y x0 x1 : ℤ)
    (hoff : ∀ t : ℤ, t ∈ Set.uIcc x0 x1 → (![t, y] : Site 2) ∉ Vc.support) :
    (offSupport Vc).Reachable (![x0, y] : Site 2) ![x1, y] := by
  classical
  have hedge : ∀ e ∈ (sw_horizSeg y x0 x1).edges, e ∈ (offSupport Vc).edgeSet := by
    intro e
    induction e with
    | h u v =>
      intro he
      have hadj : (hypercubicLattice 2).Adj u v := by
        have := (sw_horizSeg y x0 x1).edges_subset_edgeSet he
        rwa [SimpleGraph.mem_edgeSet] at this
      have huS : u ∈ (sw_horizSeg y x0 x1).support :=
        (sw_horizSeg y x0 x1).fst_mem_support_of_mem_edges he
      have hvS : v ∈ (sw_horizSeg y x0 x1).support :=
        (sw_horizSeg y x0 x1).snd_mem_support_of_mem_edges he
      obtain ⟨tu, htu, rfl⟩ := (sw_horizSeg_mem_support y x0 x1 u).mp huS
      obtain ⟨tv, htv, rfl⟩ := (sw_horizSeg_mem_support y x0 x1 v).mp hvS
      rw [SimpleGraph.mem_edgeSet, offSupport_adj]
      exact ⟨hadj, hoff tu htu, hoff tv htv⟩
  exact ⟨(sw_horizSeg y x0 x1).transfer (offSupport Vc) hedge⟩



theorem wnbe_vertRun_reachable (Vc : (hypercubicLattice 2).Walk a a) (x y0 y1 : ℤ)
    (hoff : ∀ t : ℤ, t ∈ Set.uIcc y0 y1 → (![x, t] : Site 2) ∉ Vc.support) :
    (offSupport Vc).Reachable (![x, y0] : Site 2) ![x, y1] := by
  classical
  have hedge : ∀ e ∈ (sw_vertSeg x y0 y1).edges, e ∈ (offSupport Vc).edgeSet := by
    intro e
    induction e with
    | h u v =>
      intro he
      have hadj : (hypercubicLattice 2).Adj u v := by
        have := (sw_vertSeg x y0 y1).edges_subset_edgeSet he
        rwa [SimpleGraph.mem_edgeSet] at this
      have huS : u ∈ (sw_vertSeg x y0 y1).support :=
        (sw_vertSeg x y0 y1).fst_mem_support_of_mem_edges he
      have hvS : v ∈ (sw_vertSeg x y0 y1).support :=
        (sw_vertSeg x y0 y1).snd_mem_support_of_mem_edges he
      obtain ⟨tu, htu, rfl⟩ := (sw_vertSeg_mem_support x y0 y1 u).mp huS
      obtain ⟨tv, htv, rfl⟩ := (sw_vertSeg_mem_support x y0 y1 v).mp hvS
      rw [SimpleGraph.mem_edgeSet, offSupport_adj]
      exact ⟨hadj, hoff tu htu, hoff tv htv⟩
  exact ⟨(sw_vertSeg x y0 y1).transfer (offSupport Vc) hedge⟩




theorem wnbe_horizRun_sameComponent (Vc : (hypercubicLattice 2).Walk a a) {seed : Site 2}
    {y x0 x1 : ℤ} (hoff : ∀ t : ℤ, t ∈ Set.uIcc x0 x1 → (![t, y] : Site 2) ∉ Vc.support)
    (hz : (![x0, y] : Site 2) ∈ offSupportComponent Vc seed) :
    (![x1, y] : Site 2) ∈ offSupportComponent Vc seed := by
  rw [mem_offSupportComponent] at hz ⊢
  exact hz.trans (wnbe_horizRun_reachable Vc y x0 x1 hoff)




theorem wnbe_horizRun_sameLeftRegion (Vc : (hypercubicLattice 2).Walk a a) {y x0 x1 : ℤ}
    (hoff : ∀ t : ℤ, t ∈ Set.uIcc x0 x1 → (![t, y] : Site 2) ∉ Vc.support) :
    ((![x0, y] : Site 2) ∈ jec_leftRegion Vc) ↔ ((![x1, y] : Site 2) ∈ jec_leftRegion Vc) := by
  have hx0 : (![x0, y] : Site 2) ∉ Vc.support := hoff x0 Set.left_mem_uIcc
  exact inside_sameRegion_offSupport Vc (wnbe_horizRun_reachable Vc y x0 x1 hoff) hx0


theorem wnbe_vertRun_sameLeftRegion (Vc : (hypercubicLattice 2).Walk a a) {x y0 y1 : ℤ}
    (hoff : ∀ t : ℤ, t ∈ Set.uIcc y0 y1 → (![x, t] : Site 2) ∉ Vc.support) :
    ((![x, y0] : Site 2) ∈ jec_leftRegion Vc) ↔ ((![x, y1] : Site 2) ∈ jec_leftRegion Vc) := by
  have hy0 : (![x, y0] : Site 2) ∉ Vc.support := hoff y0 Set.left_mem_uIcc
  exact inside_sameRegion_offSupport Vc (wnbe_vertRun_reachable Vc x y0 y1 hoff) hy0





theorem wnbe_LPath_reachable (Vc : (hypercubicLattice 2).Walk a a) (x0 y0 x1 y1 : ℤ)
    (hhor : ∀ t : ℤ, t ∈ Set.uIcc x0 x1 → (![t, y0] : Site 2) ∉ Vc.support)
    (hver : ∀ t : ℤ, t ∈ Set.uIcc y0 y1 → (![x1, t] : Site 2) ∉ Vc.support) :
    (offSupport Vc).Reachable (![x0, y0] : Site 2) ![x1, y1] :=
  (wnbe_horizRun_reachable Vc y0 x0 x1 hhor).trans (wnbe_vertRun_reachable Vc x1 y0 y1 hver)



theorem wnbe_LPath_sameComponent (Vc : (hypercubicLattice 2).Walk a a) {seed : Site 2}
    {x0 y0 x1 y1 : ℤ}
    (hhor : ∀ t : ℤ, t ∈ Set.uIcc x0 x1 → (![t, y0] : Site 2) ∉ Vc.support)
    (hver : ∀ t : ℤ, t ∈ Set.uIcc y0 y1 → (![x1, t] : Site 2) ∉ Vc.support)
    (hz : (![x0, y0] : Site 2) ∈ offSupportComponent Vc seed) :
    (![x1, y1] : Site 2) ∈ offSupportComponent Vc seed := by
  rw [mem_offSupportComponent] at hz ⊢
  exact hz.trans (wnbe_LPath_reachable Vc x0 y0 x1 y1 hhor hver)










theorem wnbe_clearRight_reachesExterior (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) {z : Site 2}
    (hclear : ∀ t : ℤ, t ∈ Set.uIcc (z 0) ((R : ℤ) + 1) → (![t, z 1] : Site 2) ∉ Vc.support) :
    (offSupport Vc).Reachable z (![(R : ℤ) + 1, z 1] : Site 2) := by
  have hz : z = (![z 0, z 1] : Site 2) := by funext i; fin_cases i <;> rfl
  rw [hz]
  exact wnbe_horizRun_reachable Vc (z 1) (z 0) ((R : ℤ) + 1) hclear





theorem wnbe_escapable_component_meets_exterior (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    {seed z : Site 2}
    (hclear : ∀ t : ℤ, t ∈ Set.uIcc (z 0) ((R : ℤ) + 1) → (![t, z 1] : Site 2) ∉ Vc.support)
    (hz : z ∈ offSupportComponent Vc seed) :
    (![(R : ℤ) + 1, z 1] : Site 2) ∈ offSupportComponent Vc seed := by
  rw [mem_offSupportComponent] at hz ⊢
  exact hz.trans (wnbe_clearRight_reachesExterior Vc R hclear)


theorem wnbe_clearLeft_reachesExterior (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) {z : Site 2}
    (hclear : ∀ t : ℤ, t ∈ Set.uIcc (z 0) (-(R : ℤ) - 1) → (![t, z 1] : Site 2) ∉ Vc.support) :
    (offSupport Vc).Reachable z (![-(R : ℤ) - 1, z 1] : Site 2) := by
  have hz : z = (![z 0, z 1] : Site 2) := by funext i; fin_cases i <;> rfl
  rw [hz]
  exact wnbe_horizRun_reachable Vc (z 1) (z 0) (-(R : ℤ) - 1) hclear


theorem wnbe_clearUp_reachesExterior (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) {z : Site 2}
    (hclear : ∀ t : ℤ, t ∈ Set.uIcc (z 1) ((R : ℤ) + 1) → (![z 0, t] : Site 2) ∉ Vc.support) :
    (offSupport Vc).Reachable z (![z 0, (R : ℤ) + 1] : Site 2) := by
  have hz : z = (![z 0, z 1] : Site 2) := by funext i; fin_cases i <;> rfl
  rw [hz]
  exact wnbe_vertRun_reachable Vc (z 0) (z 1) ((R : ℤ) + 1) hclear


theorem wnbe_clearDown_reachesExterior (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) {z : Site 2}
    (hclear : ∀ t : ℤ, t ∈ Set.uIcc (z 1) (-(R : ℤ) - 1) → (![z 0, t] : Site 2) ∉ Vc.support) :
    (offSupport Vc).Reachable z (![z 0, -(R : ℤ) - 1] : Site 2) := by
  have hz : z = (![z 0, z 1] : Site 2) := by funext i; fin_cases i <;> rfl
  rw [hz]
  exact wnbe_vertRun_reachable Vc (z 0) (z 1) (-(R : ℤ) - 1) hclear

end Lattice

end StatMech
