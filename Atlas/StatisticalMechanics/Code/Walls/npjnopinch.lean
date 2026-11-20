/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












































































import Mathlib
import Code.Lattice.JordanEnclosureDuality
import Code.Lattice.JordanCoresUnify
import Code.Walls.dg2degree

open SimpleGraph Set

namespace StatMech

namespace Walls

open StatMech.Lattice

attribute [local instance] Classical.propDecidable




def npj_c00 (a b : ℤ) : Site 2 := ![a, b]
def npj_c10 (a b : ℤ) : Site 2 := ![a + 1, b]
def npj_c11 (a b : ℤ) : Site 2 := ![a + 1, b + 1]
def npj_c01 (a b : ℤ) : Site 2 := ![a, b + 1]










theorem npj_lift_walk (S : Set (Site 2)) {x y : S}
    (p : ((hypercubicLattice 2).induce S).Walk x y) :
    ∃ w : (hypercubicLattice 2).Walk (x : Site 2) (y : Site 2), ∀ z ∈ w.support, z ∈ S := by
  induction p with
  | nil =>
      exact ⟨Walk.nil, by
        intro z hz
        simp only [Walk.support_nil, List.mem_singleton] at hz
        subst hz; exact Subtype.property _⟩
  | @cons a b c hab p ih =>
      obtain ⟨w, hw⟩ := ih
      refine ⟨Walk.cons hab w, ?_⟩
      intro z hz
      rw [Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact Subtype.property _
      · exact hw z hz




theorem npj_ambient_walk_of_induce_reachable {S : Set (Site 2)} {x y : Site 2}
    (hx : x ∈ S) (hy : y ∈ S)
    (h : ((hypercubicLattice 2).induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩) :
    ∃ w : (hypercubicLattice 2).Walk x y, ∀ z ∈ w.support, z ∈ S := by
  obtain ⟨p⟩ := h
  exact npj_lift_walk S p











theorem npj_paths_of_diagSplit {K : Set (Site 2)} (a b : ℤ)
    (hK : ((hypercubicLattice 2).induce K).Connected)
    (hKc : ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Connected)
    (h00 : npj_c00 a b ∈ K) (h11 : npj_c11 a b ∈ K)
    (h10 : npj_c10 a b ∈ (Kᶜ : Set (Site 2))) (h01 : npj_c01 a b ∈ (Kᶜ : Set (Site 2))) :
    (∃ w : (hypercubicLattice 2).Walk (npj_c00 a b) (npj_c11 a b),
        ∀ z ∈ w.support, z ∈ K) ∧
    (∃ w : (hypercubicLattice 2).Walk (npj_c10 a b) (npj_c01 a b),
        ∀ z ∈ w.support, z ∈ (Kᶜ : Set (Site 2))) := by
  refine ⟨npj_ambient_walk_of_induce_reachable h00 h11 (hK.preconnected ⟨_, h00⟩ ⟨_, h11⟩),
          npj_ambient_walk_of_induce_reachable h10 h01 (hKc.preconnected ⟨_, h10⟩ ⟨_, h01⟩)⟩




















theorem npj_noPinch_primary_of_separatingSide {K : Set (Site 2)} (a b : ℤ)
    {wK : (hypercubicLattice 2).Walk (npj_c00 a b) (npj_c11 a b)}
    (hwK : ∀ z ∈ wK.support, z ∈ K)
    {wKc : (hypercubicLattice 2).Walk (npj_c10 a b) (npj_c01 a b)}
    (hwKc : ∀ z ∈ wKc.support, z ∈ (Kᶜ : Set (Site 2)))
    (hsep : jcu_HasSeparatingSide Set.univ {z | z ∈ wK.support}
              {npj_c10 a b} {npj_c01 a b}) :
    False := by
  obtain ⟨z, hzKc, hzK⟩ :=
    jcu_separatingSide_forces_cross hsep (rfl : npj_c10 a b ∈ ({npj_c10 a b} : Set _))
      (rfl : npj_c01 a b ∈ ({npj_c01 a b} : Set _)) wKc (fun z _ => Set.mem_univ z)
  
  exact (hwKc z hzKc) (hwK z hzK)





def npj_SeparatingSideResidue (a b : ℤ)
    (wK : (hypercubicLattice 2).Walk (npj_c00 a b) (npj_c11 a b)) : Prop :=
  jcu_HasSeparatingSide Set.univ {z | z ∈ wK.support} {npj_c10 a b} {npj_c01 a b}








theorem npj_noPinch_of_separatingSides {K : Set (Site 2)}
    (hK : ((hypercubicLattice 2).induce K).Connected)
    (hKc : ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Connected)
    (hres :
      ∀ (a b : ℤ),
        (npj_c00 a b ∈ K → npj_c11 a b ∈ K →
          npj_c10 a b ∈ (Kᶜ : Set (Site 2)) → npj_c01 a b ∈ (Kᶜ : Set (Site 2)) →
          ∀ wK : (hypercubicLattice 2).Walk (npj_c00 a b) (npj_c11 a b),
            (∀ z ∈ wK.support, z ∈ K) → npj_SeparatingSideResidue a b wK) ∧
        
        
        (npj_c10 a b ∈ K → npj_c01 a b ∈ K →
          npj_c00 a b ∈ (Kᶜ : Set (Site 2)) → npj_c11 a b ∈ (Kᶜ : Set (Site 2)) →
          ∀ wK : (hypercubicLattice 2).Walk (npj_c10 a b) (npj_c01 a b),
            (∀ z ∈ wK.support, z ∈ K) →
            jcu_HasSeparatingSide Set.univ {z | z ∈ wK.support}
              {npj_c00 a b} {npj_c11 a b})) :
    dg2_NoPinch K := by
  intro a b hchk
  rw [dg2_checker_iff_diagSplit] at hchk
  rcases hchk with ⟨h00, h11, h10, h01⟩ | ⟨h00, h11, h10, h01⟩
  · 
    have h10c : npj_c10 a b ∈ (Kᶜ : Set (Site 2)) := h10
    have h01c : npj_c01 a b ∈ (Kᶜ : Set (Site 2)) := h01
    obtain ⟨⟨wK, hwK⟩, ⟨wKc, hwKc⟩⟩ :=
      npj_paths_of_diagSplit a b hK hKc h00 h11 h10c h01c
    exact npj_noPinch_primary_of_separatingSide a b hwK hwKc
      ((hres a b).1 h00 h11 h10c h01c wK hwK)
  · 
    
    have h00c : npj_c00 a b ∈ (Kᶜ : Set (Site 2)) := h00
    have h11c : npj_c11 a b ∈ (Kᶜ : Set (Site 2)) := h11
    
    have hKwalk := npj_ambient_walk_of_induce_reachable (S := K) h10 h01
      (hK.preconnected ⟨_, h10⟩ ⟨_, h01⟩)
    have hKcwalk := npj_ambient_walk_of_induce_reachable (S := (Kᶜ : Set (Site 2))) h00c h11c
      (hKc.preconnected ⟨_, h00c⟩ ⟨_, h11c⟩)
    obtain ⟨wK, hwK⟩ := hKwalk
    obtain ⟨wKc, hwKc⟩ := hKcwalk
    have hsep := (hres a b).2 h10 h01 h00c h11c wK hwK
    obtain ⟨z, hzKc, hzK⟩ :=
      jcu_separatingSide_forces_cross hsep (rfl : npj_c00 a b ∈ ({npj_c00 a b} : Set _))
        (rfl : npj_c11 a b ∈ ({npj_c11 a b} : Set _)) wKc (fun z _ => Set.mem_univ z)
    exact (hwKc z hzKc) (hwK z hzK)






























theorem npj_jed_faceCut_even (T : Site 2 → Prop) (v : Site 2) :
    Even (jce_degree (jed_cutSet T) v) :=
  jed_cutSet_even T v





theorem npj_jed_faceSeparation (H : SimpleGraph (Site 2)) (hfin : H.edgeSet.Finite)
    (p q f0 g0 : Site 2) (hpq : (hypercubicLattice 2).Adj p q) (hnpq : s(p, q) ∉ H.edgeSet)
    (hfg : (hypercubicLattice 2).Adj f0 g0) (hshared : sharedPrimalEdge f0 g0 = s(p, q))
    (hsep : ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0) :
    H.Reachable p q :=
  jed_reachable_of_separated H hfin p q f0 g0 hpq hnpq hfg hshared hsep

















theorem npj_jed_mismatch :
    (∀ (T : Site 2 → Prop) (v : Site 2), Even (jce_degree (jed_cutSet T) v)) ∧
    (∀ (H : SimpleGraph (Site 2)), H.edgeSet.Finite → ∀ (p q f0 g0 : Site 2),
        (hypercubicLattice 2).Adj p q → s(p, q) ∉ H.edgeSet →
        (hypercubicLattice 2).Adj f0 g0 → sharedPrimalEdge f0 g0 = s(p, q) →
        ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0 → H.Reachable p q) ∧
    (∀ {K : Set (Site 2)},
      ((hypercubicLattice 2).induce K).Connected →
      ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Connected →
      (∀ (a b : ℤ),
        (npj_c00 a b ∈ K → npj_c11 a b ∈ K →
          npj_c10 a b ∈ (Kᶜ : Set (Site 2)) → npj_c01 a b ∈ (Kᶜ : Set (Site 2)) →
          ∀ wK : (hypercubicLattice 2).Walk (npj_c00 a b) (npj_c11 a b),
            (∀ z ∈ wK.support, z ∈ K) → npj_SeparatingSideResidue a b wK) ∧
        (npj_c10 a b ∈ K → npj_c01 a b ∈ K →
          npj_c00 a b ∈ (Kᶜ : Set (Site 2)) → npj_c11 a b ∈ (Kᶜ : Set (Site 2)) →
          ∀ wK : (hypercubicLattice 2).Walk (npj_c10 a b) (npj_c01 a b),
            (∀ z ∈ wK.support, z ∈ K) →
            jcu_HasSeparatingSide Set.univ {z | z ∈ wK.support}
              {npj_c00 a b} {npj_c11 a b})) →
      dg2_NoPinch K) :=
  ⟨npj_jed_faceCut_even, npj_jed_faceSeparation,
    fun hK hKc hres => npj_noPinch_of_separatingSides hK hKc hres⟩














theorem npj_pinch_no_origin_neighbour {w : Site 2}
    (hadj : (hypercubicLattice 2).Adj (npj_c00 0 0) w) : w ∉ dg2_pinchSet := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  simp only [npj_c00, Matrix.cons_val_zero, Matrix.cons_val_one] at hadj
  intro hw
  have hwe : w = ![w 0, w 1] := by funext i; fin_cases i <;> rfl
  rw [hwe, dg2_mem_pinchSet] at hw
  
  rcases hw with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega







theorem npj_pinch_consistent :
    ¬ ∃ w : (hypercubicLattice 2).Walk (npj_c00 0 0) (npj_c11 0 0),
        ∀ z ∈ w.support, z ∈ dg2_pinchSet := by
  rintro ⟨w, hw⟩
  
  have hne : (npj_c00 0 0 : Site 2) ≠ npj_c11 0 0 := by
    intro h
    have h0 := congrFun h 0
    simp only [npj_c00, npj_c11, Matrix.cons_val_zero] at h0
    omega
  obtain ⟨b, hab, p, rfl⟩ := Walk.exists_eq_cons_of_ne hne w
  have hbK : b ∈ dg2_pinchSet := hw b (by
    rw [Walk.support_cons, List.mem_cons]; right; simp)
  exact (npj_pinch_no_origin_neighbour hab) hbK




theorem npj_box_noPinch (x0 x1 y0 y1 : ℤ) :
    dg2_NoPinch {p : Site 2 | x0 ≤ p 0 ∧ p 0 ≤ x1 ∧ y0 ≤ p 1 ∧ p 1 ≤ y1} :=
  dg2_boxPred_noPinch x0 x1 y0 y1





theorem npj_extraction_applicable {K : Set (Site 2)} (a b : ℤ)
    (hK : ((hypercubicLattice 2).induce K).Connected)
    (hKc : ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Connected)
    (h00 : npj_c00 a b ∈ K) (h11 : npj_c11 a b ∈ K)
    (h10 : npj_c10 a b ∈ (Kᶜ : Set (Site 2))) (h01 : npj_c01 a b ∈ (Kᶜ : Set (Site 2))) :
    (∃ w : (hypercubicLattice 2).Walk (npj_c00 a b) (npj_c11 a b), ∀ z ∈ w.support, z ∈ K) ∧
    (∃ w : (hypercubicLattice 2).Walk (npj_c10 a b) (npj_c01 a b),
        ∀ z ∈ w.support, z ∈ (Kᶜ : Set (Site 2))) :=
  npj_paths_of_diagSplit a b hK hKc h00 h11 h10 h01

























theorem npj_status :
    (∀ {K : Set (Site 2)},
      ((hypercubicLattice 2).induce K).Connected →
      ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Connected →
      (∀ (a b : ℤ),
        (npj_c00 a b ∈ K → npj_c11 a b ∈ K →
          npj_c10 a b ∈ (Kᶜ : Set (Site 2)) → npj_c01 a b ∈ (Kᶜ : Set (Site 2)) →
          ∀ wK : (hypercubicLattice 2).Walk (npj_c00 a b) (npj_c11 a b),
            (∀ z ∈ wK.support, z ∈ K) → npj_SeparatingSideResidue a b wK) ∧
        (npj_c10 a b ∈ K → npj_c01 a b ∈ K →
          npj_c00 a b ∈ (Kᶜ : Set (Site 2)) → npj_c11 a b ∈ (Kᶜ : Set (Site 2)) →
          ∀ wK : (hypercubicLattice 2).Walk (npj_c10 a b) (npj_c01 a b),
            (∀ z ∈ wK.support, z ∈ K) →
            jcu_HasSeparatingSide Set.univ {z | z ∈ wK.support}
              {npj_c00 a b} {npj_c11 a b})) →
      dg2_NoPinch K) ∧
    (∀ (T : Site 2 → Prop) (v : Site 2), Even (jce_degree (jed_cutSet T) v)) ∧
    (¬ ∃ w : (hypercubicLattice 2).Walk (npj_c00 0 0) (npj_c11 0 0),
        ∀ z ∈ w.support, z ∈ dg2_pinchSet) :=
  ⟨fun hK hKc hres => npj_noPinch_of_separatingSides hK hKc hres,
    npj_jed_faceCut_even, npj_pinch_consistent⟩

end Walls

end StatMech
