/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































































import Code.Walls.rc78hallmarriage

set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}








def rc79_topType : Fin n → Bool × Bool := fun _ => (false, true)



theorem rc79_mixed_iff_ne (b₁ b₂ : Bool) :
    (b₁ && b₂, b₁ || b₂) = ((false, true) : Bool × Bool) ↔ b₁ ≠ b₂ := by
  cases b₁ <;> cases b₂ <;> simp



theorem rc79_colType_top_iff (p : ConfigSpace (Fin n) × ConfigSpace (Fin n)) :
    rc78_colType p = rc79_topType ↔ ∀ i, p.1 i ≠ p.2 i := by
  unfold rc78_colType rc79_topType
  rw [funext_iff]
  constructor
  · intro h i
    exact (rc79_mixed_iff_ne (p.1 i) (p.2 i)).mp (h i)
  · intro h i
    exact (rc79_mixed_iff_ne (p.1 i) (p.2 i)).mpr (h i)











def rc79_diagTypeF (w : ConfigSpace (Fin 2)) : Fin 2 → Bool × Bool :=
  fun i => (w i, w i)



theorem rc79_colTypeF_diag_iff (p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :
    rc78_colTypeF p = rc79_diagTypeF p.1 ↔ p.1 = p.2 := by
  unfold rc78_colTypeF rc79_diagTypeF
  rw [funext_iff]
  constructor
  · intro h; funext i
    have := h i
    rw [Prod.mk.injEq] at this
    
    obtain ⟨h1, h2⟩ := this
    cases hp1 : p.1 i <;> cases hp2 : p.2 i <;> simp_all
  · intro h i
    rw [h]
    cases (p.2 i) <;> simp


theorem rc79_occ_self_mem {A : Finset (ConfigSpace (Fin 2))} {K : Finset (Fin 2)}
    {w : ConfigSpace (Fin 2)} (h : rc75_occ A K w = true) : w ∈ A := by
  unfold rc75_occ at h
  rw [decide_eq_true_eq] at h
  exact h w (fun e _ => rfl)



theorem rc79_disjOcc_mem_both {A B : Finset (ConfigSpace (Fin 2))} {w : ConfigSpace (Fin 2)}
    (h : w ∈ rc75_disjOccF A B) : w ∈ A ∧ w ∈ B := by
  unfold rc75_disjOccF at h
  rw [Finset.mem_filter] at h
  obtain ⟨_, K, L, _, hA, hB⟩ := h
  exact ⟨rc79_occ_self_mem hA, rc79_occ_self_mem hB⟩






theorem rc79_diag_orbit_dominates (A B : Finset (ConfigSpace (Fin 2))) (w : ConfigSpace (Fin 2)) :
    rc78_srcOrbit A B (rc79_diagTypeF w) ⊆ rc78_tgtOrbit A B (rc79_diagTypeF w) := by
  intro p hp
  rw [rc78_srcOrbit, Finset.mem_filter] at hp
  obtain ⟨hpsrc, hptype⟩ := hp
  
  rw [rc75_sourceF, Finset.mem_product] at hpsrc
  obtain ⟨hp1, _⟩ := hpsrc
  
  
  have hdiag_p1 : rc78_colTypeF p = rc79_diagTypeF p.1 := by
    funext i
    have := congrArg (fun f => f i) hptype
    
    simp only [rc79_diagTypeF] at this ⊢
    unfold rc78_colTypeF at this ⊢
    
    rw [Prod.mk.injEq] at this
    obtain ⟨h1, h2⟩ := this
    cases hp1' : p.1 i <;> cases hp2' : p.2 i <;> simp_all
  have hp1eqp2 : p.1 = p.2 := (rc79_colTypeF_diag_iff p).mp hdiag_p1
  
  obtain ⟨hA, hB⟩ := rc79_disjOcc_mem_both hp1
  rw [rc78_tgtOrbit, Finset.mem_filter]
  refine ⟨?_, hptype⟩
  rw [rc75_prodF, Finset.mem_product]
  exact ⟨hA, by rw [← hp1eqp2]; exact hB⟩


theorem rc79_diag_orbit_card_le (A B : Finset (ConfigSpace (Fin 2))) (w : ConfigSpace (Fin 2)) :
    (rc78_srcOrbit A B (rc79_diagTypeF w)).card ≤ (rc78_tgtOrbit A B (rc79_diagTypeF w)).card :=
  Finset.card_le_card (rc79_diag_orbit_dominates A B w)















def rc79_topTypeF : Fin 2 → Bool × Bool := fun _ => (false, true)


def rc79_complF (w : ConfigSpace (Fin 2)) : ConfigSpace (Fin 2) := fun i => !w i



def rc79_reflInterF (A B : Finset (ConfigSpace (Fin 2))) : Finset (ConfigSpace (Fin 2)) :=
  A.filter (fun a => rc79_complF a ∈ B)



theorem rc79_colTypeF_top_iff (p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :
    rc78_colTypeF p = rc79_topTypeF ↔ ∀ i, p.1 i ≠ p.2 i := by
  unfold rc78_colTypeF rc79_topTypeF
  rw [funext_iff]
  constructor
  · intro h i; exact (rc79_mixed_iff_ne (p.1 i) (p.2 i)).mp (h i)
  · intro h i; exact (rc79_mixed_iff_ne (p.1 i) (p.2 i)).mpr (h i)


theorem rc79_colTypeF_top_iff_compl (p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :
    rc78_colTypeF p = rc79_topTypeF ↔ p.2 = rc79_complF p.1 := by
  rw [rc79_colTypeF_top_iff]
  constructor
  · intro h; funext i; unfold rc79_complF
    have := h i; cases hp1 : p.1 i <;> cases hp2 : p.2 i <;> simp_all
  · intro h i; rw [h]; unfold rc79_complF; cases (p.1 i) <;> simp





theorem rc79_srcOrbit_top_card (A B : Finset (ConfigSpace (Fin 2))) :
    (rc78_srcOrbit A B rc79_topTypeF).card = (rc75_disjOccF A B).card := by
  apply Finset.card_bij (fun p _ => p.1)
  · 
    intro p hp
    rw [rc78_srcOrbit, Finset.mem_filter, rc75_sourceF, Finset.mem_product] at hp
    exact hp.1.1
  · 
    intro p hp q hq h
    rw [rc78_srcOrbit, Finset.mem_filter] at hp hq
    have hp2 := (rc79_colTypeF_top_iff_compl p).mp hp.2
    have hq2 := (rc79_colTypeF_top_iff_compl q).mp hq.2
    apply Prod.ext h
    rw [hp2, hq2, h]
  · 
    intro w hw
    refine ⟨(w, rc79_complF w), ?_, rfl⟩
    rw [rc78_srcOrbit, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [rc75_sourceF, Finset.mem_product]; exact ⟨hw, Finset.mem_univ _⟩
    · rw [rc79_colTypeF_top_iff_compl]




theorem rc79_tgtOrbit_top_card (A B : Finset (ConfigSpace (Fin 2))) :
    (rc78_tgtOrbit A B rc79_topTypeF).card = (rc79_reflInterF A B).card := by
  apply Finset.card_bij (fun p _ => p.1)
  · 
    intro p hp
    rw [rc78_tgtOrbit, Finset.mem_filter, rc75_prodF, Finset.mem_product] at hp
    rw [rc79_reflInterF, Finset.mem_filter]
    refine ⟨hp.1.1, ?_⟩
    have hp2 := (rc79_colTypeF_top_iff_compl p).mp hp.2
    rw [← hp2]; exact hp.1.2
  · intro p hp q hq h
    rw [rc78_tgtOrbit, Finset.mem_filter] at hp hq
    have hp2 := (rc79_colTypeF_top_iff_compl p).mp hp.2
    have hq2 := (rc79_colTypeF_top_iff_compl q).mp hq.2
    apply Prod.ext h
    rw [hp2, hq2, h]
  · intro a ha
    rw [rc79_reflInterF, Finset.mem_filter] at ha
    refine ⟨(a, rc79_complF a), ?_, rfl⟩
    rw [rc78_tgtOrbit, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [rc75_prodF, Finset.mem_product]; exact ⟨ha.1, ha.2⟩
    · rw [rc79_colTypeF_top_iff_compl]





theorem rc79_top_orbit_is_wall (A B : Finset (ConfigSpace (Fin 2))) :
    ((rc78_srcOrbit A B rc79_topTypeF).card ≤ (rc78_tgtOrbit A B rc79_topTypeF).card)
      ↔ ((rc75_disjOccF A B).card ≤ (rc79_reflInterF A B).card) := by
  rw [rc79_srcOrbit_top_card, rc79_tgtOrbit_top_card]








set_option maxRecDepth 8000 in



theorem rc79_top_wall_rc72_witness :
    (rc75_disjOccF rc75_wA rc75_wB).card = 2 ∧ (rc79_reflInterF rc75_wA rc75_wB).card = 2 := by
  refine ⟨?_, ?_⟩ <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in 



theorem rc79_top_wall_fin2 :
    ∀ A B : Finset (ConfigSpace (Fin 2)),
      (rc75_disjOccF A B).card ≤ (rc79_reflInterF A B).card := by
  decide














theorem rc79_perOrbitDom_fin2 : ∀ A B : Finset (ConfigSpace (Fin 2)), rc78_PerOrbitDom A B :=
  rc78_perOrbitDom_fin2

















def rc79_occ3 (A : Finset (ConfigSpace (Fin 3))) (K : Finset (Fin 3)) (ω : ConfigSpace (Fin 3)) : Bool :=
  decide (∀ ω' : ConfigSpace (Fin 3), (∀ e ∈ K, ω' e = ω e) → ω' ∈ A)


def rc79_disjOcc3 (A B : Finset (ConfigSpace (Fin 3))) : Finset (ConfigSpace (Fin 3)) :=
  Finset.univ.filter (fun ω =>
    ∃ K L : Finset (Fin 3), Disjoint K L ∧ rc79_occ3 A K ω = true ∧ rc79_occ3 B L ω = true)


def rc79_disjOcc2 (A B : Finset (ConfigSpace (Fin 2))) : Finset (ConfigSpace (Fin 2)) :=
  rc75_disjOccF A B



def rc79_slice2 (val : Bool) (E : Finset (ConfigSpace (Fin 3))) : Finset (ConfigSpace (Fin 2)) :=
  (E.filter (fun ω => ω 2 = val)).image (fun ω => fun j : Fin 2 => ω j.castSucc)


def rc79_cfg3 (b0 b1 b2 : Bool) : ConfigSpace (Fin 3) :=
  fun i => if i = 0 then b0 else if i = 1 then b1 else b2


def rc79_rA : Finset (ConfigSpace (Fin 3)) :=
  {rc79_cfg3 false true false, rc79_cfg3 false true true, rc79_cfg3 true false true,
   rc79_cfg3 true true false, rc79_cfg3 true true true}


def rc79_rB : Finset (ConfigSpace (Fin 3)) :=
  {rc79_cfg3 false true false, rc79_cfg3 false true true, rc79_cfg3 true false false,
   rc79_cfg3 true true false, rc79_cfg3 true true true}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in 







theorem rc79_split_induction_refuted_fin3 :
    (rc79_disjOcc3 rc79_rA rc79_rB).card = 2
    ∧ (rc79_disjOcc2 (rc79_slice2 false rc79_rA) (rc79_slice2 true rc79_rB)).card
        + (rc79_disjOcc2 (rc79_slice2 true rc79_rA) (rc79_slice2 false rc79_rB)).card = 1
    ∧ ¬ (rc79_disjOcc3 rc79_rA rc79_rB).card
          ≤ (rc79_disjOcc2 (rc79_slice2 false rc79_rA) (rc79_slice2 true rc79_rB)).card
            + (rc79_disjOcc2 (rc79_slice2 true rc79_rA) (rc79_slice2 false rc79_rB)).card := by
  refine ⟨?_, ?_, ?_⟩ <;> decide



open Classical in



theorem rc79_reimerWprobCore_of_boxUnionBound (h : rc60_BoxUnionBound) : ReimerWprobCore :=
  rc78_reimerWprobCore_of_boxUnionBound h

open Classical in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in 































theorem rc79_status :
    
    (∀ (A B : Finset (ConfigSpace (Fin 2))) (w : ConfigSpace (Fin 2)),
        rc78_srcOrbit A B (rc79_diagTypeF w) ⊆ rc78_tgtOrbit A B (rc79_diagTypeF w)) ∧
    
    (∀ A B : Finset (ConfigSpace (Fin 2)),
        ((rc78_srcOrbit A B rc79_topTypeF).card ≤ (rc78_tgtOrbit A B rc79_topTypeF).card)
          ↔ ((rc75_disjOccF A B).card ≤ (rc79_reflInterF A B).card)) ∧
    
    (∀ A B : Finset (ConfigSpace (Fin 2)), rc78_PerOrbitDom A B) ∧
    
    (∀ A B : Finset (ConfigSpace (Fin 2)),
        (rc75_disjOccF A B).card ≤ (rc79_reflInterF A B).card) ∧
    
    (¬ (rc79_disjOcc3 rc79_rA rc79_rB).card
          ≤ (rc79_disjOcc2 (rc79_slice2 false rc79_rA) (rc79_slice2 true rc79_rB)).card
            + (rc79_disjOcc2 (rc79_slice2 true rc79_rA) (rc79_slice2 false rc79_rB)).card) ∧
    
    (rc60_BoxUnionBound → ReimerWprobCore) :=
  ⟨rc79_diag_orbit_dominates,
   rc79_top_orbit_is_wall,
   rc79_perOrbitDom_fin2,
   rc79_top_wall_fin2,
   rc79_split_induction_refuted_fin3.2.2,
   rc79_reimerWprobCore_of_boxUnionBound⟩

end StatMech.Walls
