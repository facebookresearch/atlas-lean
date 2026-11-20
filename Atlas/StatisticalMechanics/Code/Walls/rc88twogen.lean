/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































































import Code.Walls.rc87extra

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option maxHeartbeats 800000

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]




theorem rc88_occ_pair_self_mem (a b : ConfigSpace ι) (K : Finset ι) (w : ConfigSpace ι)
    (h : rc80_occ ({a, b} : Finset (ConfigSpace ι)) K w = true) : w = a ∨ w = b := by
  unfold rc80_occ at h
  rw [decide_eq_true_eq] at h
  have := h w (fun _ _ => rfl)
  rwa [Finset.mem_insert, Finset.mem_singleton] at this



theorem rc88_occ_mem_of_agree (B : Finset (ConfigSpace ι)) (L : Finset ι) (w x : ConfigSpace ι)
    (h : rc80_occ B L w = true) (hx : ∀ e ∈ L, x e = w e) : x ∈ B := by
  unfold rc80_occ at h
  rw [decide_eq_true_eq] at h
  exact h x hx



theorem rc88_disjOccG_pair_subset (a b : ConfigSpace ι) (B : Finset (ConfigSpace ι)) :
    rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B ⊆ ({a, b} : Finset (ConfigSpace ι)) := by
  intro w hw
  simp only [rc80_disjOccG, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  obtain ⟨K, L, _, hK, _⟩ := hw
  rcases rc88_occ_pair_self_mem a b K w hK with h | h
  · rw [h]; exact Finset.mem_insert_self a {b}
  · rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)












theorem rc88_other_differs_on_L (a b : ConfigSpace ι) (K L : Finset ι)
    (w : ConfigSpace ι) (hdisj : Disjoint K L) (hK : rc80_occ ({a, b} : Finset (ConfigSpace ι)) K w = true)
    (hwa : w = a) : ∀ e ∈ L, b e ≠ w e := by
  intro e he hcontra
  
  have heK : e ∉ K := fun h => (Finset.disjoint_left.mp hdisj h) he
  
  set w' : ConfigSpace ι := Function.update w e (!w e) with hw'def
  have hagreeK : ∀ f ∈ K, w' f = w f := by
    intro f hf
    have hne : f ≠ e := by rintro rfl; exact heK hf
    rw [hw'def, Function.update_of_ne hne]
  
  have hmem : w' ∈ ({a, b} : Finset (ConfigSpace ι)) := by
    unfold rc80_occ at hK
    rw [decide_eq_true_eq] at hK
    exact hK w' hagreeK
  rw [Finset.mem_insert, Finset.mem_singleton] at hmem
  
  have hw'e : w' e = !w e := by rw [hw'def, Function.update_self]
  rcases hmem with hwa' | hwb'
  · 
    have : w' e = w e := by rw [hwa', ← hwa]
    rw [hw'e] at this
    exact (Bool.not_ne_self (w e)) this
  · 
    have : w' e = b e := by rw [hwb']
    rw [hw'e, hcontra] at this
    exact (Bool.not_ne_self (w e)) this



theorem rc88_disjOccG_pair_comm (a b : ConfigSpace ι) (B : Finset (ConfigSpace ι)) :
    rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B
      = rc80_disjOccG ({b, a} : Finset (ConfigSpace ι)) B := by
  rw [Finset.pair_comm a b]






theorem rc88_core_other (a b : ConfigSpace ι) (B : Finset (ConfigSpace ι))
    (ha : a ∈ rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B) :
    rc80_compl b ∈ B := by
  simp only [rc80_disjOccG, Finset.mem_filter, Finset.mem_univ, true_and] at ha
  obtain ⟨K, L, hdisj, hK, hL⟩ := ha
  have hdiff : ∀ e ∈ L, b e ≠ a e := rc88_other_differs_on_L a b K L a hdisj hK rfl
  apply rc88_occ_mem_of_agree B L a (rc80_compl b) hL
  intro e he
  unfold rc80_compl
  have := hdiff e he
  cases hbe : b e <;> cases hae : a e <;> simp_all





theorem rc88_core (a b : ConfigSpace ι) (B : Finset (ConfigSpace ι))
    (w : ConfigSpace ι) (hw : w ∈ rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B) :
    rc80_compl a ∈ B ∨ rc80_compl b ∈ B := by
  have hmem := rc88_disjOccG_pair_subset a b B hw
  rw [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hwa | hwb
  · 
    subst hwa
    exact Or.inr (rc88_core_other w b B hw)
  · 
    subst hwb
    rw [rc88_disjOccG_pair_comm] at hw
    exact Or.inl (rc88_core_other w a B hw)




theorem rc88_mem_reflInterG_pair (a b : ConfigSpace ι) (B : Finset (ConfigSpace ι))
    (x : ConfigSpace ι) :
    x ∈ rc80_reflInterG ({a, b} : Finset (ConfigSpace ι)) B ↔
      (x = a ∨ x = b) ∧ rc80_compl x ∈ B := by
  simp only [rc80_reflInterG, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]



theorem rc88_reflInterG_pair_nonempty (a b : ConfigSpace ι)
    (B : Finset (ConfigSpace ι)) (w : ConfigSpace ι)
    (hw : w ∈ rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B) :
    (rc80_reflInterG ({a, b} : Finset (ConfigSpace ι)) B).Nonempty := by
  rcases rc88_core a b B w hw with h | h
  · exact ⟨a, (rc88_mem_reflInterG_pair a b B a).mpr ⟨Or.inl rfl, h⟩⟩
  · exact ⟨b, (rc88_mem_reflInterG_pair a b B b).mpr ⟨Or.inr rfl, h⟩⟩




theorem rc88_reflInterG_pair_full (a b : ConfigSpace ι) (B : Finset (ConfigSpace ι))
    (ha : a ∈ rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B)
    (hb : b ∈ rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B) :
    rc80_reflInterG ({a, b} : Finset (ConfigSpace ι)) B = ({a, b} : Finset (ConfigSpace ι)) := by
  
  have hcb : rc80_compl b ∈ B := rc88_core_other a b B ha
  have hca : rc80_compl a ∈ B := by
    rw [rc88_disjOccG_pair_comm] at hb
    exact rc88_core_other b a B hb
  apply Finset.Subset.antisymm
  · exact Finset.filter_subset _ _
  · intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hxa | hxb
    · exact (rc88_mem_reflInterG_pair a b B x).mpr ⟨Or.inl hxa, hxa ▸ hca⟩
    · exact (rc88_mem_reflInterG_pair a b B x).mpr ⟨Or.inr hxb, hxb ▸ hcb⟩











theorem rc88_wall_twogen_left (a b : ConfigSpace ι) (B : Finset (ConfigSpace ι)) :
    (rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B).card
      ≤ (rc80_reflInterG ({a, b} : Finset (ConfigSpace ι)) B).card := by
  by_cases hboth : a ∈ rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B ∧
      b ∈ rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B
  · 
    obtain ⟨ha, hb⟩ := hboth
    rw [rc88_reflInterG_pair_full a b B ha hb]
    exact Finset.card_le_card (rc88_disjOccG_pair_subset a b B)
  · 
    have hsub : rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B
        ⊆ ({a, b} : Finset (ConfigSpace ι)) := rc88_disjOccG_pair_subset a b B
    have hproper : rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B
        ⊂ ({a, b} : Finset (ConfigSpace ι)) := by
      rw [Finset.ssubset_iff_of_subset hsub]
      
      by_contra hnot
      apply hboth
      refine ⟨?_, ?_⟩
      · by_contra hna
        exact hnot ⟨a, Finset.mem_insert_self a {b}, hna⟩
      · by_contra hnb
        exact hnot ⟨b, Finset.mem_insert_of_mem (Finset.mem_singleton_self b), hnb⟩
    
    have hlt : (rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B).card
        < ({a, b} : Finset (ConfigSpace ι)).card := Finset.card_lt_card hproper
    have hle2 : ({a, b} : Finset (ConfigSpace ι)).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by
      simp)
    have hle1 : (rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B).card ≤ 1 := by omega
    
    rcases Nat.eq_zero_or_pos (rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B).card with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    · have hne : (rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B).Nonempty :=
        Finset.card_pos.mp hpos
      obtain ⟨w, hw⟩ := hne
      have hRne : (rc80_reflInterG ({a, b} : Finset (ConfigSpace ι)) B).Nonempty :=
        rc88_reflInterG_pair_nonempty a b B w hw
      have hR1 : 1 ≤ (rc80_reflInterG ({a, b} : Finset (ConfigSpace ι)) B).card :=
        Finset.card_pos.mpr hRne
      omega





theorem rc88_disjOccG_comm (A B : Finset (ConfigSpace ι)) :
    rc80_disjOccG A B = rc80_disjOccG B A := by
  ext w
  simp only [rc80_disjOccG, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨K, L, hd, hA, hB⟩
    exact ⟨L, K, hd.symm, hB, hA⟩
  · rintro ⟨K, L, hd, hB, hA⟩
    exact ⟨L, K, hd.symm, hA, hB⟩



theorem rc88_reflInterG_comm_image (A B : Finset (ConfigSpace ι)) :
    rc80_reflInterG A B = (rc80_reflInterG B A).image rc80_compl := by
  ext a
  simp only [rc80_reflInterG, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨haA, hcaB⟩
    exact ⟨rc80_compl a, ⟨hcaB, by rw [rc80_compl_compl]; exact haA⟩, rc80_compl_compl a⟩
  · rintro ⟨x, ⟨hxB, hcxA⟩, rfl⟩
    exact ⟨hcxA, by rw [rc80_compl_compl]; exact hxB⟩



theorem rc88_reflInterG_card_comm (A B : Finset (ConfigSpace ι)) :
    (rc80_reflInterG A B).card = (rc80_reflInterG B A).card := by
  rw [rc88_reflInterG_comm_image, Finset.card_image_of_injective _ rc87_compl_injective]





theorem rc88_wall_twogen_right (A : Finset (ConfigSpace ι)) (a b : ConfigSpace ι) :
    (rc80_disjOccG A ({a, b} : Finset (ConfigSpace ι))).card
      ≤ (rc80_reflInterG A ({a, b} : Finset (ConfigSpace ι))).card := by
  rw [rc88_disjOccG_comm, rc88_reflInterG_card_comm]
  exact rc88_wall_twogen_left a b A






def rc88_a3 : ConfigSpace (Fin 3) := ![false, true, false]
def rc88_b3 : ConfigSpace (Fin 3) := ![true, true, false]


def rc88_A3 : Finset (ConfigSpace (Fin 3)) := {rc88_a3, rc88_b3}


theorem rc88_a3_ne_b3 : rc88_a3 ≠ rc88_b3 := by decide


theorem rc88_A3_not_upper : ¬ rc80_IsUpper rc88_A3 := by
  intro h
  have hmem : rc88_a3 ∈ rc88_A3 := by decide
  have := h _ hmem 2
  revert this
  decide


theorem rc88_A3_not_lower : ¬ rc80_IsLower rc88_A3 := by
  intro h
  have hmem : rc88_a3 ∈ rc88_A3 := by decide
  have := h _ hmem 1
  revert this
  decide





theorem rc88_nonmono_witness_fin3 (B : Finset (ConfigSpace (Fin 3))) :
    (rc80_disjOccG rc88_A3 B).card ≤ (rc80_reflInterG rc88_A3 B).card :=
  rc88_wall_twogen_left rc88_a3 rc88_b3 B



theorem rc88_A3_card : rc88_A3.card = 2 := by decide



open Classical in
































theorem rc88_status :
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ConfigSpace ι) (B : Finset (ConfigSpace ι)),
        rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B ⊆ ({a, b} : Finset (ConfigSpace ι))) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ConfigSpace ι) (B : Finset (ConfigSpace ι)),
        a ∈ rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B → rc80_compl b ∈ B) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ConfigSpace ι) (B : Finset (ConfigSpace ι)),
        (rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B).card
          ≤ (rc80_reflInterG ({a, b} : Finset (ConfigSpace ι)) B).card) ∧
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)) (a b : ConfigSpace ι),
        (rc80_disjOccG A ({a, b} : Finset (ConfigSpace ι))).card
          ≤ (rc80_reflInterG A ({a, b} : Finset (ConfigSpace ι))).card) ∧
    
    (¬ rc80_IsUpper rc88_A3 ∧ ¬ rc80_IsLower rc88_A3 ∧ rc88_A3.card = 2 ∧
        (rc80_disjOccG rc88_A3 Finset.univ).card
          ≤ (rc80_reflInterG rc88_A3 Finset.univ).card) ∧
    
    (rc60_BoxUnionBound → ReimerWprobCore) :=
  ⟨fun a b B => rc88_disjOccG_pair_subset a b B,
   fun a b B ha => rc88_core_other a b B ha,
   fun a b B => rc88_wall_twogen_left a b B,
   fun A a b => rc88_wall_twogen_right A a b,
   ⟨rc88_A3_not_upper, rc88_A3_not_lower, rc88_A3_card, rc88_nonmono_witness_fin3 Finset.univ⟩,
   rc82_reimerWprobCore_of_boxUnionBound⟩

end StatMech.Walls
