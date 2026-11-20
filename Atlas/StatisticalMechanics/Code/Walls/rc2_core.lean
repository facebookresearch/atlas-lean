/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































import Code.Walls.rc2_slabcardallisbridge
import Code.Walls.rc2_slabimgeqinter
import Code.Walls.rc2_cardformiffinter
import Code.Walls.rc2_dpairsdowndownmono
import Code.Walls.rc2_doubledboxcount
import Code.Walls.rc2_blendpoint

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]










open Classical in


theorem rc2_slabBox_eq_slabFilter (A B : Set (ConfigSpace α)) (k : ConfigSpace α × ConfigSpace α) :
    poc_slabBox A B k =
      Finset.univ.filter (fun ω => ω ∈ disjointOccurrence A B ∧ ω ∈ rc2_slab k) := by
  unfold poc_slabBox
  apply Finset.filter_congr
  intro ω _
  simp only [rc2_mem_slab]

open Classical in







theorem rc2_slabCard_iff_perKey (A B : Set (ConfigSpace α)) :
    poc_SlabCard A B ↔
      ∀ k : ConfigSpace α × ConfigSpace α,
        #(Finset.univ.filter (fun ω => ω ∈ disjointOccurrence A B ∧ ω ∈ rc2_slab k)) ≤
        #(Finset.univ.filter (fun ω => ω ∈ A ∩ rc2_keyReflect k B ∧ ω ∈ rc2_slab k)) := by
  unfold poc_SlabCard
  refine forall_congr' (fun k => ?_)
  rw [rc2_slabBox_eq_slabFilter, rc2_slabImg_eq_inter]








omit [Fintype α] [DecidableEq α] in


theorem rc2_orbitKey_symm (a b : ConfigSpace α) : orbitKey (a, b) = orbitKey (b, a) := by
  simp only [orbitKey]
  apply Prod.ext <;> funext c <;> simp [Bool.or_comm, Bool.and_comm]

omit [Fintype α] [DecidableEq α] in


theorem rc2_keyFlip_slab_invol (k : ConfigSpace α × ConfigSpace α) (ω : ConfigSpace α) :
    poc_keyFlip k (poc_keyFlip k ω) = ω :=
  rc2_keyFlip_involutive_on_slab k ω

omit [Fintype α] [DecidableEq α] in



theorem rc2_keyFlip_maps_slab (k : ConfigSpace α × ConfigSpace α) {ω : ConfigSpace α}
    (hω : ω ∈ rc2_slab k) : poc_keyFlip k ω ∈ rc2_slab k := by
  simp only [rc2_mem_slab] at hω ⊢
  rw [rc2_keyFlip_slab_invol, rc2_orbitKey_symm]
  exact hω









open Classical in






def SlabInjection (A B : Set (ConfigSpace α)) : Prop :=
  ∀ k : ConfigSpace α × ConfigSpace α,
    ∃ f : ConfigSpace α → ConfigSpace α,
      Set.InjOn f {ω | ω ∈ disjointOccurrence A B ∧ ω ∈ rc2_slab k} ∧
      ∀ ω, ω ∈ disjointOccurrence A B → ω ∈ rc2_slab k →
        f ω ∈ A ∩ rc2_keyReflect k B ∧ f ω ∈ rc2_slab k

open Classical in




theorem rc2_slabInjection_imp_slabCard {A B : Set (ConfigSpace α)} (h : SlabInjection A B) :
    poc_SlabCard A B := by
  rw [rc2_slabCard_iff_perKey]
  intro k
  obtain ⟨f, hinj, hmem⟩ := h k
  apply Finset.card_le_card_of_injOn f
  · intro ω hω
    rw [Finset.mem_coe, Finset.mem_filter] at hω
    obtain ⟨_, hbox, hslab⟩ := hω
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hmem ω hbox hslab⟩
  · intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_filter] at ha hb
    exact hinj ⟨ha.2.1, ha.2.2⟩ ⟨hb.2.1, hb.2.2⟩ hab

open Classical in






theorem rc2_slabInjection_of_slabCard {A B : Set (ConfigSpace α)} (h : poc_SlabCard A B) :
    SlabInjection A B := by
  rw [rc2_slabCard_iff_perKey] at h
  intro k
  set s := Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B ∧ ω ∈ rc2_slab k)
    with hs
  set t := Finset.univ.filter
    (fun ω : ConfigSpace α => ω ∈ A ∩ rc2_keyReflect k B ∧ ω ∈ rc2_slab k) with ht
  
  by_cases hsne : s.Nonempty
  · 
    have hcard : s.card ≤ t.card := h k
    have hemb : Nonempty (s ↪ t) := by
      rw [← Fintype.card_coe s, ← Fintype.card_coe t] at hcard
      exact Function.Embedding.nonempty_of_card_le hcard
    obtain ⟨e⟩ := hemb
    
    have htne : t.Nonempty := by
      rw [← Finset.card_pos]
      exact lt_of_lt_of_le (Finset.card_pos.mpr hsne) hcard
    obtain ⟨t0, ht0⟩ := htne
    classical
    refine ⟨fun ω => if hω : ω ∈ s then (e ⟨ω, hω⟩).val else t0, ?_, ?_⟩
    · intro a ha b hb hab
      have ha' : a ∈ s := by rw [hs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, ha⟩
      have hb' : b ∈ s := by rw [hs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hb⟩
      simp only [dif_pos ha', dif_pos hb'] at hab
      have : (⟨a, ha'⟩ : s) = ⟨b, hb'⟩ := e.injective (Subtype.ext hab)
      exact congrArg Subtype.val this
    · intro ω hbox hslab
      have hω : ω ∈ s := by rw [hs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hbox, hslab⟩
      simp only [dif_pos hω]
      have hmem : (e ⟨ω, hω⟩).val ∈ t := (e ⟨ω, hω⟩).property
      rw [Finset.mem_filter] at hmem
      exact hmem.2
  · 
    refine ⟨id, ?_, ?_⟩
    · intro a ha
      exact absurd ⟨a, by rw [hs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, ha⟩⟩ hsne
    · intro ω hbox hslab
      exact absurd ⟨ω, by rw [hs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hbox, hslab⟩⟩ hsne






theorem rc2_slabInjection_iff (A B : Set (ConfigSpace α)) :
    SlabInjection A B ↔ poc_SlabCard A B :=
  ⟨rc2_slabInjection_imp_slabCard, rc2_slabInjection_of_slabCard⟩


def SlabInjectionAll : Prop :=
  ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))), SlabInjection A B


theorem rc2_slabCardAll_of_slabInjectionAll (h : SlabInjectionAll) : StatMech.poc_SlabCardAll :=
  fun n A B => rc2_slabInjection_imp_slabCard (h n A B)




theorem rc2_reimerWprobCore_of_slabInjectionAll (h : SlabInjectionAll) : ReimerWprobCore :=
  rc2_reimerWprobCore_of_slabCardAll (rc2_slabCardAll_of_slabInjectionAll h)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in




theorem rc2_reimer_inequality_of_slabInjectionAll (h : SlabInjectionAll) {E : Type*}
    [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1) (A B : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  rc2_reimer_inequality_of_bridge
    (rc2_countBoxBridge_iff_slabCardAll.mpr (rc2_slabCardAll_of_slabInjectionAll h)) hp A B




















theorem rc2_compressionEngine {β : Type*} [DecidableEq β] (𝒜 ℬ : Finset (Finset β)) :
    (∀ i : β, dpairsCount 𝒜 ℬ ≤ dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ))
      ∧ (∀ i : β, (dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) : ℤ)
            - dpairsCount 𝒜 ℬ
          = (dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) : ℤ)
            - dpairsCount (𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i)
                (ℬ.memberSubfamily i ∩ ℬ.nonMemberSubfamily i))
      ∧ (∃ cs : List β, IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset β))
            ∧ dpairsCount 𝒜 ℬ ≤ dpairsCount (iterDownComp cs 𝒜) (iterDownComp cs ℬ))
      ∧ (IsLowerSet (𝒜 : Set (Finset β)) → IsLowerSet (ℬ : Set (Finset β)) → ∀ i : β,
            dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i)
              ≤ dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)) := by
  refine ⟨fun i => rc2_dpairsCount_downDown_mono 𝒜 ℬ i,
    fun i => rc2_deficit_identity 𝒜 ℬ i, ?_,
    fun h𝒜 hℬ i => rc2_blendpoint_favourable h𝒜 hℬ i⟩
  obtain ⟨cs, hcs, hmono, _⟩ := rc2_blendpoint_converges 𝒜
  exact ⟨cs, hcs, hmono ℬ⟩



theorem rc2_engine_count_eq_doubledBox {β : Type*} [DecidableEq β] (𝒜 ℬ : Finset (Finset β)) :
    (boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ :=
  rc2_doubled_box_count 𝒜 ℬ











theorem rc2_slabCard_of_disjoint_support {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : DependsOn A (↑S)) (hB : DependsOn B (↑T)) (hST : Disjoint S T) :
    poc_SlabCard A B :=
  poc_slabCard_of_disjoint_support hA hB hST



theorem rc2_slabCard_one (A B : Set (ConfigSpace (Fin 1))) : poc_SlabCard A B :=
  rc_core_bridge_one A B


theorem rc2_slabCard_of_box_empty {A B : Set (ConfigSpace α)}
    (hbox : disjointOccurrence A B = ∅) : poc_SlabCard A B :=
  poc_slabCard_of_box_empty hbox




theorem rc2_slabCard_rbi : poc_SlabCard rbi_A rbi_B :=
  poc_slabCard_rbi

open Classical in


theorem rc2_perKey_rbi (k : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :
    #(Finset.univ.filter (fun ω => ω ∈ disjointOccurrence rbi_A rbi_B ∧ ω ∈ rc2_slab k)) ≤
      #(Finset.univ.filter (fun ω => ω ∈ rbi_A ∩ rc2_keyReflect k rbi_B ∧ ω ∈ rc2_slab k)) :=
  (rc2_slabCard_iff_perKey rbi_A rbi_B).mp poc_slabCard_rbi k




theorem rc2_slabInjection_rbi : SlabInjection rbi_A rbi_B :=
  (rc2_slabInjection_iff rbi_A rbi_B).mpr poc_slabCard_rbi

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in

theorem rc2_slabInjection_of_disjoint_support {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : DependsOn A (↑S)) (hB : DependsOn B (↑T)) (hST : Disjoint S T) :
    SlabInjection A B :=
  (rc2_slabInjection_iff A B).mpr (poc_slabCard_of_disjoint_support hA hB hST)



theorem rc2_slabInjection_one (A B : Set (ConfigSpace (Fin 1))) : SlabInjection A B :=
  (rc2_slabInjection_iff A B).mpr (rc_core_bridge_one A B)









open Classical in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in












theorem rc2_count_box_bridge :
    (∀ {α : Type} [Fintype α] [DecidableEq α] (A B : Set (ConfigSpace α)),
        poc_SlabCard A B ↔
          ∀ k : ConfigSpace α × ConfigSpace α,
            #(Finset.univ.filter (fun ω => ω ∈ disjointOccurrence A B ∧ ω ∈ rc2_slab k)) ≤
            #(Finset.univ.filter (fun ω => ω ∈ A ∩ rc2_keyReflect k B ∧ ω ∈ rc2_slab k)))
      ∧ (SlabInjectionAll → StatMech.poc_SlabCardAll)
      ∧ (SlabInjectionAll → rc_core_CountBoxBridge)
      ∧ (SlabInjectionAll → ReimerWprobCore) := by
  refine ⟨fun {α} _ _ A B => rc2_slabCard_iff_perKey A B,
    rc2_slabCardAll_of_slabInjectionAll,
    fun h => rc2_countBoxBridge_iff_slabCardAll.mpr (rc2_slabCardAll_of_slabInjectionAll h),
    rc2_reimerWprobCore_of_slabInjectionAll⟩

end StatMech.Walls
