/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































import Code.Walls.rc5_reflectinvolution
import Code.Walls.rc5_reindextransfer
import Code.Walls.rc5_doubledboxcount
import Code.Walls.rc5_dpairsmodular
import Code.Walls.rc5_itercompcard
import Code.Walls.rc5_nonvacuity
import Code.Walls.rc2_core

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace








section Deficit

variable {α : Type*} [Fintype α] [DecidableEq α]



theorem rc5_core_reimerCardForm_iff_deficit (A B : Set (ConfigSpace α)) :
    StatMech.poc_ReimerCardForm A B ↔ rc5_deficit A B ≤ 0 :=
  rc5_reimerCardForm_iff_deficit A B



theorem rc5_core_deficitNonpos_iff_reimerCardFormAll :
    rc5_DeficitNonpos ↔ ReimerCardFormAll :=
  rc5_deficitNonpos_iff_reimerCardFormAll

end Deficit








section Engine

variable {β : Type*} [DecidableEq β]
















theorem rc5_core_compressionEngine (𝒜 ℬ : Finset (Finset β)) :
    ((boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ)
      ∧ (∀ i : β, dpairsCount 𝒜 ℬ ≤ dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ))
      ∧ (∀ i : β, (dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) : ℤ)
            - dpairsCount 𝒜 ℬ
          = (dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) : ℤ)
            - dpairsCount (𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i)
                (ℬ.memberSubfamily i ∩ ℬ.nonMemberSubfamily i))
      ∧ (∀ cs : List β, (iterDownComp cs 𝒜).card = 𝒜.card)
      ∧ (∃ cs : List β, IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset β))
            ∧ dpairsCount 𝒜 ℬ ≤ dpairsCount (iterDownComp cs 𝒜) (iterDownComp cs ℬ))
      ∧ (IsLowerSet (𝒜 : Set (Finset β)) → IsLowerSet (ℬ : Set (Finset β)) → ∀ i : β,
            dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i)
              ≤ dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)) := by
  refine ⟨rc5_doubled_box_count 𝒜 ℬ, fun i => rc5_dpairsCount_downDown_mono 𝒜 ℬ i,
    fun i => rc5_deficit_identity 𝒜 ℬ i, fun cs => rc5_iterDownComp_card cs 𝒜, ?_, ?_⟩
  · obtain ⟨cs, hcs, hmono, _⟩ := rc2_blendpoint_converges 𝒜
    exact ⟨cs, hcs, hmono ℬ⟩
  · intro h𝒜 hℬ i; exact rc2_blendpoint_favourable h𝒜 hℬ i

end Engine








section Reflection

variable {α : Type*} [Fintype α] [DecidableEq α]

open Classical in



theorem rc5_core_reflectionDeficit (A B : Set (ConfigSpace α)) :
    Function.Involutive (rmr_compl : ConfigSpace α → ConfigSpace α)
      ∧ (#(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∧ (fun a => !ω a) ∈ B))
          = #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)))
      ∧ (StatMech.poc_ReimerCardForm A B ↔ rc5_deficit A B ≤ 0) :=
  ⟨rc5_compl_involutive, rc5_RHS_eq_inter A B, rc5_reimerCardForm_iff_deficit A B⟩

end Reflection




theorem rc5_core_reindexTransfer (hcard : ReimerCardFormAll)
    {β : Type*} [Fintype β] [DecidableEq β] (A B : Set (ConfigSpace β)) :
    poc_ReimerCardForm A B :=
  rc5_reindexTransfer hcard A B








section Injection

variable {α : Type*} [Fintype α] [DecidableEq α]

open Classical in





def rc5_BoxReflectInjection (A B : Set (ConfigSpace α)) : Prop :=
  ∃ f : ConfigSpace α → ConfigSpace α,
    Set.InjOn f {ω | ω ∈ disjointOccurrence A B} ∧
    ∀ ω, ω ∈ disjointOccurrence A B → f ω ∈ A ∩ rmr_reflect B

open Classical in



theorem rc5_core_reimerCardForm_of_injection {A B : Set (ConfigSpace α)}
    (h : rc5_BoxReflectInjection A B) : StatMech.poc_ReimerCardForm A B := by
  rw [rmr_reimerCardForm_iff_inter]
  obtain ⟨f, hinj, hmem⟩ := h
  apply Finset.card_le_card_of_injOn f
  · intro ω hω
    rw [Finset.mem_coe, Finset.mem_filter] at hω
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hmem ω hω.2⟩
  · intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_filter] at ha hb
    exact hinj ha.2 hb.2 hab

open Classical in






theorem rc5_core_injection_of_reimerCardForm {A B : Set (ConfigSpace α)}
    (h : StatMech.poc_ReimerCardForm A B) : rc5_BoxReflectInjection A B := by
  rw [rmr_reimerCardForm_iff_inter] at h
  set s := Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B) with hs
  set t := Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B) with ht
  by_cases hsne : s.Nonempty
  · have hemb : Nonempty (s ↪ t) := by
      rw [← Fintype.card_coe s, ← Fintype.card_coe t] at h
      exact Function.Embedding.nonempty_of_card_le h
    obtain ⟨e⟩ := hemb
    have htne : t.Nonempty := by
      rw [← Finset.card_pos]
      exact lt_of_lt_of_le (Finset.card_pos.mpr hsne) h
    obtain ⟨t0, ht0⟩ := htne
    classical
    refine ⟨fun ω => if hω : ω ∈ s then (e ⟨ω, hω⟩).val else t0, ?_, ?_⟩
    · intro a ha b hb hab
      have ha' : a ∈ s := by rw [hs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, ha⟩
      have hb' : b ∈ s := by rw [hs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hb⟩
      simp only [dif_pos ha', dif_pos hb'] at hab
      have : (⟨a, ha'⟩ : s) = ⟨b, hb'⟩ := e.injective (Subtype.ext hab)
      exact congrArg Subtype.val this
    · intro ω hbox
      have hω : ω ∈ s := by rw [hs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hbox⟩
      simp only [dif_pos hω]
      have hmem : (e ⟨ω, hω⟩).val ∈ t := (e ⟨ω, hω⟩).property
      have hmem' : (e ⟨ω, hω⟩).val ∈ A ∩ rmr_reflect B := by
        have hthis : (e ⟨ω, hω⟩).val ∈ Finset.univ.filter
            (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B) := ht ▸ hmem
        exact (Finset.mem_filter.mp hthis).2
      exact hmem'
  · refine ⟨id, ?_, ?_⟩
    · intro a ha
      exact absurd ⟨a, by rw [hs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, ha⟩⟩ hsne
    · intro ω hbox
      exact absurd ⟨ω, by rw [hs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hbox⟩⟩ hsne





theorem rc5_core_injection_iff_reimerCardForm (A B : Set (ConfigSpace α)) :
    rc5_BoxReflectInjection A B ↔ StatMech.poc_ReimerCardForm A B :=
  ⟨rc5_core_reimerCardForm_of_injection, rc5_core_injection_of_reimerCardForm⟩

end Injection










def rc5_BoxReflectInjectionAll : Prop :=
  ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))), rc5_BoxReflectInjection A B




theorem rc5_core_reimerCardFormAll_of_injectionAll (h : rc5_BoxReflectInjectionAll) :
    ReimerCardFormAll :=
  fun n A B => rc5_core_reimerCardForm_of_injection (h n A B)




theorem rc5_core_injectionAll_of_reimerCardFormAll (h : ReimerCardFormAll) :
    rc5_BoxReflectInjectionAll :=
  fun n A B => rc5_core_injection_of_reimerCardForm (h n A B)





theorem rc5_core_injectionAll_iff_reimerCardFormAll :
    rc5_BoxReflectInjectionAll ↔ ReimerCardFormAll :=
  ⟨rc5_core_reimerCardFormAll_of_injectionAll, rc5_core_injectionAll_of_reimerCardFormAll⟩












theorem rc5_core_reimerCardFormAll_iff_residue : ReimerCardFormAll ↔ ReimerResidue :=
  rc4_residue_iff_reimerCardFormAll.symm





theorem rc5_core_injectionAll_of_residue (h : ReimerResidue) : rc5_BoxReflectInjectionAll :=
  rc5_core_injectionAll_of_reimerCardFormAll (rc3_core_reimerCardFormAll_of_residue h)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in




theorem rc5_core_reimer_inequality_of_injectionAll (h : rc5_BoxReflectInjectionAll) {E : Type*}
    [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1) (A B : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  rc4_reimer_inequality_of_reimerCardFormAll
    (rc5_core_reimerCardFormAll_of_injectionAll h) hp A B









section Nonvacuity

variable {α : Type*} [Fintype α] [DecidableEq α]




theorem rc5_core_injection_rbi : rc5_BoxReflectInjection rbi_A rbi_B :=
  rc5_core_injection_of_reimerCardForm rc5_reimerCardForm_rbi



theorem rc5_core_injection_of_disjoint_support {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : DependsOn A (↑S)) (hB : DependsOn B (↑T)) (hST : Disjoint S T) :
    rc5_BoxReflectInjection A B :=
  rc5_core_injection_of_reimerCardForm (rc5_reimerCardForm_of_disjoint_support hA hB hST)



theorem rc5_core_injection_of_box_empty {A B : Set (ConfigSpace α)}
    (hbox : disjointOccurrence A B = ∅) : rc5_BoxReflectInjection A B :=
  rc5_core_injection_of_reimerCardForm (rc5_reimerCardForm_of_box_empty hbox)



theorem rc5_core_injection_one (A B : Set (ConfigSpace (Fin 1))) : rc5_BoxReflectInjection A B :=
  rc5_core_injection_of_reimerCardForm (rc5_reimerCardForm_one A B)

end Nonvacuity






























theorem rc5_core_cardform_all :
    (rc5_DeficitNonpos ↔ ReimerCardFormAll)
      ∧ (ReimerCardFormAll ↔ ReimerResidue)
      ∧ (rc5_BoxReflectInjectionAll ↔ ReimerCardFormAll)
      ∧ (rc5_BoxReflectInjectionAll → ReimerResidue)
      ∧ (ReimerResidue → rc5_BoxReflectInjectionAll) :=
  ⟨rc5_core_deficitNonpos_iff_reimerCardFormAll,
    rc5_core_reimerCardFormAll_iff_residue,
    rc5_core_injectionAll_iff_reimerCardFormAll,
    fun h => rc5_core_reimerCardFormAll_iff_residue.mp
      (rc5_core_reimerCardFormAll_of_injectionAll h),
    rc5_core_injectionAll_of_residue⟩

end StatMech.Walls
