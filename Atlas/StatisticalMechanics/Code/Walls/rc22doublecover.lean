/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































import Code.Walls.rc21persupport
import Code.Walls.rc2_dpairsdowndownmono
import Code.Walls.rc2_blendpoint
import Code.Walls.rc16sliceunion
import Mathlib.Combinatorics.SetFamily.Compression.UV

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]












noncomputable def rc22_complPairs (𝒜 ℬ : Finset (Finset α)) : Finset (Finset α × Finset α) :=
  (𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2 ∧ p.1 ∪ p.2 = univ)


theorem rc22_mem_complPairs (𝒜 ℬ : Finset (Finset α)) (p : Finset α × Finset α) :
    p ∈ rc22_complPairs 𝒜 ℬ ↔
      p.1 ∈ 𝒜 ∧ p.2 ∈ ℬ ∧ Disjoint p.1 p.2 ∧ p.1 ∪ p.2 = univ := by
  rw [rc22_complPairs, Finset.mem_filter, Finset.mem_product]
  tauto




theorem rc22_compl_of_disjoint_union {S T : Finset α} (hd : Disjoint S T) (hu : S ∪ T = univ) :
    Sᶜ = T := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [Finset.mem_compl] at hx
    have : x ∈ S ∪ T := by rw [hu]; exact Finset.mem_univ x
    rw [Finset.mem_union] at this
    exact this.resolve_left hx
  · have hcard : #S + #T = Fintype.card α := by
      rw [← Finset.card_union_of_disjoint hd, hu, Finset.card_univ]
    have hcompl_card : #Sᶜ = Fintype.card α - #S := by rw [Finset.card_compl]
    omega

open Classical in





theorem rc22_card_reflInter_eq_complPairs (𝒜 ℬ : Finset (Finset α)) :
    #(rc10_reflInter 𝒜 ℬ) = #(rc22_complPairs 𝒜 ℬ) := by
  apply Finset.card_bij (fun S _ => (S, Sᶜ))
  · intro S hS
    rw [rc20_mem_reflInter] at hS
    rw [rc22_mem_complPairs]
    exact ⟨hS.1, hS.2, disjoint_compl_right, by simp⟩
  · intro S _ S' _ h
    exact (Prod.mk.injEq _ _ _ _ ▸ h).1
  · intro p hp
    rw [rc22_mem_complPairs] at hp
    obtain ⟨h1, h2, hd, hu⟩ := hp
    have hcompl : p.1ᶜ = p.2 := rc22_compl_of_disjoint_union hd hu
    refine ⟨p.1, ?_, ?_⟩
    · rw [rc20_mem_reflInter]
      exact ⟨h1, by rw [hcompl]; exact h2⟩
    · rw [hcompl]













theorem rc22_complPairs_eq_filter (𝒜 ℬ : Finset (Finset α)) :
    rc22_complPairs 𝒜 ℬ
      = ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).filter (fun p => p.1 ∪ p.2 = univ) := by
  rw [rc22_complPairs, Finset.filter_filter]




theorem rc22_reflInter_le_dpairsCount (𝒜 ℬ : Finset (Finset α)) :
    #(rc10_reflInter 𝒜 ℬ) ≤ dpairsCount 𝒜 ℬ := by
  rw [rc22_card_reflInter_eq_complPairs, rc22_complPairs_eq_filter, dpairsCount]
  exact Finset.card_filter_le _ _













noncomputable def rc22_complFam (ℬ : Finset (Finset α)) : Finset (Finset α) :=
  ℬ.image compl

@[simp] theorem rc22_mem_complFam (ℬ : Finset (Finset α)) (S : Finset α) :
    S ∈ rc22_complFam ℬ ↔ Sᶜ ∈ ℬ := by
  rw [rc22_complFam, Finset.mem_image]
  constructor
  · rintro ⟨T, hT, rfl⟩; rwa [compl_compl]
  · intro h; exact ⟨Sᶜ, h, compl_compl S⟩

theorem rc22_card_complFam (ℬ : Finset (Finset α)) : #(rc22_complFam ℬ) = #ℬ := by
  rw [rc22_complFam]
  exact Finset.card_image_of_injective _ (compl_injective)

open Classical in



theorem rc22_reflInter_eq_inter_complFam (𝒜 ℬ : Finset (Finset α)) :
    rc10_reflInter 𝒜 ℬ = 𝒜 ∩ rc22_complFam ℬ := by
  ext S
  rw [rc20_mem_reflInter, Finset.mem_inter, rc22_mem_complFam]










open Classical in



theorem rc22_famCylBox_subset_boxSupp (𝒜 ℬ : Finset (Finset α)) :
    rc20_famCylBox 𝒜 ℬ ⊆ rc10_boxSupp 𝒜 ℬ := by
  intro S hS
  rw [rc21_mem_famCylBox] at hS
  obtain ⟨K, L, hKL, hKA, hLB⟩ := hS
  rw [rc10_boxSupp, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, S ∩ K, S ∩ L, ?_, Finset.inter_subset_left,
    Finset.inter_subset_left, ?_, ?_⟩
  · exact Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right hKL)
  · exact hKA (S ∩ K) (by rw [Finset.inter_assoc, Finset.inter_self])
  · exact hLB (S ∩ L) (by rw [Finset.inter_assoc, Finset.inter_self])










open Classical in




theorem rc22_famCylBox_le_reflInter_of_upperSet {n : ℕ} {𝒜 ℬ : Finset (Finset (Fin n))}
    (h𝒜 : IsUpperSet (𝒜 : Set (Finset (Fin n)))) (hℬ : IsUpperSet (ℬ : Set (Finset (Fin n)))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) :=
  le_trans (Finset.card_le_card (rc22_famCylBox_subset_boxSupp 𝒜 ℬ))
    (rc16_bkrSetFamily n 𝒜 ℬ h𝒜 hℬ)

















def rc22_InterCountResidue : Prop :=
  ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(𝒜 ∩ rc22_complFam ℬ)





theorem rc22_interCountResidue_iff_famCylBoxResidue :
    rc22_InterCountResidue ↔ rc20_FamCylBoxResidue := by
  constructor
  · intro h n 𝒜 ℬ
    rw [rc22_reflInter_eq_inter_complFam]; exact h n 𝒜 ℬ
  · intro h n 𝒜 ℬ
    rw [← rc22_reflInter_eq_inter_complFam]; exact h n 𝒜 ℬ




theorem rc22_cylBoxReflInter_of_interCountResidue (h : rc22_InterCountResidue) :
    rc18_CylBoxReflInter :=
  rc20_famCylBoxResidue_iff_cylBoxReflInter.mp
    (rc22_interCountResidue_iff_famCylBoxResidue.mp h)

















variable {β : Type*} [DecidableEq β]






theorem rc22_fiber_inter_ineq (am an cm cn : Finset β) :
    #((am ∩ an) ∩ (cm ∪ cn)) + #((am ∪ an) ∩ (cm ∩ cn))
      ≤ #(am ∩ cm) + #(an ∩ cn) := by
  set A := (am ∩ an) ∩ (cm ∪ cn) with hA
  set B := (am ∪ an) ∩ (cm ∩ cn) with hB
  set X := am ∩ cm with hX
  set Y := an ∩ cn with hY
  have hunion : A ∪ B ⊆ X ∪ Y := by
    intro x hx
    simp only [hA, hB, hX, hY, Finset.mem_union, Finset.mem_inter] at hx ⊢
    rcases hx with ⟨⟨hp, hq⟩, hrs⟩ | ⟨hpq, hr, hs⟩
    · rcases hrs with hr | hs
      · exact Or.inl ⟨hp, hr⟩
      · exact Or.inr ⟨hq, hs⟩
    · rcases hpq with hp | hq
      · exact Or.inl ⟨hp, hr⟩
      · exact Or.inr ⟨hq, hs⟩
  have hinter : A ∩ B ⊆ X ∩ Y := by
    intro x hx
    simp only [hA, hB, hX, hY, Finset.mem_inter, Finset.mem_union] at hx ⊢
    obtain ⟨⟨⟨hp, hq⟩, _⟩, _, hr, hs⟩ := hx
    exact ⟨⟨hp, hr⟩, hq, hs⟩
  calc #A + #B
      = #(A ∪ B) + #(A ∩ B) := (Finset.card_union_add_card_inter A B).symm
    _ ≤ #(X ∪ Y) + #(X ∩ Y) :=
        Nat.add_le_add (Finset.card_le_card hunion) (Finset.card_le_card hinter)
    _ = #X + #Y := Finset.card_union_add_card_inter X Y










noncomputable def rc22_upComp (i : β) (𝒜 : Finset (Finset β)) : Finset (Finset β) :=
  UV.compression {i} ∅ 𝒜


theorem rc22_uvCompress_singleton (a : β) (s : Finset β) :
    UV.compress ({a} : Finset β) ∅ s = insert a s := by
  by_cases ha : a ∈ s
  · rw [UV.compress]
    simp only [Finset.disjoint_singleton_left, ha, not_true, false_and, if_false]
    rw [insert_eq_of_mem ha]
  · rw [UV.compress_of_disjoint_of_le]
    · rw [Finset.sdiff_empty, Finset.sup_eq_union, Finset.union_comm, Finset.insert_eq]
    · simp [Finset.disjoint_singleton_left, ha]
    · exact bot_le


theorem rc22_mem_upComp (i : β) (𝒜 : Finset (Finset β)) (s : Finset β) :
    s ∈ rc22_upComp i 𝒜 ↔
      (s ∈ 𝒜 ∧ insert i s ∈ 𝒜) ∨ (s ∉ 𝒜 ∧ ∃ b ∈ 𝒜, insert i b = s) := by
  unfold rc22_upComp; rw [UV.mem_compression]; simp_rw [rc22_uvCompress_singleton]


theorem rc22_upComp_card (i : β) (𝒜 : Finset (Finset β)) : (rc22_upComp i 𝒜).card = 𝒜.card := by
  unfold rc22_upComp; exact UV.card_compression _ _ _


theorem rc22_upComp_nonMemberSubfamily (i : β) (𝒞 : Finset (Finset β)) :
    (rc22_upComp i 𝒞).nonMemberSubfamily i = 𝒞.memberSubfamily i ∩ 𝒞.nonMemberSubfamily i := by
  ext s
  simp only [mem_nonMemberSubfamily, mem_inter, mem_memberSubfamily, rc22_mem_upComp]
  constructor
  · rintro ⟨h, hns⟩
    rcases h with ⟨hsC, hins⟩ | ⟨_, b, _, hb⟩
    · exact ⟨⟨hins, hns⟩, hsC, hns⟩
    · exact absurd (by rw [← hb]; exact mem_insert_self i b) hns
  · rintro ⟨⟨hins, _⟩, hsC, hns⟩; exact ⟨Or.inl ⟨hsC, hins⟩, hns⟩


theorem rc22_upComp_memberSubfamily (i : β) (𝒞 : Finset (Finset β)) :
    (rc22_upComp i 𝒞).memberSubfamily i = 𝒞.memberSubfamily i ∪ 𝒞.nonMemberSubfamily i := by
  ext s
  simp only [mem_memberSubfamily, mem_union, mem_nonMemberSubfamily, rc22_mem_upComp]
  constructor
  · rintro ⟨h, hns⟩
    rcases h with ⟨hsC, _⟩ | ⟨_, b, hbC, hb⟩
    · exact Or.inl ⟨hsC, hns⟩
    · by_cases hib : i ∈ b
      · rw [insert_eq_of_mem hib] at hb; exact Or.inl ⟨hb ▸ hbC, hns⟩
      · have hbs : b = s := by
          have := congrArg (fun t => Finset.erase t i) hb
          simp only [Finset.erase_insert hib, Finset.erase_insert hns] at this; exact this
        exact Or.inr ⟨hbs ▸ hbC, hns⟩
  · intro h
    rcases h with ⟨hins, hns⟩ | ⟨hsC, hns⟩
    · exact ⟨Or.inl ⟨hins, by rw [insert_idem]; exact hins⟩, hns⟩
    · refine ⟨?_, hns⟩
      by_cases hins : insert i s ∈ 𝒞
      · exact Or.inl ⟨hins, by rw [insert_idem]; exact hins⟩
      · exact Or.inr ⟨hins, s, hsC, rfl⟩











theorem rc22_downInterUp_le (i : β) (𝒜 𝒞 : Finset (Finset β)) :
    #(Down.compression i 𝒜 ∩ rc22_upComp i 𝒞) ≤ #(𝒜 ∩ 𝒞) := by
  rw [← card_memberSubfamily_add_card_nonMemberSubfamily i (Down.compression i 𝒜 ∩ rc22_upComp i 𝒞),
      ← card_memberSubfamily_add_card_nonMemberSubfamily i (𝒜 ∩ 𝒞),
      memberSubfamily_inter, nonMemberSubfamily_inter, memberSubfamily_inter,
      nonMemberSubfamily_inter, rc2_downComp_memberSubfamily, rc2_downComp_nonMemberSubfamily,
      rc22_upComp_memberSubfamily, rc22_upComp_nonMemberSubfamily]
  exact rc22_fiber_inter_ineq _ _ _ _


theorem rc22_mem_complImage [Fintype β] (ℬ : Finset (Finset β)) (s : Finset β) :
    s ∈ ℬ.image compl ↔ sᶜ ∈ ℬ := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨T, hT, rfl⟩; rwa [compl_compl]
  · intro h; exact ⟨sᶜ, h, compl_compl s⟩



theorem rc22_complImage_downCompression [Fintype β] (i : β) (ℬ : Finset (Finset β)) :
    (Down.compression i ℬ).image compl = rc22_upComp i (ℬ.image compl) := by
  ext s
  rw [rc22_mem_complImage, rc22_mem_upComp, Down.mem_compression]
  simp only [rc22_mem_complImage]
  rw [Finset.compl_insert]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h1, h2⟩
    · have his : i ∈ s := by
        by_contra hc
        exact h1 (by rwa [insert_eq_of_mem (Finset.mem_compl.mpr hc)] at h2)
      refine Or.inr ⟨h1, s.erase i, ?_, Finset.insert_erase his⟩
      rw [compl_erase]; exact h2
  · rintro (⟨h1, h2⟩ | ⟨h1, b, hb1, hb2⟩)
    · exact Or.inl ⟨h1, h2⟩
    · refine Or.inr ⟨h1, ?_⟩
      have hib : i ∉ b := by
        intro hc; rw [insert_eq_of_mem hc] at hb2; exact h1 (hb2 ▸ hb1)
      subst hb2
      rw [Finset.compl_insert, Finset.insert_erase (Finset.mem_compl.mpr hib)]
      exact hb1







theorem rc22_reflInter_downDown_antitone [Fintype β] (i : β) (𝒜 ℬ : Finset (Finset β)) :
    #(rc10_reflInter (Down.compression i 𝒜) (Down.compression i ℬ))
      ≤ #(rc10_reflInter 𝒜 ℬ) := by
  rw [rc22_reflInter_eq_inter_complFam, rc22_reflInter_eq_inter_complFam, rc22_complFam,
    rc22_complFam, rc22_complImage_downCompression]
  exact rc22_downInterUp_le i 𝒜 (ℬ.image compl)





theorem rc22_reflInter_iterDownComp_antitone [Fintype β] (cs : List β) (𝒜 ℬ : Finset (Finset β)) :
    #(rc10_reflInter (iterDownComp cs 𝒜) (iterDownComp cs ℬ)) ≤ #(rc10_reflInter 𝒜 ℬ) := by
  induction cs with
  | nil => rw [iterDownComp_nil, iterDownComp_nil]
  | cons i cs ih =>
    rw [iterDownComp_cons, iterDownComp_cons]
    exact le_trans (rc22_reflInter_downDown_antitone i _ _) ih


























open Classical in





def rc22_BoxCompressionMono : Prop :=
  ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (i : Fin n),
    #(rc20_famCylBox 𝒜 ℬ)
      ≤ #(rc20_famCylBox (Down.compression i 𝒜) (Down.compression i ℬ))












theorem rc22_traceClosed_iff_of_lowerSet {𝒜 : Finset (Finset α)}
    (h𝒜 : IsLowerSet (𝒜 : Set (Finset α))) (K S : Finset α) :
    (∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜) ↔ (S ∪ Kᶜ) ∈ 𝒜 := by
  constructor
  · intro h
    apply h
    ext x; simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_compl]
    constructor
    · rintro ⟨hx | hx, hxK⟩
      · exact ⟨hx, hxK⟩
      · exact absurd hxK hx
    · rintro ⟨hxS, hxK⟩; exact ⟨Or.inl hxS, hxK⟩
  · intro hmem T hT
    have hsub : T ⊆ S ∪ Kᶜ := by
      intro x hxT
      simp only [Finset.mem_union, Finset.mem_compl]
      by_cases hxK : x ∈ K
      · left
        have : x ∈ T ∩ K := Finset.mem_inter.mpr ⟨hxT, hxK⟩
        rw [hT] at this
        exact (Finset.mem_inter.mp this).1
      · right; exact hxK
    exact h𝒜 hsub hmem

open Classical in



theorem rc22_mem_famCylBox_of_lowerSet {𝒜 ℬ : Finset (Finset α)}
    (h𝒜 : IsLowerSet (𝒜 : Set (Finset α))) (hℬ : IsLowerSet (ℬ : Set (Finset α))) (S : Finset α) :
    S ∈ rc20_famCylBox 𝒜 ℬ ↔
      ∃ K L : Finset α, Disjoint K L ∧ (S ∪ Kᶜ) ∈ 𝒜 ∧ (S ∪ Lᶜ) ∈ ℬ := by
  rw [rc21_mem_famCylBox]
  refine exists_congr fun K => exists_congr fun L => ?_
  rw [rc22_traceClosed_iff_of_lowerSet h𝒜, rc22_traceClosed_iff_of_lowerSet hℬ]

open Classical in




def rc22_BoxDownsetBase : Prop :=
  ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
    IsLowerSet (𝒜 : Set (Finset (Fin n))) → IsLowerSet (ℬ : Set (Finset (Fin n))) →
      #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)

open Classical in



theorem rc22_famCylBox_iterDownComp_mono (h : rc22_BoxCompressionMono) {n : ℕ}
    (cs : List (Fin n)) (𝒜 ℬ : Finset (Finset (Fin n))) :
    #(rc20_famCylBox 𝒜 ℬ)
      ≤ #(rc20_famCylBox (iterDownComp cs 𝒜) (iterDownComp cs ℬ)) := by
  induction cs with
  | nil => rw [iterDownComp_nil, iterDownComp_nil]
  | cons i cs ih =>
    rw [iterDownComp_cons, iterDownComp_cons]
    exact le_trans ih (h n _ _ i)

open Classical in












theorem rc22_famCylBoxResidue_of_boxCompression
    (hmono : rc22_BoxCompressionMono) (hbase : rc22_BoxDownsetBase) :
    rc20_FamCylBoxResidue := by
  intro n 𝒜 ℬ
  obtain ⟨cs, hcs𝒜, hcsℬ, _, _, _⟩ := rc2_blendpoint_pair 𝒜 ℬ
  calc #(rc20_famCylBox 𝒜 ℬ)
      ≤ #(rc20_famCylBox (iterDownComp cs 𝒜) (iterDownComp cs ℬ)) :=
        rc22_famCylBox_iterDownComp_mono hmono cs 𝒜 ℬ
    _ ≤ #(rc10_reflInter (iterDownComp cs 𝒜) (iterDownComp cs ℬ)) :=
        hbase n _ _ hcs𝒜 hcsℬ
    _ ≤ #(rc10_reflInter 𝒜 ℬ) := rc22_reflInter_iterDownComp_antitone cs 𝒜 ℬ




theorem rc22_cylBoxReflInter_of_boxCompression
    (hmono : rc22_BoxCompressionMono) (hbase : rc22_BoxDownsetBase) :
    rc18_CylBoxReflInter :=
  rc20_famCylBoxResidue_iff_cylBoxReflInter.mp
    (rc22_famCylBoxResidue_of_boxCompression hmono hbase)









open Classical in



theorem rc22_boxDownsetBase_fin0 (𝒜 ℬ : Finset (Finset (Fin 0))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) :=
  rc20_famCylBox_fin0 𝒜 ℬ

open Classical in




theorem rc22_boxDownsetBase_upperSet {n : ℕ} {𝒜 ℬ : Finset (Finset (Fin n))}
    (h𝒜 : IsUpperSet (𝒜 : Set (Finset (Fin n)))) (hℬ : IsUpperSet (ℬ : Set (Finset (Fin n)))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) :=
  rc22_famCylBox_le_reflInter_of_upperSet h𝒜 hℬ



set_option linter.unusedVariables false in
open Classical in



































theorem rc22_reimer_doublecover :
    (∀ (𝒜 ℬ : Finset (Finset α)), #(rc10_reflInter 𝒜 ℬ) = #(rc22_complPairs 𝒜 ℬ))
      ∧ (∀ (𝒜 ℬ : Finset (Finset α)), rc10_reflInter 𝒜 ℬ = 𝒜 ∩ rc22_complFam ℬ)
      ∧ (∀ (𝒜 ℬ : Finset (Finset α)), rc20_famCylBox 𝒜 ℬ ⊆ rc10_boxSupp 𝒜 ℬ)
      ∧ (rc22_InterCountResidue ↔ rc20_FamCylBoxResidue)
      ∧ (∀ [Fintype α] (i : α) (𝒜 ℬ : Finset (Finset α)),
          #(rc10_reflInter (Down.compression i 𝒜) (Down.compression i ℬ))
            ≤ #(rc10_reflInter 𝒜 ℬ))
      ∧ (rc22_BoxCompressionMono → rc22_BoxDownsetBase → rc18_CylBoxReflInter) :=
  ⟨rc22_card_reflInter_eq_complPairs,
    rc22_reflInter_eq_inter_complFam,
    rc22_famCylBox_subset_boxSupp,
    rc22_interCountResidue_iff_famCylBoxResidue,
    fun i 𝒜 ℬ => rc22_reflInter_downDown_antitone i 𝒜 ℬ,
    rc22_cylBoxReflInter_of_boxCompression⟩

end StatMech.Walls
