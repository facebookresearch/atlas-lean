/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




























import Code.Walls.rc20reflection

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]







open Classical in


theorem rc21_mem_famCylBox (𝒜 ℬ : Finset (Finset α)) (S : Finset α) :
    S ∈ rc20_famCylBox 𝒜 ℬ ↔ ∃ K L : Finset α, Disjoint K L ∧
      (∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜) ∧
      (∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ) := by
  rw [rc20_famCylBox, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩















omit [Fintype α] in



theorem rc21_symmDiff_inter_left (S K L : Finset α) (hKL : Disjoint K L) :
    (symmDiff S L) ∩ K = S ∩ K := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_symmDiff]
  constructor
  · rintro ⟨h, hxK⟩
    refine ⟨?_, hxK⟩
    rcases h with ⟨hS, _⟩ | ⟨hL, _⟩
    · exact hS
    · exact absurd hxK (Finset.disjoint_right.mp hKL hL)
  · rintro ⟨hxS, hxK⟩
    have hxL : x ∉ L := Finset.disjoint_left.mp hKL hxK
    exact ⟨Or.inl ⟨hxS, hxL⟩, hxK⟩



theorem rc21_symmDiff_compl_inter_right (S L : Finset α) :
    (symmDiff S L)ᶜ ∩ L = S ∩ L := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_compl, Finset.mem_symmDiff]
  constructor
  · rintro ⟨h, hxL⟩
    refine ⟨?_, hxL⟩
    by_contra hxS
    exact h (Or.inr ⟨hxL, hxS⟩)
  · rintro ⟨hxS, hxL⟩
    refine ⟨?_, hxL⟩
    rintro (⟨_, h⟩ | ⟨_, h⟩)
    · exact h hxL
    · exact h hxS

open Classical in







theorem rc21_symmDiff_mem_reflInter {𝒜 ℬ : Finset (Finset α)} {S K L : Finset α}
    (hKL : Disjoint K L) (hKA : ∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜)
    (hLB : ∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ) :
    symmDiff S L ∈ rc10_reflInter 𝒜 ℬ := by
  rw [rc20_mem_reflInter]
  refine ⟨hKA _ (rc21_symmDiff_inter_left S K L hKL), hLB _ ?_⟩
  exact rc21_symmDiff_compl_inter_right S L












open Classical in





def rc21_SymmDiffReflection : Prop :=
  ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
    ∃ K L : Finset (Fin n) → Finset (Fin n),
      (∀ S ∈ rc20_famCylBox 𝒜 ℬ, Disjoint (K S) (L S) ∧
        (∀ T : Finset (Fin n), T ∩ K S = S ∩ K S → T ∈ 𝒜) ∧
        (∀ T : Finset (Fin n), T ∩ L S = S ∩ L S → T ∈ ℬ)) ∧
      Set.InjOn (fun S => symmDiff S (L S)) (rc20_famCylBox 𝒜 ℬ : Set (Finset (Fin n)))

open Classical in




theorem rc21_perSupportReflection_of_symmDiffReflection (h : rc21_SymmDiffReflection) :
    rc20_PerSupportReflection := by
  intro n 𝒜 ℬ
  obtain ⟨K, L, hwit, hinj⟩ := h n 𝒜 ℬ
  refine ⟨fun S => symmDiff S (L S), hinj, ?_⟩
  intro S hS
  obtain ⟨hKL, hKA, hLB⟩ := hwit S hS
  exact rc21_symmDiff_mem_reflInter hKL hKA hLB




theorem rc21_cylBoxReflInter_of_symmDiffReflection (h : rc21_SymmDiffReflection) :
    rc18_CylBoxReflInter :=
  rc20_perSupportReflection_iff_cylBoxReflInter.mp
    (rc21_perSupportReflection_of_symmDiffReflection h)

















open Classical in






theorem rc21_localRefl_mem_reflInter {𝒜 ℬ : Finset (Finset α)} {S K L R : Finset α}
    (hKA : ∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜)
    (hLB : ∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ)
    (hRK : R ∩ K = S ∩ K) (hRL : Rᶜ ∩ L = S ∩ L) :
    R ∈ rc10_reflInter 𝒜 ℬ := by
  rw [rc20_mem_reflInter]
  exact ⟨hKA R hRK, hLB Rᶜ hRL⟩


def rc21_boxComp (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  univ.filter (fun S => decide (∃ K ∈ (univ : Finset (Finset (Fin n))),
    ∃ L ∈ (univ : Finset (Finset (Fin n))), Disjoint K L ∧
      rc20_traceClass n K S ⊆ 𝒜 ∧ rc20_traceClass n L S ⊆ ℬ) = true)





def rc21_admComp (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  univ.filter (fun R => decide (∃ K ∈ (univ : Finset (Finset (Fin n))),
    ∃ L ∈ (univ : Finset (Finset (Fin n))), Disjoint K L ∧
      rc20_traceClass n K S ⊆ 𝒜 ∧ rc20_traceClass n L S ⊆ ℬ ∧
      R ∩ K = S ∩ K ∧ Rᶜ ∩ L = S ∩ L) = true)

open Classical in


theorem rc21_boxComp_eq (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) :
    rc21_boxComp n 𝒜 ℬ = rc20_famCylBox 𝒜 ℬ := by
  rw [← rc20_famCylBoxComp_eq]
  rfl

open Classical in





theorem rc21_admComp_subset_reflInter (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    rc21_admComp n 𝒜 ℬ S ⊆ rc10_reflInter 𝒜 ℬ := by
  intro R hR
  rw [rc21_admComp, Finset.mem_filter, decide_eq_true_eq] at hR
  obtain ⟨_, K, _, L, _, hKL, hKA, hLB, hRK, hRL⟩ := hR
  exact rc21_localRefl_mem_reflInter
    ((rc20_traceClass_subset_iff n K S 𝒜).mp hKA)
    ((rc20_traceClass_subset_iff n L S ℬ).mp hLB) hRK hRL





def rc21_localReflSearch (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) : Bool :=
  decide (∀ 𝒯 ∈ (rc21_boxComp n 𝒜 ℬ).powerset,
    𝒯.card ≤ (𝒯.biUnion (rc21_admComp n 𝒜 ℬ)).card)










theorem rc21_localReflSearch_fin2_refuted :
    rc21_localReflSearch 2 ({∅, {0}, {1}} : Finset (Finset (Fin 2)))
      ({{0}, {1}, {0, 1}} : Finset (Finset (Fin 2))) = false := by
  decide










def rc21_symmWitComp (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  univ.filter (fun L => decide (∃ K ∈ (univ : Finset (Finset (Fin n))), Disjoint K L ∧
    rc20_traceClass n K S ⊆ 𝒜 ∧ rc20_traceClass n L S ⊆ ℬ) = true)






theorem rc21_symmDiffMirror_fin2_refuted :
    ((rc21_boxComp 2 ({∅, {0}, {1}}) ({{0}, {1}, {0, 1}})).biUnion
        (fun S => (rc21_symmWitComp 2 ({∅, {0}, {1}}) ({{0}, {1}, {0, 1}}) S).image
          (fun L => symmDiff S L))).card
      < (rc21_boxComp 2 ({∅, {0}, {1}}) ({{0}, {1}, {0, 1}})).card := by
  decide

open Classical in






theorem rc21_wall_holds_refuting_pair :
    #(rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 2))) ({{0}, {1}, {0, 1}}))
      ≤ #(rc10_reflInter ({∅, {0}, {1}} : Finset (Finset (Fin 2))) ({{0}, {1}, {0, 1}})) :=
  rc20_famCylBox_fin2 _ _

open Classical in








theorem rc21_generalReflection_refuting_pair :
    ∃ f : Finset (Fin 2) → Finset (Fin 2),
      Set.InjOn f (rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 2))) ({{0}, {1}, {0, 1}})
        : Set (Finset (Fin 2))) ∧
      ∀ S ∈ rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 2))) ({{0}, {1}, {0, 1}}),
        f S ∈ rc10_reflInter ({∅, {0}, {1}} : Finset (Finset (Fin 2))) ({{0}, {1}, {0, 1}}) := by
  set 𝒜 : Finset (Finset (Fin 2)) := {∅, {0}, {1}} with h𝒜
  set ℬ : Finset (Finset (Fin 2)) := {{0}, {1}, {0, 1}} with hℬ
  have hle := rc20_famCylBox_fin2 𝒜 ℬ
  by_cases hne : (rc20_famCylBox 𝒜 ℬ).Nonempty
  · have hemb : Nonempty ((rc20_famCylBox 𝒜 ℬ) ↪ (rc10_reflInter 𝒜 ℬ)) := by
      rw [← Fintype.card_coe, ← Fintype.card_coe (rc10_reflInter 𝒜 ℬ)] at hle
      exact Function.Embedding.nonempty_of_card_le hle
    obtain ⟨e⟩ := hemb
    have htne : (rc10_reflInter 𝒜 ℬ).Nonempty := by
      rw [← Finset.card_pos]; exact lt_of_lt_of_le (Finset.card_pos.mpr hne) hle
    obtain ⟨t0, ht0⟩ := htne
    refine ⟨fun S => if hS : S ∈ rc20_famCylBox 𝒜 ℬ then (e ⟨S, hS⟩).val else t0, ?_, ?_⟩
    · intro a ha b hb hab
      rw [Finset.mem_coe] at ha hb
      simp only [dif_pos ha, dif_pos hb] at hab
      have : (⟨a, ha⟩ : (rc20_famCylBox 𝒜 ℬ : Finset (Finset (Fin 2)))) = ⟨b, hb⟩ :=
        e.injective (Subtype.ext hab)
      exact congrArg Subtype.val this
    · intro S hS
      simp only [dif_pos hS]
      exact (e ⟨S, hS⟩).property
  · exact ⟨id, fun a ha => by rw [Finset.mem_coe] at ha; exact absurd ⟨a, ha⟩ hne,
      fun S hS => absurd ⟨S, hS⟩ hne⟩



open Classical in


























theorem rc21_reimer_persupport :
    (rc21_SymmDiffReflection → rc18_CylBoxReflInter)
      ∧ (∀ {𝒜 ℬ : Finset (Finset α)} {S K L : Finset α}, Disjoint K L →
          (∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜) →
          (∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ) →
          symmDiff S L ∈ rc10_reflInter 𝒜 ℬ)
      ∧ (rc21_localReflSearch 2 ({∅, {0}, {1}}) ({{0}, {1}, {0, 1}}) = false)
      ∧ (#(rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 2))) ({{0}, {1}, {0, 1}}))
          ≤ #(rc10_reflInter ({∅, {0}, {1}} : Finset (Finset (Fin 2))) ({{0}, {1}, {0, 1}}))) :=
  ⟨rc21_cylBoxReflInter_of_symmDiffReflection,
    fun hKL hKA hLB => rc21_symmDiff_mem_reflInter hKL hKA hLB,
    rc21_localReflSearch_fin2_refuted,
    rc21_wall_holds_refuting_pair⟩

end StatMech.Walls
