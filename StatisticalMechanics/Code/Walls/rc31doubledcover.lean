/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



























































































import Code.Walls.rc30groundrec
import Code.Walls.rc22doublecover

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]










theorem rc31_compl_involutive (S : Finset α) : Sᶜᶜ = S := compl_compl S

open Classical in




theorem rc31_reflInter_swap (𝒜 ℬ : Finset (Finset α)) :
    #(rc10_reflInter 𝒜 ℬ) = #(rc10_reflInter ℬ 𝒜) := by
  apply Finset.card_bij (fun S _ => Sᶜ)
  · intro S hS
    rw [rc20_mem_reflInter] at hS
    rw [rc20_mem_reflInter, compl_compl]
    exact ⟨hS.2, hS.1⟩
  · intro S _ S' _ h
    have := congrArg compl h
    rwa [compl_compl, compl_compl] at this
  · intro T hT
    rw [rc20_mem_reflInter] at hT
    refine ⟨Tᶜ, ?_, by rw [compl_compl]⟩
    rw [rc20_mem_reflInter, compl_compl]
    exact ⟨hT.2, hT.1⟩

open Classical in




theorem rc31_complPairs_swap (𝒜 ℬ : Finset (Finset α)) :
    #(rc22_complPairs 𝒜 ℬ) = #(rc22_complPairs ℬ 𝒜) := by
  apply Finset.card_bij (fun p _ => (p.2, p.1))
  · intro p hp
    rw [rc22_mem_complPairs] at hp
    rw [rc22_mem_complPairs]
    exact ⟨hp.2.1, hp.1, hp.2.2.1.symm, by rw [Finset.union_comm]; exact hp.2.2.2⟩
  · intro p _ q _ h
    have h1 : p.2 = q.2 := (Prod.mk.injEq _ _ _ _ ▸ h).1
    have h2 : p.1 = q.1 := (Prod.mk.injEq _ _ _ _ ▸ h).2
    exact Prod.ext h2 h1
  · intro p hp
    rw [rc22_mem_complPairs] at hp
    refine ⟨(p.2, p.1), ?_, rfl⟩
    rw [rc22_mem_complPairs]
    exact ⟨hp.2.1, hp.1, hp.2.2.1.symm, by rw [Finset.union_comm]; exact hp.2.2.2⟩








open Classical in



theorem rc31_famCylBox_swap (𝒜 ℬ : Finset (Finset α)) :
    rc20_famCylBox 𝒜 ℬ = rc20_famCylBox ℬ 𝒜 := by
  ext S
  rw [rc21_mem_famCylBox, rc21_mem_famCylBox]
  constructor
  · rintro ⟨K, L, hKL, hKA, hLB⟩
    exact ⟨L, K, hKL.symm, hLB, hKA⟩
  · rintro ⟨K, L, hKL, hKB, hLA⟩
    exact ⟨L, K, hKL.symm, hLA, hKB⟩

open Classical in




theorem rc31_wall_symm (𝒜 ℬ : Finset (Finset α)) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) ↔
      #(rc20_famCylBox ℬ 𝒜) ≤ #(rc10_reflInter ℬ 𝒜) := by
  rw [rc31_famCylBox_swap, rc31_reflInter_swap]











open Classical in





theorem rc31_boxWitness_to_complPair {𝒜 ℬ : Finset (Finset α)} {S K L : Finset α}
    (hKL : Disjoint K L) (hKA : ∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜)
    (hLB : ∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ) :
    (symmDiff S L, (symmDiff S L)ᶜ) ∈ rc22_complPairs 𝒜 ℬ := by
  have hmem := rc21_symmDiff_mem_reflInter hKL hKA hLB
  rw [rc20_mem_reflInter] at hmem
  rw [rc22_mem_complPairs]
  exact ⟨hmem.1, hmem.2, disjoint_compl_right, Finset.union_compl _⟩




















set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in







theorem rc31_boxCompressionMono_false :
    ¬ (#(rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 3)))
            ({∅, {0}, {0, 1}, {2}, {0, 2}, {0, 1, 2}}))
        ≤ #(rc20_famCylBox
            (Down.compression 0 ({∅, {0}, {1}} : Finset (Finset (Fin 3))))
            (Down.compression 0 ({∅, {0}, {0, 1}, {2}, {0, 2}, {0, 1, 2}})))) := by
  rw [← rc20_famCylBoxComp_eq, ← rc20_famCylBoxComp_eq]
  decide

open Classical in




theorem rc31_not_boxCompressionMono : ¬ rc22_BoxCompressionMono := by
  intro h
  exact rc31_boxCompressionMono_false
    (h 3 ({∅, {0}, {1}}) ({∅, {0}, {0, 1}, {2}, {0, 2}, {0, 1, 2}}) 0)














set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in





theorem rc31_wall_holds_on_boxDrop :
    #(rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 3)))
        ({∅, {0}, {0, 1}, {2}, {0, 2}, {0, 1, 2}}))
      ≤ #(rc10_reflInter ({∅, {0}, {1}} : Finset (Finset (Fin 3)))
          ({∅, {0}, {0, 1}, {2}, {0, 2}, {0, 1, 2}})) := by
  rw [← rc20_famCylBoxComp_eq, ← rc20_reflInterComp_eq]
  decide













open Classical in







theorem rc31_famCylBoxResidue_of_perSupportReflection (h : rc20_PerSupportReflection) :
    rc20_FamCylBoxResidue :=
  rc20_perSupportReflection_iff_famCylBoxResidue.mp h

open Classical in







theorem rc31_cylBoxReflInter_of_symmDiffReflection (h : rc21_SymmDiffReflection) :
    rc18_CylBoxReflInter :=
  rc21_cylBoxReflInter_of_symmDiffReflection h













open Classical in


theorem rc31_boxDownsetBase_fin0 (𝒜 ℬ : Finset (Finset (Fin 0))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) :=
  rc22_boxDownsetBase_fin0 𝒜 ℬ

open Classical in



theorem rc31_boxDownsetBase_upperSet {n : ℕ} {𝒜 ℬ : Finset (Finset (Fin n))}
    (h𝒜 : IsUpperSet (𝒜 : Set (Finset (Fin n)))) (hℬ : IsUpperSet (ℬ : Set (Finset (Fin n)))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) :=
  rc22_boxDownsetBase_upperSet h𝒜 hℬ










open Classical in





theorem rc31_reflInter_downDown_antitone (i : α) (𝒜 ℬ : Finset (Finset α)) :
    #(rc10_reflInter (Down.compression i 𝒜) (Down.compression i ℬ))
      ≤ #(rc10_reflInter 𝒜 ℬ) :=
  rc22_reflInter_downDown_antitone i 𝒜 ℬ



set_option linter.unusedVariables false in
open Classical in











































theorem rc31_reimer_doubledcover :
    (∀ (𝒜 ℬ : Finset (Finset α)), #(rc10_reflInter 𝒜 ℬ) = #(rc10_reflInter ℬ 𝒜))
      ∧ (∀ (𝒜 ℬ : Finset (Finset α)), rc20_famCylBox 𝒜 ℬ = rc20_famCylBox ℬ 𝒜)
      ∧ (∀ {𝒜 ℬ : Finset (Finset α)} {S K L : Finset α}, Disjoint K L →
          (∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜) →
          (∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ) →
          (symmDiff S L, (symmDiff S L)ᶜ) ∈ rc22_complPairs 𝒜 ℬ)
      ∧ (¬ rc22_BoxCompressionMono)
      ∧ (#(rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 3)))
            ({∅, {0}, {0, 1}, {2}, {0, 2}, {0, 1, 2}}))
          ≤ #(rc10_reflInter ({∅, {0}, {1}} : Finset (Finset (Fin 3)))
              ({∅, {0}, {0, 1}, {2}, {0, 2}, {0, 1, 2}})))
      ∧ (rc20_PerSupportReflection → rc20_FamCylBoxResidue) :=
  ⟨rc31_reflInter_swap,
    rc31_famCylBox_swap,
    fun hKL hKA hLB => rc31_boxWitness_to_complPair hKL hKA hLB,
    rc31_not_boxCompressionMono,
    rc31_wall_holds_on_boxDrop,
    rc31_famCylBoxResidue_of_perSupportReflection⟩

end StatMech.Walls
