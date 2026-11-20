/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































import Code.Walls.rc23boxmono
import Code.Walls.rc2_dpairsdowndownmono

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]








omit [Fintype α] in



theorem rc24_traceCond_antitone {K₁ K₂ S T : Finset α} (h : K₁ ⊆ K₂)
    (hT : T ∩ K₂ = S ∩ K₂) : T ∩ K₁ = S ∩ K₁ := by
  ext x
  simp only [Finset.mem_inter]
  constructor
  · rintro ⟨hxT, hxK₁⟩
    have hx2 : x ∈ T ∩ K₂ := Finset.mem_inter.mpr ⟨hxT, h hxK₁⟩
    rw [hT] at hx2
    exact ⟨(Finset.mem_inter.mp hx2).1, hxK₁⟩
  · rintro ⟨hxS, hxK₁⟩
    have hx2 : x ∈ S ∩ K₂ := Finset.mem_inter.mpr ⟨hxS, h hxK₁⟩
    rw [← hT] at hx2
    exact ⟨(Finset.mem_inter.mp hx2).1, hxK₁⟩







open Classical in



noncomputable def rc24_complCylBox (𝒜 ℬ : Finset (Finset α)) : Finset (Finset α) :=
  univ.filter (fun S => ∃ K : Finset α,
    (∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜) ∧
    (∀ T : Finset α, T ∩ Kᶜ = S ∩ Kᶜ → T ∈ ℬ))

open Classical in

theorem rc24_mem_complCylBox (𝒜 ℬ : Finset (Finset α)) (S : Finset α) :
    S ∈ rc24_complCylBox 𝒜 ℬ ↔ ∃ K : Finset α,
      (∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜) ∧
      (∀ T : Finset α, T ∩ Kᶜ = S ∩ Kᶜ → T ∈ ℬ) := by
  rw [rc24_complCylBox, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩









open Classical in



theorem rc24_complCylBox_subset_famCylBox (𝒜 ℬ : Finset (Finset α)) :
    rc24_complCylBox 𝒜 ℬ ⊆ rc20_famCylBox 𝒜 ℬ := by
  intro S hS
  rw [rc24_mem_complCylBox] at hS
  obtain ⟨K, hKA, hKcB⟩ := hS
  rw [rc21_mem_famCylBox]
  exact ⟨K, Kᶜ, disjoint_compl_right, hKA, hKcB⟩

open Classical in






theorem rc24_famCylBox_subset_complCylBox (𝒜 ℬ : Finset (Finset α)) :
    rc20_famCylBox 𝒜 ℬ ⊆ rc24_complCylBox 𝒜 ℬ := by
  intro S hS
  rw [rc21_mem_famCylBox] at hS
  obtain ⟨K, L, hKL, hKA, hLB⟩ := hS
  rw [rc24_mem_complCylBox]
  refine ⟨K, hKA, ?_⟩
  have hLKc : L ⊆ Kᶜ := Finset.subset_compl_iff_disjoint_right.mpr hKL.symm
  intro T hT
  exact hLB T (rc24_traceCond_antitone hLKc hT)

open Classical in






theorem rc24_famCylBox_eq_complCylBox (𝒜 ℬ : Finset (Finset α)) :
    rc20_famCylBox 𝒜 ℬ = rc24_complCylBox 𝒜 ℬ :=
  Finset.Subset.antisymm (rc24_famCylBox_subset_complCylBox 𝒜 ℬ)
    (rc24_complCylBox_subset_famCylBox 𝒜 ℬ)










theorem rc24_upComp_eq_complConj (i : α) (𝒜 : Finset (Finset α)) :
    rc22_upComp i 𝒜 = (Down.compression i (𝒜.image compl)).image compl := by
  have hid : (𝒜.image compl).image compl = 𝒜 := by rw [Finset.image_image]; simp
  have h := rc22_complImage_downCompression i (𝒜.image compl)
  rw [hid] at h
  exact h.symm












open Classical in








def rc24_BoxDownUpMono : Prop :=
  ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (i : Fin n),
    #(rc20_famCylBox 𝒜 ℬ)
      ≤ #(rc20_famCylBox (Down.compression i 𝒜) (rc22_upComp i ℬ))




def rc24_upCompComp (n : ℕ) (i : Fin n) (𝒜 : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  (Down.compression i (𝒜.image (fun S => Sᶜ))).image (fun S => Sᶜ)


theorem rc24_upCompComp_eq (n : ℕ) (i : Fin n) (𝒜 : Finset (Finset (Fin n))) :
    rc24_upCompComp n i 𝒜 = rc22_upComp i 𝒜 := by
  rw [rc24_upCompComp, rc24_upComp_eq_complConj]

set_option maxHeartbeats 4000000 in









theorem rc24_boxDownUpMono_fin2 (𝒜 ℬ : Finset (Finset (Fin 2))) (i : Fin 2) :
    #(rc20_famCylBox 𝒜 ℬ)
      ≤ #(rc20_famCylBox (Down.compression i 𝒜) (rc22_upComp i ℬ)) := by
  rw [← rc24_upCompComp_eq, ← rc20_famCylBoxComp_eq, ← rc20_famCylBoxComp_eq]
  revert 𝒜 ℬ i
  decide




















open Classical in








theorem rc24_reflInter_downUp_increases :
    #(rc10_reflInter ({∅} : Finset (Finset (Fin 2))) ({{0}}))
      < #(rc10_reflInter (Down.compression 1 ({∅} : Finset (Finset (Fin 2))))
          (rc22_upComp 1 ({{0}} : Finset (Finset (Fin 2))))) := by
  rw [← rc24_upCompComp_eq, ← rc20_reflInterComp_eq, ← rc20_reflInterComp_eq]
  decide















open Classical in






theorem rc24_famCylBox_violates_fiberRecursion :
    #(rc20_famCylBox ({∅} : Finset (Finset (Fin 2))) (univ))
      ≠ #(rc20_famCylBox (({∅} : Finset (Finset (Fin 2))).nonMemberSubfamily 0)
            ((univ : Finset (Finset (Fin 2))).nonMemberSubfamily 0))
        + #(rc20_famCylBox (({∅} : Finset (Finset (Fin 2))).memberSubfamily 0)
            ((univ : Finset (Finset (Fin 2))).nonMemberSubfamily 0))
        + #(rc20_famCylBox (({∅} : Finset (Finset (Fin 2))).nonMemberSubfamily 0)
            ((univ : Finset (Finset (Fin 2))).memberSubfamily 0)) := by
  rw [← rc20_famCylBoxComp_eq, ← rc20_famCylBoxComp_eq, ← rc20_famCylBoxComp_eq,
    ← rc20_famCylBoxComp_eq]
  decide



open Classical in




























theorem rc24_reimer_countbridge :
    (∀ (𝒜 ℬ : Finset (Finset α)), rc20_famCylBox 𝒜 ℬ = rc24_complCylBox 𝒜 ℬ)
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 2))) (i : Fin 2),
          #(rc20_famCylBox 𝒜 ℬ)
            ≤ #(rc20_famCylBox (Down.compression i 𝒜) (rc22_upComp i ℬ)))
      ∧ (#(rc10_reflInter ({∅} : Finset (Finset (Fin 2))) ({{0}}))
          < #(rc10_reflInter (Down.compression 1 ({∅} : Finset (Finset (Fin 2))))
              (rc22_upComp 1 ({{0}} : Finset (Finset (Fin 2))))))
      ∧ (#(rc20_famCylBox ({∅} : Finset (Finset (Fin 2))) (univ))
          ≠ #(rc20_famCylBox (({∅} : Finset (Finset (Fin 2))).nonMemberSubfamily 0)
                ((univ : Finset (Finset (Fin 2))).nonMemberSubfamily 0))
            + #(rc20_famCylBox (({∅} : Finset (Finset (Fin 2))).memberSubfamily 0)
                ((univ : Finset (Finset (Fin 2))).nonMemberSubfamily 0))
            + #(rc20_famCylBox (({∅} : Finset (Finset (Fin 2))).nonMemberSubfamily 0)
                ((univ : Finset (Finset (Fin 2))).memberSubfamily 0))) :=
  ⟨rc24_famCylBox_eq_complCylBox, rc24_boxDownUpMono_fin2, rc24_reflInter_downUp_increases,
    rc24_famCylBox_violates_fiberRecursion⟩

end StatMech.Walls
