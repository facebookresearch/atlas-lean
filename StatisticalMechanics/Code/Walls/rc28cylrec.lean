/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















import Code.Walls.rc27recursion

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]








open Classical in




noncomputable def rc28_famCylBoxE (E : Finset α) (𝒜 ℬ : Finset (Finset α)) : Finset (Finset α) :=
  E.powerset.filter (fun S => ∃ K L : Finset α, Disjoint K L ∧
    (∀ T : Finset α, T ⊆ E → T ∩ K = S ∩ K → T ∈ 𝒜) ∧
    (∀ T : Finset α, T ⊆ E → T ∩ L = S ∩ L → T ∈ ℬ))

open Classical in

theorem rc28_mem_famCylBoxE (E : Finset α) (𝒜 ℬ : Finset (Finset α)) (S : Finset α) :
    S ∈ rc28_famCylBoxE E 𝒜 ℬ ↔ S ⊆ E ∧ ∃ K L : Finset α, Disjoint K L ∧
      (∀ T : Finset α, T ⊆ E → T ∩ K = S ∩ K → T ∈ 𝒜) ∧
      (∀ T : Finset α, T ⊆ E → T ∩ L = S ∩ L → T ∈ ℬ) := by
  simp only [rc28_famCylBoxE, Finset.mem_filter, Finset.mem_powerset]







def rc28_traceClassE (n : ℕ) (E K S : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  E.powerset.filter (fun T => T ∩ K = S ∩ K)



def rc28_famCylBoxEComp (n : ℕ) (E : Finset (Fin n)) (𝒜 ℬ : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n)) :=
  E.powerset.filter (fun S => decide (∃ K ∈ E.powerset, ∃ L ∈ E.powerset, Disjoint K L ∧
    rc28_traceClassE n E K S ⊆ 𝒜 ∧ rc28_traceClassE n E L S ⊆ ℬ) = true)


theorem rc28_traceClassE_subset_iff (n : ℕ) (E K S : Finset (Fin n)) (𝒜 : Finset (Finset (Fin n))) :
    rc28_traceClassE n E K S ⊆ 𝒜 ↔ ∀ T : Finset (Fin n), T ⊆ E → T ∩ K = S ∩ K → T ∈ 𝒜 := by
  rw [rc28_traceClassE]
  constructor
  · intro h T hTE hT
    exact h (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTE, hT⟩)
  · intro h T hT
    rw [Finset.mem_filter, Finset.mem_powerset] at hT
    exact h T hT.1 hT.2

omit [Fintype α] in


theorem rc28_traceCond_inter_ground {E K S T : Finset α} (hSE : S ⊆ E) (hTE : T ⊆ E) :
    T ∩ (K ∩ E) = S ∩ (K ∩ E) ↔ T ∩ K = S ∩ K := by
  constructor
  · intro h
    ext x
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨hxT, hxK⟩
      have hxE : x ∈ E := hTE hxT
      have : x ∈ T ∩ (K ∩ E) := Finset.mem_inter.mpr ⟨hxT, Finset.mem_inter.mpr ⟨hxK, hxE⟩⟩
      rw [h] at this
      exact ⟨(Finset.mem_inter.mp this).1, hxK⟩
    · rintro ⟨hxS, hxK⟩
      have hxE : x ∈ E := hSE hxS
      have : x ∈ S ∩ (K ∩ E) := Finset.mem_inter.mpr ⟨hxS, Finset.mem_inter.mpr ⟨hxK, hxE⟩⟩
      rw [← h] at this
      exact ⟨(Finset.mem_inter.mp this).1, hxK⟩
  · intro h
    ext x
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨hxT, hxK, hxE⟩
      have : x ∈ T ∩ K := Finset.mem_inter.mpr ⟨hxT, hxK⟩
      rw [h] at this
      exact ⟨(Finset.mem_inter.mp this).1, hxK, hxE⟩
    · rintro ⟨hxS, hxK, hxE⟩
      have : x ∈ S ∩ K := Finset.mem_inter.mpr ⟨hxS, hxK⟩
      rw [← h] at this
      exact ⟨(Finset.mem_inter.mp this).1, hxK, hxE⟩

open Classical in

theorem rc28_famCylBoxEComp_eq (n : ℕ) (E : Finset (Fin n)) (𝒜 ℬ : Finset (Finset (Fin n))) :
    rc28_famCylBoxEComp n E 𝒜 ℬ = rc28_famCylBoxE E 𝒜 ℬ := by
  ext S
  rw [rc28_famCylBoxEComp, rc28_famCylBoxE, Finset.mem_filter, Finset.mem_filter, decide_eq_true_eq]
  refine and_congr_right (fun hSp => ?_)
  rw [Finset.mem_powerset] at hSp
  constructor
  · rintro ⟨K, _, L, _, hKL, hKA, hLB⟩
    exact ⟨K, L, hKL, (rc28_traceClassE_subset_iff n E K S 𝒜).mp hKA,
      (rc28_traceClassE_subset_iff n E L S ℬ).mp hLB⟩
  · rintro ⟨K, L, hKL, hKA, hLB⟩
    refine ⟨K ∩ E, Finset.mem_powerset.mpr Finset.inter_subset_right, L ∩ E,
      Finset.mem_powerset.mpr Finset.inter_subset_right, ?_, ?_, ?_⟩
    · exact Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hKL)
    · rw [rc28_traceClassE_subset_iff]
      intro T hTE hT
      exact hKA T hTE ((rc28_traceCond_inter_ground hSp hTE).mp hT)
    · rw [rc28_traceClassE_subset_iff]
      intro T hTE hT
      exact hLB T hTE ((rc28_traceCond_inter_ground hSp hTE).mp hT)







open Classical in


theorem rc28_famCylBoxE_univ (𝒜 ℬ : Finset (Finset α)) :
    rc28_famCylBoxE univ 𝒜 ℬ = rc20_famCylBox 𝒜 ℬ := by
  ext S
  rw [rc28_mem_famCylBoxE, rc21_mem_famCylBox]
  constructor
  · rintro ⟨_, K, L, hKL, hKA, hLB⟩
    exact ⟨K, L, hKL, fun T hT => hKA T (Finset.subset_univ T) hT,
      fun T hT => hLB T (Finset.subset_univ T) hT⟩
  · rintro ⟨K, L, hKL, hKA, hLB⟩
    exact ⟨Finset.subset_univ S, K, L, hKL, fun T _ hT => hKA T hT, fun T _ hT => hLB T hT⟩














open Classical in





theorem rc28_notMem_fiber_subset {E : Finset α} {𝒜 ℬ : Finset (Finset α)} {a : α}
    {S : Finset α} (hS : S ∈ rc28_famCylBoxE E 𝒜 ℬ) (haS : a ∉ S) :
    S ∈ rc28_famCylBoxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a) := by
  rw [rc28_mem_famCylBoxE] at hS ⊢
  obtain ⟨hSE, K, L, hKL, hKA, hLB⟩ := hS
  have hSF : S ⊆ E.erase a := fun x hx => Finset.mem_erase.mpr ⟨fun h => haS (h ▸ hx), hSE hx⟩
  refine ⟨hSF, K, L, hKL, ?_, ?_⟩
  · intro T hTF hTK
    have hTE : T ⊆ E := hTF.trans (Finset.erase_subset a E)
    have haT : a ∉ T := fun h => (Finset.mem_erase.mp (hTF h)).1 rfl
    exact Finset.mem_nonMemberSubfamily.mpr ⟨hKA T hTE hTK, haT⟩
  · intro T hTF hTL
    have hTE : T ⊆ E := hTF.trans (Finset.erase_subset a E)
    have haT : a ∉ T := fun h => (Finset.mem_erase.mp (hTF h)).1 rfl
    exact Finset.mem_nonMemberSubfamily.mpr ⟨hLB T hTE hTL, haT⟩

omit [Fintype α] in




theorem rc28_insert_trace_eq {K S T : Finset α} {a : α} (haS : a ∈ S) (haT : a ∉ T)
    (h : T ∩ K.erase a = (S.erase a) ∩ K.erase a) :
    (insert a T) ∩ K = S ∩ K := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_insert]
  by_cases hxa : x = a
  · subst hxa
    simp only [haS, true_and]
    tauto
  · constructor
    · rintro ⟨hxT | hxT, hxK⟩
      · exact absurd hxT hxa
      · have : x ∈ T ∩ K.erase a :=
          Finset.mem_inter.mpr ⟨hxT, Finset.mem_erase.mpr ⟨hxa, hxK⟩⟩
        rw [h] at this
        exact ⟨(Finset.mem_erase.mp (Finset.mem_inter.mp this).1).2, hxK⟩
    · rintro ⟨hxS, hxK⟩
      have : x ∈ (S.erase a) ∩ K.erase a :=
        Finset.mem_inter.mpr ⟨Finset.mem_erase.mpr ⟨hxa, hxS⟩, Finset.mem_erase.mpr ⟨hxa, hxK⟩⟩
      rw [← h] at this
      exact ⟨Or.inr (Finset.mem_inter.mp this).1, hxK⟩

open Classical in





theorem rc28_mem_fiber_subset {E : Finset α} {𝒜 ℬ : Finset (Finset α)} {a : α}
    {S : Finset α} (hS : S ∈ rc28_famCylBoxE E 𝒜 ℬ) (haS : a ∈ S) :
    S.erase a ∈ rc28_famCylBoxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.memberSubfamily a) := by
  rw [rc28_mem_famCylBoxE] at hS ⊢
  obtain ⟨hSE, K, L, hKL, hKA, hLB⟩ := hS
  have hSF : S.erase a ⊆ E.erase a := Finset.erase_subset_erase a hSE
  refine ⟨hSF, K.erase a, L.erase a, ?_, ?_, ?_⟩
  · exact Finset.disjoint_of_subset_left (Finset.erase_subset a K)
      (Finset.disjoint_of_subset_right (Finset.erase_subset a L) hKL)
  · intro T hTF hTK
    have haT : a ∉ T := fun h => (Finset.mem_erase.mp (hTF h)).1 rfl
    have hTE : insert a T ⊆ E := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxT
      · exact hSE haS
      · exact (Finset.erase_subset a E) (hTF hxT)
    have htrace : (insert a T) ∩ K = S ∩ K := rc28_insert_trace_eq haS haT hTK
    exact Finset.mem_memberSubfamily.mpr ⟨hKA (insert a T) hTE htrace, haT⟩
  · intro T hTF hTL
    have haT : a ∉ T := fun h => (Finset.mem_erase.mp (hTF h)).1 rfl
    have hTE : insert a T ⊆ E := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxT
      · exact hSE haS
      · exact (Finset.erase_subset a E) (hTF hxT)
    have htrace : (insert a T) ∩ L = S ∩ L := rc28_insert_trace_eq haS haT hTL
    exact Finset.mem_memberSubfamily.mpr ⟨hLB (insert a T) hTE htrace, haT⟩













set_option linter.unusedVariables false in
open Classical in







theorem rc28_sameSideRecursion {E : Finset α} (𝒜 ℬ : Finset (Finset α)) {a : α} (haE : a ∈ E) :
    #(rc28_famCylBoxE E 𝒜 ℬ)
      ≤ #(rc28_famCylBoxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a))
        + #(rc28_famCylBoxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.memberSubfamily a)) := by
  classical
  rw [← Finset.card_filter_add_card_filter_not (s := rc28_famCylBoxE E 𝒜 ℬ) (p := fun S => a ∈ S)]
  have hle_in :
      #((rc28_famCylBoxE E 𝒜 ℬ).filter (fun S => a ∈ S))
        ≤ #(rc28_famCylBoxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.memberSubfamily a)) := by
    apply Finset.card_le_card_of_injOn (fun S => S.erase a)
    · intro S hS
      rw [Finset.mem_coe, Finset.mem_filter] at hS
      exact Finset.mem_coe.mpr (rc28_mem_fiber_subset hS.1 hS.2)
    · intro S hS S' hS' h
      rw [Finset.mem_coe, Finset.mem_filter] at hS hS'
      have := congrArg (insert a) h
      rwa [Finset.insert_erase hS.2, Finset.insert_erase hS'.2] at this
  have hle_notin :
      #((rc28_famCylBoxE E 𝒜 ℬ).filter (fun S => ¬ a ∈ S))
        ≤ #(rc28_famCylBoxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a)) := by
    apply Finset.card_le_card
    intro S hS
    rw [Finset.mem_filter] at hS
    exact rc28_notMem_fiber_subset hS.1 hS.2
  omega







def rc28_reflEComp (n : ℕ) (E : Finset (Fin n)) (𝒜 ℬ : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n)) :=
  E.powerset.filter (fun S => decide (S ∈ 𝒜 ∧ E \ S ∈ ℬ) = true)

open Classical in

theorem rc28_reflEComp_eq (n : ℕ) (E : Finset (Fin n)) (𝒜 ℬ : Finset (Finset (Fin n))) :
    rc28_reflEComp n E 𝒜 ℬ = rc14_reflE E 𝒜 ℬ := by
  ext S
  rw [rc28_reflEComp, rc14_reflE, Finset.mem_filter, Finset.mem_filter, decide_eq_true_eq]



















def rc28_CrossRecursion : Prop :=
  ∀ (E : Finset α) (𝒜 ℬ : Finset (Finset α)) (a : α), a ∈ E →
    #(rc28_famCylBoxE E 𝒜 ℬ)
      ≤ #(rc28_famCylBoxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a))
        + #(rc28_famCylBoxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in







theorem rc28_crossRecursion_false :
    ¬ (#(rc28_famCylBoxE (univ : Finset (Fin 3))
          ({∅, {0}, {1}, {2}, {0, 1}}) ({∅, {0}, {1}, {0, 1}, {0, 2}}))
        ≤ #(rc28_famCylBoxE ((univ : Finset (Fin 3)).erase 0)
              (({∅, {0}, {1}, {2}, {0, 1}} : Finset (Finset (Fin 3))).nonMemberSubfamily 0)
              (({∅, {0}, {1}, {0, 1}, {0, 2}} : Finset (Finset (Fin 3))).memberSubfamily 0))
          + #(rc28_famCylBoxE ((univ : Finset (Fin 3)).erase 0)
              (({∅, {0}, {1}, {2}, {0, 1}} : Finset (Finset (Fin 3))).memberSubfamily 0)
              (({∅, {0}, {1}, {0, 1}, {0, 2}} : Finset (Finset (Fin 3))).nonMemberSubfamily 0))) := by
  rw [← rc28_famCylBoxEComp_eq, ← rc28_famCylBoxEComp_eq, ← rc28_famCylBoxEComp_eq]
  decide












open Classical in


theorem rc28_target_empty (𝒜 ℬ : Finset (Finset α)) :
    #(rc28_famCylBoxE (∅ : Finset α) 𝒜 ℬ) ≤ #(rc14_reflE (∅ : Finset α) 𝒜 ℬ) := by
  apply Finset.card_le_card
  intro S hS
  rw [rc28_mem_famCylBoxE] at hS
  obtain ⟨hSE, K, L, _, hKA, hLB⟩ := hS
  have hS0 : S = ∅ := Finset.subset_empty.mp hSE
  subst hS0
  rw [rc14_mem_reflE]
  refine ⟨Finset.Subset.refl _, ?_, ?_⟩
  · exact hKA ∅ (Finset.Subset.refl _) rfl
  · simpa using hLB ∅ (Finset.Subset.refl _) rfl

open Classical in









theorem rc28_target_of_crossRecursion (h : rc28_CrossRecursion (α := α)) :
    ∀ E : Finset α, ∀ 𝒜 ℬ : Finset (Finset α),
      #(rc28_famCylBoxE E 𝒜 ℬ) ≤ #(rc14_reflE E 𝒜 ℬ) := by
  intro E
  induction E using Finset.strongInduction with
  | _ E ih =>
    intro 𝒜 ℬ
    rcases E.eq_empty_or_nonempty with rfl | ⟨a, haE⟩
    · exact rc28_target_empty 𝒜 ℬ
    · have hIHnm : #(rc28_famCylBoxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a))
          ≤ #(rc14_reflE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a)) :=
        ih (E.erase a) (Finset.erase_ssubset haE) _ _
      have hIHmn : #(rc28_famCylBoxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a))
          ≤ #(rc14_reflE (E.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a)) :=
        ih (E.erase a) (Finset.erase_ssubset haE) _ _
      have hcross := h E 𝒜 ℬ a haE
      have hrefl := rc27_reflInterRecursion E 𝒜 ℬ a haE
      omega













open Classical in






theorem rc28_box_le_sameSide_reflSum {E : Finset α} (𝒜 ℬ : Finset (Finset α)) {a : α} (haE : a ∈ E)
    (hIHnn : #(rc28_famCylBoxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a))
        ≤ #(rc14_reflE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a)))
    (hIHmm : #(rc28_famCylBoxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.memberSubfamily a))
        ≤ #(rc14_reflE (E.erase a) (𝒜.memberSubfamily a) (ℬ.memberSubfamily a))) :
    #(rc28_famCylBoxE E 𝒜 ℬ)
      ≤ #(rc14_reflE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a))
        + #(rc14_reflE (E.erase a) (𝒜.memberSubfamily a) (ℬ.memberSubfamily a)) := by
  have hrec := rc28_sameSideRecursion 𝒜 ℬ haE
  omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in






theorem rc28_sameSide_reflSum_overshoots :
    #(rc14_reflE (univ : Finset (Fin 3)) ({∅}) ({{1, 2}})) <
      #(rc28_reflEComp 3 ((univ : Finset (Fin 3)).erase 0)
          (({∅} : Finset (Finset (Fin 3))).nonMemberSubfamily 0)
          (({{1, 2}} : Finset (Finset (Fin 3))).nonMemberSubfamily 0))
        + #(rc28_reflEComp 3 ((univ : Finset (Fin 3)).erase 0)
            (({∅} : Finset (Finset (Fin 3))).memberSubfamily 0)
            (({{1, 2}} : Finset (Finset (Fin 3))).memberSubfamily 0)) := by
  rw [← rc28_reflEComp_eq]
  decide






set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in





theorem rc28_sameSideRecursion_witness :
    #(rc28_famCylBoxE (univ : Finset (Fin 3))
        ({∅, {0}, {0, 1}, {1}}) ({∅, {0}, {0, 2}, {2}})) = 2
      ∧ #(rc28_famCylBoxE ((univ : Finset (Fin 3)).erase 0)
            (({∅, {0}, {0, 1}, {1}} : Finset (Finset (Fin 3))).nonMemberSubfamily 0)
            (({∅, {0}, {0, 2}, {2}} : Finset (Finset (Fin 3))).nonMemberSubfamily 0)) = 1
      ∧ #(rc28_famCylBoxE ((univ : Finset (Fin 3)).erase 0)
            (({∅, {0}, {0, 1}, {1}} : Finset (Finset (Fin 3))).memberSubfamily 0)
            (({∅, {0}, {0, 2}, {2}} : Finset (Finset (Fin 3))).memberSubfamily 0)) = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (rw [← rc28_famCylBoxEComp_eq]; decide)









open Classical in






theorem rc28_famCylBoxResidue_of_crossRecursion
    (h : ∀ {β : Type} [Fintype β] [DecidableEq β], rc28_CrossRecursion (α := β)) :
    rc20_FamCylBoxResidue := by
  intro n 𝒜 ℬ
  have hkey := rc28_target_of_crossRecursion (h (β := Fin n)) univ 𝒜 ℬ
  rwa [rc28_famCylBoxE_univ, rc15_reflE_univ] at hkey



open Classical in


































theorem rc28_reimer_cylrec :
    (∀ (𝒜 ℬ : Finset (Finset α)), rc28_famCylBoxE univ 𝒜 ℬ = rc20_famCylBox 𝒜 ℬ)
      ∧ (∀ (E : Finset α) (𝒜 ℬ : Finset (Finset α)) (a : α), a ∈ E →
          #(rc28_famCylBoxE E 𝒜 ℬ)
            ≤ #(rc28_famCylBoxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a))
              + #(rc28_famCylBoxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.memberSubfamily a)))
      ∧ (¬ (#(rc28_famCylBoxE (univ : Finset (Fin 3))
              ({∅, {0}, {1}, {2}, {0, 1}}) ({∅, {0}, {1}, {0, 1}, {0, 2}}))
            ≤ #(rc28_famCylBoxE ((univ : Finset (Fin 3)).erase 0)
                  (({∅, {0}, {1}, {2}, {0, 1}} : Finset (Finset (Fin 3))).nonMemberSubfamily 0)
                  (({∅, {0}, {1}, {0, 1}, {0, 2}} : Finset (Finset (Fin 3))).memberSubfamily 0))
              + #(rc28_famCylBoxE ((univ : Finset (Fin 3)).erase 0)
                  (({∅, {0}, {1}, {2}, {0, 1}} : Finset (Finset (Fin 3))).memberSubfamily 0)
                  (({∅, {0}, {1}, {0, 1}, {0, 2}} : Finset (Finset (Fin 3))).nonMemberSubfamily 0))))
      ∧ (rc28_CrossRecursion (α := α) →
          ∀ E : Finset α, ∀ 𝒜 ℬ : Finset (Finset α),
            #(rc28_famCylBoxE E 𝒜 ℬ) ≤ #(rc14_reflE E 𝒜 ℬ)) :=
  ⟨rc28_famCylBoxE_univ,
    fun _ 𝒜 ℬ _ haE => rc28_sameSideRecursion 𝒜 ℬ haE,
    rc28_crossRecursion_false,
    rc28_target_of_crossRecursion⟩

end StatMech.Walls
