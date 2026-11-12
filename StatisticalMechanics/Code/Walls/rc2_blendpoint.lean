/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



























































import Code.Inequalities.ReimerButterflyProve3
import Code.Walls.rc_core

open Finset
open scoped FinsetFamily

namespace StatMech.Walls

open StatMech

variable {α : Type*} [DecidableEq α]

















theorem rc2_blendpoint_converges (𝒜 : Finset (Finset α)) :
    ∃ cs : List α,
      IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset α))
        ∧ (∀ ℬ : Finset (Finset α),
            dpairsCount 𝒜 ℬ ≤ dpairsCount (iterDownComp cs 𝒜) (iterDownComp cs ℬ))
        ∧ (iterDownComp cs 𝒜).card = 𝒜.card := by
  obtain ⟨cs, hcs⟩ := exists_iterDownComp_isLowerSet 𝒜
  exact ⟨cs, hcs, fun ℬ => dpairsCount_iterDownComp_mono cs 𝒜 ℬ, iterDownComp_card cs 𝒜⟩













theorem rc2_blendpoint_favourable {𝒜 ℬ : Finset (Finset α)}
    (h𝒜 : IsLowerSet (𝒜 : Set (Finset α))) (hℬ : IsLowerSet (ℬ : Set (Finset α))) (i : α) :
    dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i)
      ≤ dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i) :=
  dpairsCount_member_le_nonMember_of_isLowerSet h𝒜 hℬ i















theorem rc2_blendpoint :
    (∀ 𝒜 : Finset (Finset α), ∃ cs : List α,
        IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset α))
          ∧ ∀ ℬ : Finset (Finset α),
              dpairsCount 𝒜 ℬ ≤ dpairsCount (iterDownComp cs 𝒜) (iterDownComp cs ℬ))
      ∧ (∀ {𝒜 ℬ : Finset (Finset α)}, IsLowerSet (𝒜 : Set (Finset α)) →
          IsLowerSet (ℬ : Set (Finset α)) → ∀ i : α,
            dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i)
              ≤ dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)) := by
  refine ⟨fun 𝒜 => ?_, fun h𝒜 hℬ i => rc2_blendpoint_favourable h𝒜 hℬ i⟩
  obtain ⟨cs, hcs, hmono, _⟩ := rc2_blendpoint_converges 𝒜
  exact ⟨cs, hcs, hmono⟩













theorem rc2_iterDownComp_append (cs₁ cs₂ : List α) (𝒜 : Finset (Finset α)) :
    iterDownComp (cs₁ ++ cs₂) 𝒜 = iterDownComp cs₁ (iterDownComp cs₂ 𝒜) := by
  unfold iterDownComp; rw [List.foldr_append]











theorem rc2_blendpoint_pair (𝒜 ℬ : Finset (Finset α)) :
    ∃ cs : List α,
      IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset α))
        ∧ IsLowerSet ((iterDownComp cs ℬ) : Set (Finset α))
        ∧ dpairsCount 𝒜 ℬ ≤ dpairsCount (iterDownComp cs 𝒜) (iterDownComp cs ℬ)
        ∧ (iterDownComp cs 𝒜).card = 𝒜.card
        ∧ (iterDownComp cs ℬ).card = ℬ.card := by
  
  obtain ⟨cs₁, hcs₁⟩ := exists_iterDownComp_isLowerSet 𝒜
  
  obtain ⟨cs₂, hcs₂⟩ := exists_iterDownComp_isLowerSet (iterDownComp cs₁ ℬ)
  refine ⟨cs₂ ++ cs₁, ?_, ?_, ?_, ?_, ?_⟩
  · 
    rw [rc2_iterDownComp_append, iterDownComp_eq_self_of_isLowerSet hcs₁ cs₂]
    exact hcs₁
  · rw [rc2_iterDownComp_append]; exact hcs₂
  · exact dpairsCount_iterDownComp_mono (cs₂ ++ cs₁) 𝒜 ℬ
  · rw [iterDownComp_card]
  · rw [iterDownComp_card]


















theorem rc2_blendpoint_deficit_nonneg {𝒜 ℬ : Finset (Finset α)}
    (h𝒜 : IsLowerSet (𝒜 : Set (Finset α))) (hℬ : IsLowerSet (ℬ : Set (Finset α))) (i : α) :
    (0 : ℤ) ≤ (dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) : ℤ)
        - dpairsCount (𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i)
            (ℬ.memberSubfamily i ∩ ℬ.nonMemberSubfamily i)
      ∧ dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i)
          ≤ dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i) :=
  ⟨rc_core_deficit_nonneg 𝒜 ℬ i, rc2_blendpoint_favourable h𝒜 hℬ i⟩










theorem rc2_blendpoint_favourable_self {𝒜 : Finset (Finset α)}
    (h𝒜 : IsLowerSet (𝒜 : Set (Finset α))) (i : α) :
    dpairsCount (𝒜.memberSubfamily i) (𝒜.memberSubfamily i)
      ≤ dpairsCount (𝒜.nonMemberSubfamily i) (𝒜.nonMemberSubfamily i) :=
  rc2_blendpoint_favourable h𝒜 h𝒜 i



theorem rc2_blendpoint_empty :
    IsLowerSet ((iterDownComp ([] : List α) (∅ : Finset (Finset α))) : Set (Finset α))
      ∧ (iterDownComp ([] : List α) (∅ : Finset (Finset α))).card = 0 := by
  refine ⟨?_, by simp⟩
  rw [iterDownComp_nil]
  simp [IsLowerSet]




theorem rc2_blendpoint_univ [Fintype α] :
    IsLowerSet
      ((iterDownComp ([] : List α) (Finset.univ : Finset (Finset α))) : Set (Finset α)) := by
  rw [iterDownComp_nil]
  intro s t _ _
  simp




















end StatMech.Walls
