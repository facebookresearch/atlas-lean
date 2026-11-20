/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




























































import Code.Walls.rc29reconcile

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]








open Classical in



theorem rc30_wall_base (𝒜 ℬ : Finset (Finset α)) :
    #(rc28_famCylBoxE (∅ : Finset α) 𝒜 ℬ) ≤ #(rc14_reflE (∅ : Finset α) 𝒜 ℬ) :=
  rc28_target_empty 𝒜 ℬ
















def rc30_SameSideReflDom : Prop :=
  ∀ (F : Finset α) (𝒜 ℬ : Finset (Finset α)) (a : α),
    #(rc14_reflE F (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a))
        + #(rc14_reflE F (𝒜.memberSubfamily a) (ℬ.memberSubfamily a))
      ≤ #(rc14_reflE F (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a))
        + #(rc14_reflE F (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a))












open Classical in








theorem rc30_wall_of_sameSideReflDom (h : rc30_SameSideReflDom (α := α)) :
    ∀ E : Finset α, ∀ 𝒜 ℬ : Finset (Finset α),
      #(rc28_famCylBoxE E 𝒜 ℬ) ≤ #(rc14_reflE E 𝒜 ℬ) := by
  intro E
  induction E using Finset.strongInduction with
  | _ E ih =>
    intro 𝒜 ℬ
    rcases E.eq_empty_or_nonempty with rfl | ⟨a, haE⟩
    · exact rc30_wall_base 𝒜 ℬ
    · 
      have hbox := rc28_sameSideRecursion 𝒜 ℬ haE
      
      have hIHnn : #(rc28_famCylBoxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a))
          ≤ #(rc14_reflE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a)) :=
        ih (E.erase a) (Finset.erase_ssubset haE) _ _
      have hIHmm : #(rc28_famCylBoxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.memberSubfamily a))
          ≤ #(rc14_reflE (E.erase a) (𝒜.memberSubfamily a) (ℬ.memberSubfamily a)) :=
        ih (E.erase a) (Finset.erase_ssubset haE) _ _
      
      have hdom := h (E.erase a) 𝒜 ℬ a
      
      have hrefl := rc27_reflInterRecursion E 𝒜 ℬ a haE
      omega

open Classical in




theorem rc30_famCylBoxResidue_of_sameSideReflDom
    (h : ∀ {β : Type} [Fintype β] [DecidableEq β], rc30_SameSideReflDom (α := β))
    (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
  have hkey := rc30_wall_of_sameSideReflDom (h (β := Fin n)) univ 𝒜 ℬ
  rwa [rc28_famCylBoxE_univ, rc15_reflE_univ] at hkey














set_option maxRecDepth 10000 in




theorem rc30_sameSideReflDom_false :
    ¬ (#(rc14_reflE ((univ : Finset (Fin 3)).erase 0)
            (({∅} : Finset (Finset (Fin 3))).nonMemberSubfamily 0)
            (({{1, 2}} : Finset (Finset (Fin 3))).nonMemberSubfamily 0))
          + #(rc14_reflE ((univ : Finset (Fin 3)).erase 0)
              (({∅} : Finset (Finset (Fin 3))).memberSubfamily 0)
              (({{1, 2}} : Finset (Finset (Fin 3))).memberSubfamily 0))
        ≤ #(rc14_reflE ((univ : Finset (Fin 3)).erase 0)
              (({∅} : Finset (Finset (Fin 3))).nonMemberSubfamily 0)
              (({{1, 2}} : Finset (Finset (Fin 3))).memberSubfamily 0))
          + #(rc14_reflE ((univ : Finset (Fin 3)).erase 0)
              (({∅} : Finset (Finset (Fin 3))).memberSubfamily 0)
              (({{1, 2}} : Finset (Finset (Fin 3))).nonMemberSubfamily 0))) := by
  rw [← rc28_reflEComp_eq, ← rc28_reflEComp_eq, ← rc28_reflEComp_eq, ← rc28_reflEComp_eq]
  decide



theorem rc30_not_sameSideReflDom_fin3 : ¬ rc30_SameSideReflDom (α := Fin 3) := by
  intro h
  exact rc30_sameSideReflDom_false (h ((univ : Finset (Fin 3)).erase 0) ({∅}) ({{1, 2}}) 0)












set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in




theorem rc30_wall_holds_on_overshoot :
    #(rc28_famCylBoxE (univ : Finset (Fin 3)) ({∅}) ({{1, 2}}))
      ≤ #(rc14_reflE (univ : Finset (Fin 3)) ({∅}) ({{1, 2}})) := by
  rw [← rc28_famCylBoxEComp_eq, ← rc28_reflEComp_eq]
  decide







set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in



theorem rc30_wall_fin2 :
    ∀ 𝒜 ℬ : Finset (Finset (Fin 2)),
      #(rc28_famCylBoxE (univ : Finset (Fin 2)) 𝒜 ℬ)
        ≤ #(rc14_reflE (univ : Finset (Fin 2)) 𝒜 ℬ) := by
  have h : ∀ 𝒜 ℬ : Finset (Finset (Fin 2)),
      #(rc28_famCylBoxEComp 2 univ 𝒜 ℬ) ≤ #(rc28_reflEComp 2 univ 𝒜 ℬ) := by decide
  intro 𝒜 ℬ
  have := h 𝒜 ℬ
  rwa [rc28_famCylBoxEComp_eq, rc28_reflEComp_eq] at this














set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in




theorem rc30_flipCandidate_overshoots :
    #(rc14_reflE (univ : Finset (Fin 3)) ({∅}) ({{1, 2}}))
      < #(rc14_reflE (univ : Finset (Fin 3)) ({∅})
          (rc29_flipA 0 ({{1, 2}} : Finset (Finset (Fin 3))))) := by
  rw [← rc29_flipAComp_eq, ← rc28_reflEComp_eq, ← rc28_reflEComp_eq]
  decide



open Classical in



































theorem rc30_reimer_groundrec :
    (∀ (𝒜 ℬ : Finset (Finset α)),
        #(rc28_famCylBoxE (∅ : Finset α) 𝒜 ℬ) ≤ #(rc14_reflE (∅ : Finset α) 𝒜 ℬ))
      ∧ (rc30_SameSideReflDom (α := α) →
          ∀ E : Finset α, ∀ 𝒜 ℬ : Finset (Finset α),
            #(rc28_famCylBoxE E 𝒜 ℬ) ≤ #(rc14_reflE E 𝒜 ℬ))
      ∧ (¬ rc30_SameSideReflDom (α := Fin 3))
      ∧ (#(rc28_famCylBoxE (univ : Finset (Fin 3)) ({∅}) ({{1, 2}}))
          ≤ #(rc14_reflE (univ : Finset (Fin 3)) ({∅}) ({{1, 2}}))) :=
  ⟨rc30_wall_base, rc30_wall_of_sameSideReflDom, rc30_not_sameSideReflDom_fin3,
    rc30_wall_holds_on_overshoot⟩

end StatMech.Walls
