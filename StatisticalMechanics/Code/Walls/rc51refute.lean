/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































import Code.Walls.rc50hall

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace












def rc51_neighbourhoodComp (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (rc20_reflInterComp n 𝒜 ℬ).filter (fun R =>
    decide (∃ K ∈ (univ : Finset (Finset (Fin n))), ∃ L ∈ (univ : Finset (Finset (Fin n))),
      Disjoint K L ∧ rc20_traceClass n K S ⊆ 𝒜 ∧ rc20_traceClass n L S ⊆ ℬ ∧
      rc49_jointImage S K L = R) = true)

open Classical in

theorem rc51_neighbourhoodComp_eq (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    rc51_neighbourhoodComp n 𝒜 ℬ S = rc49_neighbourhood 𝒜 ℬ S := by
  ext R
  rw [rc51_neighbourhoodComp, rc49_neighbourhood, Finset.mem_filter, Finset.mem_filter,
    decide_eq_true_eq, rc20_reflInterComp_eq]
  refine and_congr_right (fun _ => ?_)
  constructor
  · rintro ⟨K, _, L, _, hKL, hKA, hLB, hEq⟩
    exact ⟨K, L, hKL, (rc20_traceClass_subset_iff n K S 𝒜).mp hKA,
      (rc20_traceClass_subset_iff n L S ℬ).mp hLB, hEq⟩
  · rintro ⟨K, L, hKL, hKA, hLB, hEq⟩
    exact ⟨K, Finset.mem_univ _, L, Finset.mem_univ _, hKL,
      (rc20_traceClass_subset_iff n K S 𝒜).mpr hKA,
      (rc20_traceClass_subset_iff n L S ℬ).mpr hLB, hEq⟩









def rc51_hallCondComp (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) : Bool :=
  decide (∀ W ∈ (rc20_famCylBoxComp n 𝒜 ℬ).powerset,
    W.card ≤ (W.biUnion (rc51_neighbourhoodComp n 𝒜 ℬ)).card)

open Classical in


theorem rc51_hallCondComp_iff (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) :
    rc51_hallCondComp n 𝒜 ℬ = true ↔ rc49_HallCond 𝒜 ℬ := by
  rw [rc51_hallCondComp, decide_eq_true_eq, rc49_HallCond]
  have hbox : rc20_famCylBoxComp n 𝒜 ℬ = rc20_famCylBox 𝒜 ℬ := rc20_famCylBoxComp_eq n 𝒜 ℬ
  have hnb : ∀ W : Finset (Finset (Fin n)),
      W.biUnion (rc51_neighbourhoodComp n 𝒜 ℬ) = W.biUnion (rc49_neighbourhood 𝒜 ℬ) :=
    fun W => Finset.biUnion_congr rfl (fun S _ => rc51_neighbourhoodComp_eq n 𝒜 ℬ S)
  constructor
  · intro h W hW
    have hWmem : W ∈ (rc20_famCylBoxComp n 𝒜 ℬ).powerset := by
      rw [Finset.mem_powerset, hbox]; exact hW
    have := h W hWmem
    rwa [hnb] at this
  · intro h W hW
    rw [Finset.mem_powerset, hbox] at hW
    have := h W hW
    rwa [hnb]

open Classical in


theorem rc51_not_hallCond_of_comp_false (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (h : rc51_hallCondComp n 𝒜 ℬ = false) : ¬ rc49_HallCond 𝒜 ℬ := by
  intro hHall
  rw [← rc51_hallCondComp_iff] at hHall
  rw [hHall] at h
  exact Bool.noConfusion h






def rc51_Aref : Finset (Finset (Fin 3)) := {∅, {0}, {1}}


def rc51_Bref : Finset (Finset (Fin 3)) := {{0}, {1}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}}

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in



theorem rc51_hallCond_refuter_false :
    rc51_hallCondComp 3 rc51_Aref rc51_Bref = false := by
  rw [rc51_hallCondComp, rc51_Aref, rc51_Bref]; decide

open Classical in



theorem rc51_not_hallCond_refuter : ¬ rc49_HallCond rc51_Aref rc51_Bref :=
  rc51_not_hallCond_of_comp_false 3 rc51_Aref rc51_Bref rc51_hallCond_refuter_false

open Classical in




theorem rc51_not_injectiveSelection_refuter : ¬ rc50_InjectiveSelection rc51_Aref rc51_Bref := by
  intro h
  exact rc51_not_hallCond_refuter ((rc50_hall_iff_injectiveSelection rc51_Aref rc51_Bref).mpr h)

open Classical in




theorem rc51_not_hallDoubled : ¬ rc49_HallDoubled := by
  intro h
  exact rc51_not_hallCond_refuter (h 3 rc51_Aref rc51_Bref)

open Classical in





theorem rc51_not_injectiveSelectionAll : ¬ rc50_InjectiveSelectionAll := by
  intro h
  exact rc51_not_injectiveSelection_refuter (h 3 rc51_Aref rc51_Bref)








set_option maxRecDepth 4000 in


theorem rc51_box_refuter_eq :
    rc20_famCylBox rc51_Aref rc51_Bref = {({0} : Finset (Fin 3)), ({1} : Finset (Fin 3))} := by
  rw [← rc20_famCylBoxComp_eq, rc51_Aref, rc51_Bref]; decide

set_option maxRecDepth 4000 in


theorem rc51_reflInter_refuter_eq :
    rc10_reflInter rc51_Aref rc51_Bref
      = {(∅ : Finset (Fin 3)), ({0} : Finset (Fin 3)), ({1} : Finset (Fin 3))} := by
  rw [← rc20_reflInterComp_eq, rc51_Aref, rc51_Bref]; decide

set_option maxRecDepth 4000 in




theorem rc51_wall_refuter_holds :
    (rc20_famCylBoxComp 3 rc51_Aref rc51_Bref).card
      ≤ (rc20_reflInterComp 3 rc51_Aref rc51_Bref).card := by
  rw [rc51_Aref, rc51_Bref]; decide



open Classical in





























theorem rc51_reimer_route_refuted :
    (rc51_hallCondComp 3 rc51_Aref rc51_Bref = false)
      ∧ ¬ rc49_HallCond rc51_Aref rc51_Bref
      ∧ ¬ rc50_InjectiveSelection rc51_Aref rc51_Bref
      ∧ ¬ rc49_HallDoubled
      ∧ ¬ rc50_InjectiveSelectionAll
      ∧ (rc20_famCylBox rc51_Aref rc51_Bref = {({0} : Finset (Fin 3)), ({1} : Finset (Fin 3))})
      ∧ ((rc20_famCylBoxComp 3 rc51_Aref rc51_Bref).card
          ≤ (rc20_reflInterComp 3 rc51_Aref rc51_Bref).card) :=
  ⟨rc51_hallCond_refuter_false,
    rc51_not_hallCond_refuter,
    rc51_not_injectiveSelection_refuter,
    rc51_not_hallDoubled,
    rc51_not_injectiveSelectionAll,
    rc51_box_refuter_eq,
    rc51_wall_refuter_holds⟩

end StatMech.Walls
