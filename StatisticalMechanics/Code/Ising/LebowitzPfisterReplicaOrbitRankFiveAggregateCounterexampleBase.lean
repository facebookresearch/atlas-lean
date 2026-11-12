/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitRankFiveCounterexample










open Finset
open scoped symmDiff

namespace StatMech.Ising.LPRankFiveAggregateCounterexample

open LPRankFiveCounterexample

abbrev Seam := Fin 3


def seam : Seam -> Finset LPRankFiveCounterVertex
  | 0 => seamI
  | 1 => seamJ
  | 2 => {6, 7}


def sourceSectorStates (i j : Seam) : Finset
    (LPRankFiveCounterOrientation × LPRankFiveCounterColoring) :=
  Finset.univ.filter fun z =>
    pattern z.1 ∅ (seam i ∆ seam j ∆ ghosts) z.2


def targetSectorStates (i j : Seam) : Finset
    (LPRankFiveCounterOrientation × LPRankFiveCounterColoring) :=
  Finset.univ.filter fun z =>
    pattern z.1 (seam i) (seam j ∆ ghosts) z.2


def sectorOrientations : Seam -> Seam ->
    Finset LPRankFiveCounterOrientation
  | 0, 0 => {4, 11}
  | 0, 1 => {0, 15}
  | 0, 2 => {6, 9}
  | 1, 0 => {0, 15}
  | 1, 1 => {4, 11}
  | 1, 2 => {2, 13}
  | 2, 0 => {6, 9}
  | 2, 1 => {2, 13}
  | 2, 2 => {4, 11}



def targetColoring : LPRankFiveCounterColoring := ⟨170, by decide⟩

set_option maxRecDepth 100000 in

theorem sources_eq_sectorBoundary_iff (i j : Seam)
    (o : LPRankFiveCounterOrientation)
    (K : Finset LPRankFiveCounterSlot) :
    LPRankFiveCounterexample.sources o K =
        seam i ∆ seam j ∆ ghosts ↔
      o ∈ sectorOrientations i j ∧ K = Finset.univ := by
  revert o K
  fin_cases i <;> fin_cases j <;> decide

set_option maxRecDepth 100000 in


theorem sources_eq_empty_of_mem_sectorOrientations
    (i j : Seam) (o : LPRankFiveCounterOrientation)
    (ho : o ∈ sectorOrientations i j)
    (K : Finset LPRankFiveCounterSlot)
    (hK : LPRankFiveCounterexample.sources o K = ∅) :
    K = ∅ := by
  revert o K
  fin_cases i <;> fin_cases j <;> decide

set_option maxRecDepth 100000 in


theorem sources_eq_seam_iff_of_mem_sectorOrientations
    (i j k : Seam) (o : LPRankFiveCounterOrientation)
    (ho : o ∈ sectorOrientations i j)
    (K : Finset LPRankFiveCounterSlot) :
    LPRankFiveCounterexample.sources o K = seam k ↔
      k = 2 ∧ K = {4} := by
  revert o K
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

set_option maxRecDepth 100000 in


theorem saturated_pattern_iff_sectorOrientation (i j : Seam)
    (hij : i ≠ j) (o : LPRankFiveCounterOrientation) :
    pattern o ∅ (seam i ∆ seam j ∆ ghosts) saturatedColoring ↔
      o ∈ sectorOrientations i j := by
  revert o
  fin_cases i <;> fin_cases j <;>
    first | exact (hij rfl).elim | decide

set_option maxRecDepth 100000 in


theorem target_pattern_iff_sectorOrientation (j : Seam)
    (o : LPRankFiveCounterOrientation) :
    pattern o (seam 2) (seam j ∆ ghosts) targetColoring ↔
      o ∈ sectorOrientations 2 j := by
  revert o
  fin_cases j <;> decide

set_option maxRecDepth 100000 in

theorem eq_saturatedColoring_of_colorClass_two_eq_univ
    (c : LPRankFiveCounterColoring) (hc : colorClass c 2 = Finset.univ) :
    c = saturatedColoring := by
  revert c
  decide

set_option maxRecDepth 100000 in


theorem eq_targetColoring_of_colorClasses
    (c : LPRankFiveCounterColoring) (hzero : colorClass c 0 = {4})
    (hunion : colorClass c 0 ∪ colorClass c 2 = Finset.univ) :
    c = targetColoring := by
  revert c
  decide


theorem mem_sourceSectorStates_iff (i j : Seam)
    (hij : i ≠ j)
    (z : LPRankFiveCounterOrientation × LPRankFiveCounterColoring) :
    z ∈ sourceSectorStates i j ↔
      z.1 ∈ sectorOrientations i j ∧ z.2 = saturatedColoring := by
  simp only [sourceSectorStates, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hboundary, _, _⟩
    rcases hboundary with ⟨hzero, _, htwo, _⟩
    have hunion : LPRankFiveCounterexample.sources z.1
        (colorClass z.2 0 ∪ colorClass z.2 2) =
        seam i ∆ seam j ∆ ghosts := by
      unfold LPRankFiveCounterexample.sources at hzero htwo ⊢
      rw [StatMech.GrahamGHS.FourColor.sources_union_of_disjoint
        (colorClass_disjoint_zero_two z.2), hzero, htwo]
      rw [symmDiff_assoc]
      simp
    obtain ⟨ho, hall⟩ :=
      (sources_eq_sectorBoundary_iff i j z.1 _).mp hunion
    have hclassZero : colorClass z.2 0 = ∅ :=
      sources_eq_empty_of_mem_sectorOrientations i j z.1 ho _ hzero
    have hclassTwo : colorClass z.2 2 = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro e
      have he : e ∈ colorClass z.2 0 ∪ colorClass z.2 2 := by
        rw [hall]
        simp
      exact (Finset.mem_union.mp he).resolve_left (by simp [hclassZero])
    exact ⟨ho, eq_saturatedColoring_of_colorClass_two_eq_univ z.2 hclassTwo⟩
  · rintro ⟨ho, hcolor⟩
    rw [hcolor]
    exact (saturated_pattern_iff_sectorOrientation i j hij z.1).mpr ho


theorem mem_targetSectorStates_iff (i j : Seam)
    (z : LPRankFiveCounterOrientation × LPRankFiveCounterColoring) :
    z ∈ targetSectorStates i j ↔
      i = 2 ∧ z.1 ∈ sectorOrientations i j ∧
        z.2 = targetColoring := by
  simp only [targetSectorStates, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hboundary, _, _⟩
    rcases hboundary with ⟨hzero, _, htwo, _⟩
    have hunion : LPRankFiveCounterexample.sources z.1
        (colorClass z.2 0 ∪ colorClass z.2 2) =
        seam i ∆ seam j ∆ ghosts := by
      unfold LPRankFiveCounterexample.sources at hzero htwo ⊢
      rw [StatMech.GrahamGHS.FourColor.sources_union_of_disjoint
        (colorClass_disjoint_zero_two z.2), hzero, htwo]
      rw [symmDiff_assoc]
    obtain ⟨ho, hall⟩ :=
      (sources_eq_sectorBoundary_iff i j z.1 _).mp hunion
    obtain ⟨hi, hclassZero⟩ :=
      (sources_eq_seam_iff_of_mem_sectorOrientations
        i j i z.1 ho _).mp hzero
    subst i
    have hcolor := eq_targetColoring_of_colorClasses z.2 hclassZero hall
    exact ⟨rfl, ho, hcolor⟩
  · rintro ⟨rfl, ho, hcolor⟩
    rw [hcolor]
    exact (target_pattern_iff_sectorOrientation j z.1).mpr ho

theorem sectorOrientations_card (i j : Seam) :
    (sectorOrientations i j).card = 2 := by
  fin_cases i <;> fin_cases j <;> decide


theorem sourceSectorStates_card_of_ne (i j : Seam) (hij : i ≠ j) :
    (sourceSectorStates i j).card = 2 := by
  classical
  have heq : sourceSectorStates i j =
      sectorOrientations i j ×ˢ {saturatedColoring} := by
    ext z
    constructor
    · intro hz
      have hz' := (mem_sourceSectorStates_iff i j hij z).mp hz
      exact Finset.mem_product.mpr ⟨hz'.1, by simp [hz'.2]⟩
    · intro hz
      obtain ⟨ho, hc⟩ := Finset.mem_product.mp hz
      apply (mem_sourceSectorStates_iff i j hij z).mpr
      exact ⟨ho, by simpa using hc⟩
  rw [heq, Finset.card_product, Finset.card_singleton,
    sectorOrientations_card, mul_one]



theorem targetSectorStates_card (i j : Seam) :
    (targetSectorStates i j).card = if i = 2 then 2 else 0 := by
  classical
  by_cases hi : i = 2
  · subst i
    have heq : targetSectorStates 2 j =
        sectorOrientations 2 j ×ˢ {targetColoring} := by
      ext z
      constructor
      · intro hz
        have hz' := (mem_targetSectorStates_iff 2 j z).mp hz
        exact Finset.mem_product.mpr ⟨hz'.2.1, by simp [hz'.2.2]⟩
      · intro hz
        obtain ⟨ho, hc⟩ := Finset.mem_product.mp hz
        apply (mem_targetSectorStates_iff 2 j z).mpr
        exact ⟨rfl, ho, by simpa using hc⟩
    rw [heq, Finset.card_product, Finset.card_singleton,
      sectorOrientations_card, mul_one, if_pos rfl]
  · have heq : targetSectorStates i j = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hi (mem_targetSectorStates_iff i j z |>.mp hz).1
    rw [heq, Finset.card_empty, if_neg hi]

end StatMech.Ising.LPRankFiveAggregateCounterexample
