/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamFourColorBalancedCore











open scoped symmDiff
open Finset

namespace StatMech.Ising

abbrev LPRankFiveCounterVertex := Fin 8
abbrev LPRankFiveCounterSlot := Fin 5
abbrev LPRankFiveCounterOrientation := Fin 16
abbrev LPRankFiveCounterColoring := Fin 1024

namespace LPRankFiveCounterexample

def orientationBit (o : LPRankFiveCounterOrientation) (i : Fin 4) : Bool :=
  o.val.testBit i.val

def colorAt (c : LPRankFiveCounterColoring) (e : LPRankFiveCounterSlot) : Fin 4 :=
  ⟨(c.val / 4 ^ e.val) % 4, Nat.mod_lt _ (by decide)⟩


def ends (o : LPRankFiveCounterOrientation) :
    LPRankFiveCounterSlot -> Sym2 LPRankFiveCounterVertex
  | 0 => if orientationBit o 0 then s((1 : Fin 8), (7 : Fin 8))
      else s((0 : Fin 8), (6 : Fin 8))
  | 1 => if orientationBit o 1 then s((6 : Fin 8), (2 : Fin 8))
      else s((7 : Fin 8), (3 : Fin 8))
  | 2 => if orientationBit o 2 then s((3 : Fin 8), (5 : Fin 8))
      else s((2 : Fin 8), (4 : Fin 8))
  | 3 => if orientationBit o 3 then s((0 : Fin 8), (4 : Fin 8))
      else s((1 : Fin 8), (5 : Fin 8))
  | 4 => s((6 : Fin 8), (7 : Fin 8))

def colorClass (c : LPRankFiveCounterColoring) (a : Fin 4) :
    Finset LPRankFiveCounterSlot :=
  Finset.univ.filter fun e => colorAt c e = a

def rowClass (c : LPRankFiveCounterColoring) (row : Bool) :
    Finset LPRankFiveCounterSlot :=
  Finset.univ.filter fun e => if row then 2 <= colorAt c e else colorAt c e < 2

def adjacent (o : LPRankFiveCounterOrientation)
    (K : Finset LPRankFiveCounterSlot)
    (u v : LPRankFiveCounterVertex) : Prop :=
  ∃ e ∈ K, u ∈ ends o e ∧ v ∈ ends o e ∧ u ≠ v

instance adjacentDecidable (o : LPRankFiveCounterOrientation)
    (K : Finset LPRankFiveCounterSlot) : DecidableRel (adjacent o K) := by
  intro u v
  unfold adjacent
  infer_instance

def componentStep (o : LPRankFiveCounterOrientation)
    (K : Finset LPRankFiveCounterSlot)
    (S : Finset LPRankFiveCounterVertex) : Finset LPRankFiveCounterVertex :=
  Finset.univ.filter fun v => v ∈ S ∨ ∃ u ∈ S, adjacent o K u v

def component (o : LPRankFiveCounterOrientation)
    (K : Finset LPRankFiveCounterSlot)
    (u : LPRankFiveCounterVertex) : Nat → Finset LPRankFiveCounterVertex
  | 0 => {u}
  | n + 1 => componentStep o K (component o K u n)


def reachable (o : LPRankFiveCounterOrientation)
    (K : Finset LPRankFiveCounterSlot)
    (u v : LPRankFiveCounterVertex) : Prop :=
  v ∈ component o K u 8

instance reachableDecidable (o : LPRankFiveCounterOrientation)
    (K : Finset LPRankFiveCounterSlot) : DecidableRel (reachable o K) := by
  intro u v
  unfold reachable component componentStep
  infer_instance

def sources (o : LPRankFiveCounterOrientation)
    (K : Finset LPRankFiveCounterSlot) :
    Finset LPRankFiveCounterVertex :=
  StatMech.Sharpness.RandomCurrent.sources (ends o) K

def boundaryPattern (o : LPRankFiveCounterOrientation)
    (A B : Finset LPRankFiveCounterVertex)
    (c : LPRankFiveCounterColoring) : Prop :=
  sources o (colorClass c 0) = A ∧
    sources o (colorClass c 1) = ∅ ∧
    sources o (colorClass c 2) = B ∧
    sources o (colorClass c 3) = ∅

def pattern (o : LPRankFiveCounterOrientation)
    (A B : Finset LPRankFiveCounterVertex)
    (c : LPRankFiveCounterColoring) : Prop :=
  boundaryPattern o A B c ∧
    ¬ reachable o (rowClass c false) 0 1 ∧
    ¬ reachable o (rowClass c true) 0 1

instance patternDecidable (o : LPRankFiveCounterOrientation)
    (A B : Finset LPRankFiveCounterVertex)
    (c : LPRankFiveCounterColoring) : Decidable (pattern o A B c) := by
  unfold pattern boundaryPattern sources colorClass rowClass
  infer_instance

instance boundaryPatternDecidable (o : LPRankFiveCounterOrientation)
    (A B : Finset LPRankFiveCounterVertex)
    (c : LPRankFiveCounterColoring) : Decidable (boundaryPattern o A B c) := by
  unfold boundaryPattern sources colorClass
  infer_instance

def seamI : Finset LPRankFiveCounterVertex := {2, 3}
def seamJ : Finset LPRankFiveCounterVertex := {4, 5}
def ghosts : Finset LPRankFiveCounterVertex := {0, 1}
def offdiag : Finset LPRankFiveCounterVertex := seamI ∪ seamJ ∪ ghosts

def sourceStates : Finset
    (LPRankFiveCounterOrientation × LPRankFiveCounterColoring) :=
  Finset.univ.filter fun z => pattern z.1 ∅ offdiag z.2

def leftTargetStates : Finset
    (LPRankFiveCounterOrientation × LPRankFiveCounterColoring) :=
  Finset.univ.filter fun z => pattern z.1 seamI (seamJ ∪ ghosts) z.2

def rightTargetStates : Finset
    (LPRankFiveCounterOrientation × LPRankFiveCounterColoring) :=
  Finset.univ.filter fun z => pattern z.1 seamJ (seamI ∪ ghosts) z.2

def orientationLeft : LPRankFiveCounterOrientation := ⟨0, by decide⟩
def orientationRight : LPRankFiveCounterOrientation := ⟨15, by decide⟩
def saturatedColoring : LPRankFiveCounterColoring := ⟨682, by decide⟩

set_option maxRecDepth 100000 in
theorem offdiag_sources_iff : ∀ o K,
    sources o K = offdiag ↔
      (o = orientationLeft ∧ K = Finset.univ) ∨
      (o = orientationRight ∧ K = Finset.univ) := by
  letI inner (o : LPRankFiveCounterOrientation) : Decidable (∀ K,
      sources o K = offdiag ↔
        (o = orientationLeft ∧ K = Finset.univ) ∨
        (o = orientationRight ∧ K = Finset.univ)) :=
    Fintype.decidableForallFintype
  letI outer : Decidable (∀ o K,
      sources o K = offdiag ↔
        (o = orientationLeft ∧ K = Finset.univ) ∨
        (o = orientationRight ∧ K = Finset.univ)) :=
    Fintype.decidableForallFintype
  decide

theorem no_seamI_sources_left : ∀ K : Finset LPRankFiveCounterSlot,
    sources orientationLeft K ≠ seamI := by
  letI : Decidable (∀ K : Finset LPRankFiveCounterSlot,
      sources orientationLeft K ≠ seamI) := Fintype.decidableForallFintype
  decide

theorem no_seamI_sources_right : ∀ K : Finset LPRankFiveCounterSlot,
    sources orientationRight K ≠ seamI := by
  letI : Decidable (∀ K : Finset LPRankFiveCounterSlot,
      sources orientationRight K ≠ seamI) := Fintype.decidableForallFintype
  decide

theorem no_seamJ_sources_left : ∀ K : Finset LPRankFiveCounterSlot,
    sources orientationLeft K ≠ seamJ := by
  letI : Decidable (∀ K : Finset LPRankFiveCounterSlot,
      sources orientationLeft K ≠ seamJ) := Fintype.decidableForallFintype
  decide

theorem no_seamJ_sources_right : ∀ K : Finset LPRankFiveCounterSlot,
    sources orientationRight K ≠ seamJ := by
  letI : Decidable (∀ K : Finset LPRankFiveCounterSlot,
      sources orientationRight K ≠ seamJ) := Fintype.decidableForallFintype
  decide

theorem left_boundary_symmDiff : seamI ∆ (seamJ ∪ ghosts) = offdiag := by
  decide

theorem right_boundary_symmDiff : seamJ ∆ (seamI ∪ ghosts) = offdiag := by
  decide

theorem colorClass_disjoint_zero_two (c : LPRankFiveCounterColoring) :
    Disjoint (colorClass c 0) (colorClass c 2) := by
  rw [Finset.disjoint_left]
  intro e he0 he2
  simp only [colorClass, Finset.mem_filter, Finset.mem_univ, true_and] at he0 he2
  have : (0 : Fin 4) = 2 := he0.symm.trans he2
  omega

theorem not_left_target_boundaryPattern (o) (c) :
    ¬ boundaryPattern o seamI (seamJ ∪ ghosts) c := by
  rintro ⟨h0, _, h2, _⟩
  have hu : sources o (colorClass c 0 ∪ colorClass c 2) = offdiag := by
    unfold sources at h0 h2 ⊢
    rw [StatMech.GrahamGHS.FourColor.sources_union_of_disjoint
      (colorClass_disjoint_zero_two c), h0, h2, left_boundary_symmDiff]
  rcases (offdiag_sources_iff o _).mp hu with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact no_seamI_sources_left _ h0
  · exact no_seamI_sources_right _ h0

theorem not_right_target_boundaryPattern (o) (c) :
    ¬ boundaryPattern o seamJ (seamI ∪ ghosts) c := by
  rintro ⟨h0, _, h2, _⟩
  have hu : sources o (colorClass c 0 ∪ colorClass c 2) = offdiag := by
    unfold sources at h0 h2 ⊢
    rw [StatMech.GrahamGHS.FourColor.sources_union_of_disjoint
      (colorClass_disjoint_zero_two c), h0, h2, right_boundary_symmDiff]
  rcases (offdiag_sources_iff o _).mp hu with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact no_seamJ_sources_left _ h0
  · exact no_seamJ_sources_right _ h0

theorem source_pattern_left : pattern orientationLeft ∅ offdiag saturatedColoring := by
  decide

theorem source_pattern_right : pattern orientationRight ∅ offdiag saturatedColoring := by
  decide

theorem not_left_target_pattern (o) (c) :
    ¬ pattern o seamI (seamJ ∪ ghosts) c := by
  exact fun h => not_left_target_boundaryPattern o c h.1

theorem not_right_target_pattern (o) (c) :
    ¬ pattern o seamJ (seamI ∪ ghosts) c := by
  exact fun h => not_right_target_boundaryPattern o c h.1

theorem sourceState_left_mem :
    (orientationLeft, saturatedColoring) ∈ sourceStates := by
  simp only [sourceStates, Finset.mem_filter, Finset.mem_univ, true_and]
  exact source_pattern_left

theorem sourceState_right_mem :
    (orientationRight, saturatedColoring) ∈ sourceStates := by
  simp only [sourceStates, Finset.mem_filter, Finset.mem_univ, true_and]
  exact source_pattern_right

theorem sourceStates_nonempty : sourceStates.Nonempty :=
  ⟨(orientationLeft, saturatedColoring), sourceState_left_mem⟩

theorem sourceStates_card_ge_two : 2 <= sourceStates.card := by
  have hsub :
      ({(orientationLeft, saturatedColoring),
          (orientationRight, saturatedColoring)} :
        Finset (LPRankFiveCounterOrientation × LPRankFiveCounterColoring)) ⊆
        sourceStates := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact sourceState_left_mem
    · exact sourceState_right_mem
  have hne : orientationLeft ≠ orientationRight := by decide
  have hcard :
      ({(orientationLeft, saturatedColoring),
          (orientationRight, saturatedColoring)} :
        Finset (LPRankFiveCounterOrientation × LPRankFiveCounterColoring)).card = 2 := by
    simp [hne]
  rw [← hcard]
  exact Finset.card_le_card hsub

theorem leftTargetStates_eq_empty : leftTargetStates = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  exact not_left_target_pattern z.1 z.2 (Finset.mem_filter.mp hz).2

theorem rightTargetStates_eq_empty : rightTargetStates = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  exact not_right_target_pattern z.1 z.2 (Finset.mem_filter.mp hz).2

theorem leftTargetStates_card : leftTargetStates.card = 0 := by
  rw [leftTargetStates_eq_empty]
  rfl

theorem rightTargetStates_card : rightTargetStates.card = 0 := by
  rw [rightTargetStates_eq_empty]
  rfl



theorem not_source_card_le_target_card :
    ¬ sourceStates.card ≤ leftTargetStates.card + rightTargetStates.card := by
  rw [leftTargetStates_card, rightTargetStates_card]
  have htwo := sourceStates_card_ge_two
  omega

end LPRankFiveCounterexample
end StatMech.Ising
