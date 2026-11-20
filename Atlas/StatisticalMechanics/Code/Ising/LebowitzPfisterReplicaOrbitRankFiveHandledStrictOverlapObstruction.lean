/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant
















namespace StatMech.Ising.LPRankFiveHandledStrictOverlapObstruction


abbrev Target := Fin 4


abbrev StrictSource := Fin 3


abbrev HandledSource := Fin 2


def flip : Target -> Target
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 2



def Related (z : StrictSource) (y : Target) : Prop :=
  (z.val ≤ 1 ∧ (y.val = 0 ∨ y.val = 2)) ∨
    (z.val = 2 ∧ y.val = 1)

instance relatedDecidable (z : StrictSource) (y : Target) :
    Decidable (Related z y) := by
  unfold Related
  infer_instance

def candidates (z : StrictSource) : Finset Target :=
  Finset.univ.filter (Related z)

def incoming (y : Target) : Finset StrictSource :=
  Finset.univ.filter fun z => Related z y

def incomingDegree (degree : Nat) (y : Target) : Finset StrictSource :=
  Finset.univ.filter fun z => Related z y ∧ (candidates z).card = degree


def rerouteNeighborhood (y : Target) : Finset Target :=
  insert y (insert (flip y)
    (Finset.univ.filter fun y' =>
      ∃ z, z ∈ incoming y ∧ Related z y'))



def center : HandledSource -> Target
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 2

theorem flip_ne (y : Target) : flip y ≠ y := by
  fin_cases y <;> decide

theorem flip_involutive (y : Target) : flip (flip y) = y := by
  fin_cases y <;> decide

theorem center_injective : Function.Injective center := by
  intro a b
  fin_cases a <;> fin_cases b <;> decide


theorem center_ne_flip_center (a b : HandledSource) :
    center a ≠ flip (center b) := by
  fin_cases a <;> fin_cases b <;> decide


theorem candidates_card_eq_one_or_two (z : StrictSource) :
    (candidates z).card = 1 ∨ (candidates z).card = 2 := by
  fin_cases z <;> decide


theorem incoming_classification (y : Target) :
    ((incomingDegree 1 y).card = 0 ∧
        (incomingDegree 2 y).card ≤ 2) ∨
      ((incomingDegree 1 y).card = 1 ∧
        (incomingDegree 2 y).card = 0) := by
  fin_cases y <;> decide



theorem one_add_incoming_card_le_rerouteNeighborhood (y : Target) :
    1 + (incoming y).card ≤ (rerouteNeighborhood y).card := by
  fin_cases y <;> decide



theorem chosen_rerouteNeighborhoods_not_disjoint :
    ¬ Disjoint (rerouteNeighborhood (center 0))
      (rerouteNeighborhood (center 1)) := by
  decide



theorem not_combined_card_le_target :
    ¬ Fintype.card (HandledSource ⊕ StrictSource) ≤
      Fintype.card Target := by
  decide

end StatMech.Ising.LPRankFiveHandledStrictOverlapObstruction

namespace StatMech.Ising.LPRankFiveMultiplicityMateOverlapObstruction






abbrev Target := Fin 2
abbrev StrictSource := Fin 2
abbrev HandledSource := Unit

def flip (y : Target) : Target :=
  ⟨1 - y.val, by omega⟩

def Related (z : StrictSource) (y : Target) : Prop := z = y

instance relatedDecidable (z : StrictSource) (y : Target) :
    Decidable (Related z y) := by
  unfold Related
  infer_instance

def candidates (z : StrictSource) : Finset Target :=
  Finset.univ.filter (Related z)

def incoming (y : Target) : Finset StrictSource :=
  Finset.univ.filter fun z => Related z y

def pairIncoming (y : Target) : Finset StrictSource :=
  incoming y ∪ incoming (flip y)

def component (_y : Target) : Finset Target := Finset.univ

def center (_h : HandledSource) : Target := 0

theorem flip_ne (y : Target) : flip y ≠ y := by
  fin_cases y <;> decide

theorem flip_involutive (y : Target) : flip (flip y) = y := by
  fin_cases y <;> decide

theorem every_source_degree_one (z : StrictSource) :
    (candidates z).card = 1 := by
  fin_cases z <;> decide

theorem every_target_has_one_degree_one_incoming (y : Target) :
    (incoming y).card = 1 := by
  fin_cases y <;> decide

theorem local_center_capacity :
    1 + (incoming (center ())).card ≤ (component (center ())).card := by
  decide


theorem mate_closed_component_has_no_extra_capacity :
    (pairIncoming (center ())).card = (component (center ())).card ∧
      ¬ 1 + (pairIncoming (center ())).card ≤
        (component (center ())).card := by
  decide

theorem not_combined_card_le_target :
    ¬ Fintype.card (HandledSource ⊕ StrictSource) ≤
      Fintype.card Target := by
  decide

end StatMech.Ising.LPRankFiveMultiplicityMateOverlapObstruction

namespace StatMech.Ising.LPRankFiveDegreeTwoCycleOverlapObstruction





abbrev Target := Fin 2
abbrev StrictSource := Fin 2
abbrev HandledSource := Unit

def flip (y : Target) : Target :=
  ⟨1 - y.val, by omega⟩

def Related (_z : StrictSource) (_y : Target) : Prop := True

instance relatedDecidable (z : StrictSource) (y : Target) :
    Decidable (Related z y) := by
  unfold Related
  infer_instance

def candidates (z : StrictSource) : Finset Target :=
  Finset.univ.filter (Related z)

def incoming (y : Target) : Finset StrictSource :=
  Finset.univ.filter fun z => Related z y

def incomingDegree (degree : Nat) (y : Target) : Finset StrictSource :=
  Finset.univ.filter fun z => Related z y ∧ (candidates z).card = degree

def component (_y : Target) : Finset Target := Finset.univ

theorem flip_ne (y : Target) : flip y ≠ y := by
  fin_cases y <;> decide

theorem flip_involutive (y : Target) : flip (flip y) = y := by
  fin_cases y <;> decide


theorem every_source_degree_two (z : StrictSource) :
    (candidates z).card = 2 := by
  fin_cases z <;> decide


theorem both_mates_have_no_degree_one_incoming (y : Target) :
    (incomingDegree 1 y).card = 0 ∧
      (incomingDegree 1 (flip y)).card = 0 := by
  fin_cases y <;> decide


theorem incoming_classification (y : Target) :
    (incomingDegree 1 y).card = 0 ∧
      (incomingDegree 2 y).card ≤ 2 := by
  fin_cases y <;> decide


theorem strict_component_saturated (y : Target) :
    Fintype.card StrictSource = (component y).card := by
  fin_cases y <;> decide


theorem no_component_slack_for_handled (y : Target) :
    ¬ 1 + Fintype.card StrictSource ≤ (component y).card := by
  fin_cases y <;> decide

theorem not_combined_card_le_target :
    ¬ Fintype.card (HandledSource ⊕ StrictSource) ≤
      Fintype.card Target := by
  decide

end StatMech.Ising.LPRankFiveDegreeTwoCycleOverlapObstruction

namespace StatMech.Ising.LPRankFiveDoubledRectangleOverlapObstruction








abbrev Target := Fin 4
abbrev StrictSource := Fin 4
abbrev HandledSource := Unit

def flip : Target -> Target
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 2

def Related (z : StrictSource) (y : Target) : Prop :=
  (z.val ≤ 1 ∧ (y.val = 0 ∨ y.val = 2)) ∨
    (2 ≤ z.val ∧ (y.val = 1 ∨ y.val = 3))

instance relatedDecidable (z : StrictSource) (y : Target) :
    Decidable (Related z y) := by
  unfold Related
  infer_instance

def candidates (z : StrictSource) : Finset Target :=
  Finset.univ.filter (Related z)

def incoming (y : Target) : Finset StrictSource :=
  Finset.univ.filter fun z => Related z y

def incomingDegree (degree : Nat) (y : Target) : Finset StrictSource :=
  Finset.univ.filter fun z => Related z y ∧ (candidates z).card = degree

def rerouteNeighborhood (y : Target) : Finset Target :=
  insert y (insert (flip y)
    (Finset.univ.filter fun y' =>
      ∃ z, z ∈ incoming y ∧ Related z y'))

def component (_y : Target) : Finset Target := Finset.univ

theorem flip_ne (y : Target) : flip y ≠ y := by
  fin_cases y <;> decide

theorem flip_involutive (y : Target) : flip (flip y) = y := by
  fin_cases y <;> decide

theorem every_source_degree_two (z : StrictSource) :
    (candidates z).card = 2 := by
  fin_cases z <;> decide

theorem every_target_has_two_degree_two_incoming (y : Target) :
    (incomingDegree 1 y).card = 0 ∧
      (incomingDegree 2 y).card = 2 := by
  fin_cases y <;> decide




theorem exists_alternate_ne_target_ne_flip
    (z : StrictSource) (y : Target) (hzy : Related z y) :
    ∃ y', Related z y' ∧ y' ≠ y ∧ y' ≠ flip y := by
  fin_cases z <;> fin_cases y <;> decide


theorem one_add_incoming_card_le_rerouteNeighborhood (y : Target) :
    1 + (incoming y).card ≤ (rerouteNeighborhood y).card := by
  fin_cases y <;> decide



theorem strict_component_saturated (y : Target) :
    Fintype.card StrictSource = (component y).card := by
  fin_cases y <;> decide

theorem no_component_slack_for_handled (y : Target) :
    ¬ 1 + Fintype.card StrictSource ≤ (component y).card := by
  fin_cases y <;> decide

theorem not_combined_card_le_target :
    ¬ Fintype.card (HandledSource ⊕ StrictSource) ≤
      Fintype.card Target := by
  decide

end StatMech.Ising.LPRankFiveDoubledRectangleOverlapObstruction
