/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































































import Code.Walls.rc60reimerinjection
import Code.Inequalities.ReimerDoubled

set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}











theorem rc61_boxDoubled_card_invariant (𝒜 ℬ : Finset (Finset (Fin n))) (i : Fin n) :
    (StatMech.doubleCompress i (StatMech.boxDoubled 𝒜 ℬ)).card
      = (StatMech.boxDoubled 𝒜 ℬ).card :=
  StatMech.doubleCompress_card i _





theorem rc61_boxDoubled_card_le_mul (𝒜 ℬ : Finset (Finset (Fin n))) :
    (StatMech.boxDoubled 𝒜 ℬ).card ≤ 𝒜.card * ℬ.card :=
  StatMech.card_boxDoubled_le_mul 𝒜 ℬ





theorem rc61_boxDoubled_card_eq_dpairs (𝒜 ℬ : Finset (Finset (Fin n))) :
    (StatMech.boxDoubled 𝒜 ℬ).card
      = ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).card :=
  StatMech.card_boxDoubled 𝒜 ℬ


















def rc61_upB (i : Fin n) (ℬ : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  UV.compression {i} ∅ ℬ




def rc61_dnA (i : Fin n) (𝒜 : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  Down.compression i 𝒜

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2000000 in 






theorem rc61_reflInter_downUp_mono_fin2 :
    ∀ 𝒜 ℬ : Finset (Finset (Fin 2)),
      (rc20_reflInterComp 2 𝒜 ℬ).card
        ≤ (rc20_reflInterComp 2 (rc61_dnA 0 𝒜) (rc61_upB 0 ℬ)).card := by
  decide

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in 



theorem rc61_reflInter_downUp_mono_fin2_coord1 :
    ∀ 𝒜 ℬ : Finset (Finset (Fin 2)),
      (rc20_reflInterComp 2 𝒜 ℬ).card
        ≤ (rc20_reflInterComp 2 (rc61_dnA 1 𝒜) (rc61_upB 1 ℬ)).card := by
  decide

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2000000 in 




theorem rc61_famCylBox_downUp_mono_fin2 :
    ∀ 𝒜 ℬ : Finset (Finset (Fin 2)),
      (rc20_famCylBoxComp 2 𝒜 ℬ).card
        ≤ (rc20_famCylBoxComp 2 (rc61_dnA 0 𝒜) (rc61_upB 0 ℬ)).card := by
  decide









set_option maxRecDepth 4000 in







theorem rc61_gap_not_downUp_mono_fin2 :
    (rc20_reflInterComp 2 (rc61_dnA 0 ({∅, {0}} : Finset (Finset (Fin 2)))) (rc61_upB 0 {{0}, {1}})).card
        + (rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {1}}).card
      < (rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {1}}).card
        + (rc20_famCylBoxComp 2 (rc61_dnA 0 ({∅, {0}} : Finset (Finset (Fin 2)))) (rc61_upB 0 {{0}, {1}})).card := by
  decide

set_option maxRecDepth 4000 in






theorem rc61_famCylBox_not_subset_reflInter_at_fixpoint_fin2 :
    ¬ (rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {0, 1}}
        ⊆ rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {0, 1}}) := by
  decide

set_option maxRecDepth 4000 in




theorem rc61_fixpoint_witness_is_fixed :
    Down.compression 0 ({∅, {0}} : Finset (Finset (Fin 2))) = {∅, {0}} ∧
    Down.compression 1 ({∅, {0}} : Finset (Finset (Fin 2))) = {∅, {0}} ∧
    UV.compression {0} ∅ ({{0}, {0, 1}} : Finset (Finset (Fin 2))) = {{0}, {0, 1}} ∧
    UV.compression {1} ∅ ({{0}, {0, 1}} : Finset (Finset (Fin 2))) = {{0}, {0, 1}} := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide






















def rc61_DoubledButterflyResidue : Prop := rc60_BoxUnionBound




theorem rc61_reimerWprobCore_of_residue (h : rc61_DoubledButterflyResidue) : ReimerWprobCore :=
  rc60_reimerWprobCore_of_boxUnionBound h





theorem rc61_residue_eq_boxUnionBound : rc61_DoubledButterflyResidue = rc60_BoxUnionBound := rfl




theorem rc61_wall_of_residue (𝒜 ℬ : Finset (Finset (Fin n)))
    (h : #(rc20_famCylBox 𝒜 ℬ) ≤ #((rc20_famCylBox 𝒜 ℬ).biUnion (rc59_nbhd 𝒜 ℬ))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) :=
  rc60_wall_of_boxUnionBound 𝒜 ℬ h



set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in 














theorem rc61_status :
    (∀ (𝒜 ℬ : Finset (Finset (Fin 2))) (i : Fin 2),
        (StatMech.doubleCompress i (StatMech.boxDoubled 𝒜 ℬ)).card = (StatMech.boxDoubled 𝒜 ℬ).card) ∧
    (∀ 𝒜 ℬ : Finset (Finset (Fin 2)),
        (rc20_reflInterComp 2 𝒜 ℬ).card
          ≤ (rc20_reflInterComp 2 (rc61_dnA 0 𝒜) (rc61_upB 0 ℬ)).card) ∧
    ((rc20_reflInterComp 2 (rc61_dnA 0 ({∅, {0}} : Finset (Finset (Fin 2)))) (rc61_upB 0 {{0}, {1}})).card
        + (rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {1}}).card
      < (rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {1}}).card
        + (rc20_famCylBoxComp 2 (rc61_dnA 0 ({∅, {0}} : Finset (Finset (Fin 2)))) (rc61_upB 0 {{0}, {1}})).card) ∧
    (¬ (rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {0, 1}}
        ⊆ rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {0, 1}})) ∧
    (rc61_DoubledButterflyResidue → ReimerWprobCore) :=
  ⟨fun 𝒜 ℬ i => rc61_boxDoubled_card_invariant 𝒜 ℬ i,
   rc61_reflInter_downUp_mono_fin2,
   rc61_gap_not_downUp_mono_fin2,
   rc61_famCylBox_not_subset_reflInter_at_fixpoint_fin2,
   rc61_reimerWprobCore_of_residue⟩

end StatMech.Walls
