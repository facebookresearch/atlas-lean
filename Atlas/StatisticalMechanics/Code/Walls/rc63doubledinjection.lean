/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































import Code.Walls.rc62reflfunctional

set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}









def rc63_dn (i : Fin n) (𝒜 : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  Down.compression i 𝒜


theorem rc63_dn_eq (i : Fin n) (𝒜 : Finset (Finset (Fin n))) :
    rc63_dn i 𝒜 = rc61_dnA i 𝒜 := rfl

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in






theorem rc63_reflInter_downdown_noninc_fin2 :
    ∀ 𝒜 ℬ : Finset (Finset (Fin 2)),
      (rc20_reflInterComp 2 (rc63_dn 0 𝒜) (rc63_dn 0 ℬ)).card
        ≤ (rc20_reflInterComp 2 𝒜 ℬ).card := by
  decide

set_option maxRecDepth 4000 in







theorem rc63_box_downdown_decreases_witness :
    (rc20_famCylBoxComp 2 (rc63_dn 0 ({∅, {0}, {1}} : Finset (Finset (Fin 2)))) (rc63_dn 0 {∅, {0}, {0, 1}})).card
        < (rc20_famCylBoxComp 2 ({∅, {0}, {1}} : Finset (Finset (Fin 2))) {∅, {0}, {0, 1}}).card
    ∧ (rc20_reflInterComp 2 (rc63_dn 0 ({∅, {0}, {1}} : Finset (Finset (Fin 2)))) (rc63_dn 0 {∅, {0}, {0, 1}})).card
        = (rc20_reflInterComp 2 ({∅, {0}, {1}} : Finset (Finset (Fin 2))) {∅, {0}, {0, 1}}).card := by
  refine ⟨?_, ?_⟩ <;> decide

















def rc63_ops : List (Finset (Finset (Fin 2)) → Finset (Finset (Fin 2))) :=
  [ id,
    Down.compression 0, Down.compression 1,
    UV.compression {0} ∅, UV.compression {1} ∅ ]




def rc63_opGood (f g : Finset (Finset (Fin 2)) → Finset (Finset (Fin 2))) : Bool :=
  decide (∀ 𝒜 ℬ : Finset (Finset (Fin 2)),
    (rc20_famCylBoxComp 2 𝒜 ℬ).card ≤ (rc20_famCylBoxComp 2 (f 𝒜) (g ℬ)).card ∧
    (rc20_reflInterComp 2 (f 𝒜) (g ℬ)).card ≤ (rc20_reflInterComp 2 𝒜 ℬ).card)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in 




theorem rc63_downdown_not_good :
    rc63_opGood (Down.compression 0) (Down.compression 0) = false := by
  decide




def rc63_nontrivialPairs :
    List ((Finset (Finset (Fin 2)) → Finset (Finset (Fin 2))) ×
          (Finset (Finset (Fin 2)) → Finset (Finset (Fin 2)))) :=
  (rc63_ops.product rc63_ops).filter (fun p => ¬ (p.1 = id ∧ p.2 = id))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 40000000 in 













theorem rc63_no_opposite_compression_fin2 :
    ∀ p ∈ rc63_nontrivialPairs, rc63_opGood p.1 p.2 = false := by
  decide








set_option maxRecDepth 4000 in



theorem rc63_identity_not_injection_fin2 :
    (∅ : Finset (Fin 2)) ∈ rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {1}}
    ∧ (∅ : Finset (Fin 2)) ∉ rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {1}}
    ∧ rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {1}} = {{0}} := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

set_option maxRecDepth 4000 in










theorem rc63_no_coordinatewise_injection_fin2 :
    rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {1}} = {∅}
    ∧ rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {1}} = {{0}}
    ∧ rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {0, 1}} = {{0}}
    ∧ rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {0, 1}} = {∅} := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide














theorem rc63_fixpoint_wall (𝒜 ℬ : Finset (Finset (Fin 2)))
    (hd : rc62_isDown 2 𝒜 = true) (hu : rc62_isUp 2 ℬ = true) :
    (rc20_famCylBoxComp 2 𝒜 ℬ).card ≤ (rc20_reflInterComp 2 𝒜 ℬ).card :=
  rc62_fixpoint_wall_fin2 𝒜 ℬ hd hu



open Classical in




theorem rc63_reimerWprobCore_of_boxUnionBound (h : rc60_BoxUnionBound) : ReimerWprobCore :=
  rc60_reimerWprobCore_of_boxUnionBound h

open Classical in
set_option maxRecDepth 12000 in
set_option maxHeartbeats 40000000 in 


















theorem rc63_status :
    (∀ 𝒜 ℬ : Finset (Finset (Fin 2)),
        (rc20_reflInterComp 2 (rc63_dn 0 𝒜) (rc63_dn 0 ℬ)).card
          ≤ (rc20_reflInterComp 2 𝒜 ℬ).card) ∧
    ((rc20_famCylBoxComp 2 (rc63_dn 0 ({∅, {0}, {1}} : Finset (Finset (Fin 2)))) (rc63_dn 0 {∅, {0}, {0, 1}})).card
        < (rc20_famCylBoxComp 2 ({∅, {0}, {1}} : Finset (Finset (Fin 2))) {∅, {0}, {0, 1}}).card) ∧
    (∀ p ∈ rc63_nontrivialPairs, rc63_opGood p.1 p.2 = false) ∧
    ((∅ : Finset (Fin 2)) ∈ rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {1}}
      ∧ (∅ : Finset (Fin 2)) ∉ rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {1}}) ∧
    (∀ 𝒜 ℬ : Finset (Finset (Fin 2)),
        rc62_isDown 2 𝒜 = true → rc62_isUp 2 ℬ = true →
        (rc20_famCylBoxComp 2 𝒜 ℬ).card ≤ (rc20_reflInterComp 2 𝒜 ℬ).card) ∧
    (rc60_BoxUnionBound → ReimerWprobCore) :=
  ⟨rc63_reflInter_downdown_noninc_fin2,
   rc63_box_downdown_decreases_witness.1,
   rc63_no_opposite_compression_fin2,
   ⟨rc63_identity_not_injection_fin2.1, rc63_identity_not_injection_fin2.2.1⟩,
   rc63_fixpoint_wall,
   rc63_reimerWprobCore_of_boxUnionBound⟩

end StatMech.Walls
