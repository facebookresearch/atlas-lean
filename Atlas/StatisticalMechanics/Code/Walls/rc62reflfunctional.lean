/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































import Code.Walls.rc61doubledbutterfly

set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}












set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in



theorem rc62_reflInter_ge_box_fin2 :
    ∀ 𝒜 ℬ : Finset (Finset (Fin 2)),
      (rc20_famCylBoxComp 2 𝒜 ℬ).card ≤ (rc20_reflInterComp 2 𝒜 ℬ).card := by
  decide

open Classical in







theorem rc62_forward_chain_only_bounds_fixpoint
    (boxStart Φstart Φfix reflFix : ℕ)
    (ha : boxStart ≤ Φstart) (hc : Φstart ≤ Φfix) (hb : Φfix ≤ reflFix) :
    boxStart ≤ reflFix :=
  ha.trans (hc.trans hb)

set_option maxRecDepth 4000 in








theorem rc62_forward_chain_strict_gap_fin2 :
    (rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {1}}).card = 0
    ∧ (rc20_famCylBoxComp 2 (rc61_dnA 0 ({∅, {0}} : Finset (Finset (Fin 2)))) (rc61_upB 0 {{0}, {1}})).card = 1
    ∧ (rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {1}}).card = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide























def rc62_node₁ : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)) := ({∅, {0}}, {∅, {1}})
def rc62_node₂ : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)) := ({∅, {0}}, {{0}, {0, 1}})
def rc62_node₃ : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)) := ({∅, {0}}, {{0}, {1}})
def rc62_node₄ : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)) := ({∅, {0}}, {{1}, {0, 1}})
def rc62_node₅ : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)) := ({∅, {0}}, {∅, {0}})


def rc62_step (i : Fin 2) (p : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2))) :
    Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)) :=
  (rc61_dnA i p.1, rc61_upB i p.2)

set_option maxRecDepth 4000 in

theorem rc62_edge₁₂ : rc62_step 0 rc62_node₁ = rc62_node₂ := by
  rw [rc62_step, rc62_node₁, rc62_node₂]; refine Prod.ext ?_ ?_ <;> decide

set_option maxRecDepth 4000 in

theorem rc62_edge₃₂ : rc62_step 0 rc62_node₃ = rc62_node₂ := by
  rw [rc62_step, rc62_node₃, rc62_node₂]; refine Prod.ext ?_ ?_ <;> decide

set_option maxRecDepth 4000 in

theorem rc62_edge₃₄ : rc62_step 1 rc62_node₃ = rc62_node₄ := by
  rw [rc62_step, rc62_node₃, rc62_node₄]; refine Prod.ext ?_ ?_ <;> decide

set_option maxRecDepth 4000 in

theorem rc62_edge₅₄ : rc62_step 1 rc62_node₅ = rc62_node₄ := by
  rw [rc62_step, rc62_node₅, rc62_node₄]; refine Prod.ext ?_ ?_ <;> decide

set_option maxRecDepth 4000 in

theorem rc62_node₁_box : (rc20_famCylBoxComp 2 rc62_node₁.1 rc62_node₁.2).card = 1 := by
  rw [rc62_node₁]; decide

set_option maxRecDepth 4000 in

theorem rc62_node₅_refl : (rc20_reflInterComp 2 rc62_node₅.1 rc62_node₅.2).card = 0 := by
  rw [rc62_node₅]; decide

open Classical in








theorem rc62_no_invariant_sandwich
    (Φ : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)) → ℕ)
    (hinv : ∀ (i : Fin 2) (p : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2))),
      Φ (rc62_step i p) = Φ p)
    (hlo : ∀ p : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)),
      (rc20_famCylBoxComp 2 p.1 p.2).card ≤ Φ p)
    (hhi : ∀ p : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)),
      Φ p ≤ (rc20_reflInterComp 2 p.1 p.2).card) :
    False := by
  
  have h12 : Φ rc62_node₁ = Φ rc62_node₂ := by rw [← rc62_edge₁₂, hinv]
  have h32 : Φ rc62_node₃ = Φ rc62_node₂ := by rw [← rc62_edge₃₂, hinv]
  have h34 : Φ rc62_node₃ = Φ rc62_node₄ := by rw [← rc62_edge₃₄, hinv]
  have h54 : Φ rc62_node₅ = Φ rc62_node₄ := by rw [← rc62_edge₅₄, hinv]
  
  have h15 : Φ rc62_node₁ = Φ rc62_node₅ := by
    rw [h12, ← h32, h34, ← h54]
  
  have hlo1 : (1 : ℕ) ≤ Φ rc62_node₁ := by
    have := hlo rc62_node₁; rwa [rc62_node₁_box] at this
  have hhi5 : Φ rc62_node₅ ≤ 0 := by
    have := hhi rc62_node₅; rwa [rc62_node₅_refl] at this
  rw [h15] at hlo1
  omega










set_option maxRecDepth 4000 in





theorem rc62_uniform_overshoots_reflInter :
    (({∅, {0}} : Finset (Finset (Fin 2))).card * ({∅, {0}} : Finset (Finset (Fin 2))).card) / 4
        > (rc20_reflInterComp 2 ({∅, {0}}) ({∅, {0}})).card
    ∧ (rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) ({∅, {0}})).card
        ≤ (({∅, {0}} : Finset (Finset (Fin 2))).card * ({∅, {0}} : Finset (Finset (Fin 2))).card) / 4 := by
  refine ⟨?_, ?_⟩ <;> decide













def rc62_isDown (n : ℕ) (𝒜 : Finset (Finset (Fin n))) : Bool :=
  decide (∀ S ∈ 𝒜, ∀ i : Fin n, i ∈ S → S.erase i ∈ 𝒜)



def rc62_isUp (n : ℕ) (ℬ : Finset (Finset (Fin n))) : Bool :=
  decide (∀ S ∈ ℬ, ∀ i : Fin n, i ∉ S → insert i S ∈ ℬ)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in





theorem rc62_fixpoint_wall_fin2 :
    ∀ 𝒜 ℬ : Finset (Finset (Fin 2)),
      rc62_isDown 2 𝒜 = true → rc62_isUp 2 ℬ = true →
      (rc20_famCylBoxComp 2 𝒜 ℬ).card ≤ (rc20_reflInterComp 2 𝒜 ℬ).card := by
  decide



open Classical in



theorem rc62_reimerWprobCore_of_boxUnionBound (h : rc60_BoxUnionBound) : ReimerWprobCore :=
  rc60_reimerWprobCore_of_boxUnionBound h

open Classical in
set_option maxRecDepth 6000 in
set_option maxHeartbeats 8000000 in














theorem rc62_status :
    (∀ 𝒜 ℬ : Finset (Finset (Fin 2)),
        (rc20_famCylBoxComp 2 𝒜 ℬ).card ≤ (rc20_reflInterComp 2 𝒜 ℬ).card) ∧
    (∀ (Φ : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)) → ℕ),
        (∀ (i : Fin 2) (p : _), Φ (rc62_step i p) = Φ p) →
        (∀ p, (rc20_famCylBoxComp 2 p.1 p.2).card ≤ Φ p) →
        (∀ p, Φ p ≤ (rc20_reflInterComp 2 p.1 p.2).card) → False) ∧
    ((({∅, {0}} : Finset (Finset (Fin 2))).card * ({∅, {0}} : Finset (Finset (Fin 2))).card) / 4
        > (rc20_reflInterComp 2 ({∅, {0}}) ({∅, {0}})).card) ∧
    (∀ 𝒜 ℬ : Finset (Finset (Fin 2)),
        rc62_isDown 2 𝒜 = true → rc62_isUp 2 ℬ = true →
        (rc20_famCylBoxComp 2 𝒜 ℬ).card ≤ (rc20_reflInterComp 2 𝒜 ℬ).card) ∧
    (rc60_BoxUnionBound → ReimerWprobCore) :=
  ⟨rc62_reflInter_ge_box_fin2,
   rc62_no_invariant_sandwich,
   (rc62_uniform_overshoots_reflInter).1,
   rc62_fixpoint_wall_fin2,
   rc62_reimerWprobCore_of_boxUnionBound⟩

end StatMech.Walls
