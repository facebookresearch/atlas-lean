/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































import Code.Walls.rc63doubledinjection

set_option linter.style.longLine false



set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}






























def rc64_ReimerLeaf : Prop := rc59_IndepHall


theorem rc64_reimerLeaf_eq : rc64_ReimerLeaf = rc59_IndepHall := rfl


theorem rc64_reimerLeaf_iff :
    rc64_ReimerLeaf ↔
      ∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))),
        ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
          𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card :=
  Iff.rfl






def rc64_BoxUnionBound : Prop := rc60_BoxUnionBound


theorem rc64_boxUnionBound_eq : rc64_BoxUnionBound = rc60_BoxUnionBound := rfl









open Classical in


theorem rc64_boxUnionBound_of_leaf (h : rc64_ReimerLeaf) : rc64_BoxUnionBound :=
  rc60_boxUnionBound_of_indepHall_global h

open Classical in



theorem rc64_wall_of_boxUnionBound (h : rc64_BoxUnionBound) (m : ℕ)
    (𝒜 ℬ : Finset (Finset (Fin m))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) :=
  rc60_wall_of_boxUnionBound 𝒜 ℬ (h m 𝒜 ℬ)

open Classical in


theorem rc64_famCylBoxResidue_of_boxUnionBound (h : rc64_BoxUnionBound) : rc20_FamCylBoxResidue :=
  rc60_famCylBoxResidue_of_boxUnionBound h

open Classical in




theorem rc64_reimerWprobCore_of_boxUnionBound (h : rc64_BoxUnionBound) : ReimerWprobCore :=
  rc60_reimerWprobCore_of_boxUnionBound h

open Classical in

theorem rc64_reimerWprobCore_of_leaf (h : rc64_ReimerLeaf) : ReimerWprobCore :=
  rc64_reimerWprobCore_of_boxUnionBound (rc64_boxUnionBound_of_leaf h)

open Classical in









theorem rc64_reimer_inequality_of_leaf (h : rc64_ReimerLeaf) {E : Type*} [Fintype E] [DecidableEq E]
    {p : ℝ≥0} (hp : p ≤ 1) (A B : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  reimer_inequality_of_core (rc64_reimerWprobCore_of_leaf h) hp A B

open Classical in

theorem rc64_reimer_inequality_of_boxUnionBound (h : rc64_BoxUnionBound)
    {E : Type*} [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1)
    (A B : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  reimer_inequality_of_core (rc64_reimerWprobCore_of_boxUnionBound h) hp A B

open Classical in











theorem rc64_all_reductions :
    (rc64_ReimerLeaf → rc64_BoxUnionBound) ∧
    (rc64_BoxUnionBound → ∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))),
        #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) ∧
    (rc64_BoxUnionBound → ReimerWprobCore) ∧
    (rc64_ReimerLeaf → ReimerWprobCore) ∧
    (∀ (_h : ReimerWprobCore) (E : Type) [Fintype E] [DecidableEq E] (p : ℝ≥0) (hp : p ≤ 1)
        (A B : Set (ConfigSpace E)),
        (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
          ≤ (bernoulliProductMeasure (E := E) p hp).real A
            * (bernoulliProductMeasure (E := E) p hp).real B) :=
  ⟨rc64_boxUnionBound_of_leaf,
   rc64_wall_of_boxUnionBound,
   rc64_reimerWprobCore_of_boxUnionBound,
   rc64_reimerWprobCore_of_leaf,
   fun h _ _ _ _ hp A B => reimer_inequality_of_core h hp A B⟩

























open Classical in













theorem rc64_impossibility_summary :
    
    (∀ (Φ : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)) → ℕ),
        (∀ (i : Fin 2) (p : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2))),
          Φ (rc62_step i p) = Φ p) →
        (∀ p : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)),
          (rc20_famCylBoxComp 2 p.1 p.2).card ≤ Φ p) →
        (∀ p : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)),
          Φ p ≤ (rc20_reflInterComp 2 p.1 p.2).card) → False) ∧
    
    (({∅, {0}} : Finset (Finset (Fin 2))).card * ({∅, {0}} : Finset (Finset (Fin 2))).card / 4
        > (rc20_reflInterComp 2 ({∅, {0}}) ({∅, {0}})).card) ∧
    
    (∀ p ∈ rc63_nontrivialPairs, rc63_opGood p.1 p.2 = false) ∧
    
    ((∅ : Finset (Fin 2)) ∈ rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {1}}
      ∧ (∅ : Finset (Fin 2)) ∉ rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {1}}) ∧
    (rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {1}} = {∅}
      ∧ rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {1}} = {{0}}
      ∧ rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {0, 1}} = {{0}}
      ∧ rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {0, 1}} = {∅}) :=
  ⟨rc62_no_invariant_sandwich,
   rc62_uniform_overshoots_reflInter.1,
   rc63_no_opposite_compression_fin2,
   ⟨rc63_identity_not_injection_fin2.1, rc63_identity_not_injection_fin2.2.1⟩,
   rc63_no_coordinatewise_injection_fin2⟩


















open Classical in


theorem rc64_marriage_empty (𝒜 ℬ : Finset (Finset (Fin n))) :
    (∅ : Finset (Finset (Fin n))).card
      ≤ ((∅ : Finset (Finset (Fin n))).biUnion (rc59_nbhd 𝒜 ℬ)).card :=
  rc60_indepHall_empty 𝒜 ℬ

open Classical in





theorem rc64_marriage_singleton (𝒜 ℬ : Finset (Finset (Fin n))) {S : Finset (Fin n)}
    (hS : S ∈ rc20_famCylBox 𝒜 ℬ) :
    ({S} : Finset (Finset (Fin n))).card
      ≤ (({S} : Finset (Finset (Fin n))).biUnion (rc59_nbhd 𝒜 ℬ)).card :=
  rc60_indepHall_singleton 𝒜 ℬ hS

open Classical in


theorem rc64_marriage_card_le_one (𝒜 ℬ : Finset (Finset (Fin n)))
    (𝒯 : Finset (Finset (Fin n))) (h𝒯 : 𝒯 ⊆ rc20_famCylBox 𝒜 ℬ) (hcard : 𝒯.card ≤ 1) :
    𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card := by
  
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with h0 | h1
  · rw [Finset.card_eq_zero.mp h0]; simp
  · obtain ⟨S, hS⟩ := Finset.card_eq_one.mp h1
    subst hS
    exact rc64_marriage_singleton 𝒜 ℬ (h𝒯 (Finset.mem_singleton_self S))

open Classical in


theorem rc64_marriage_fin2 (𝒜 ℬ : Finset (Finset (Fin 2))) :
    ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card :=
  rc59_indepHall_fin2 𝒜 ℬ

open Classical in





theorem rc64_marriage_fin3_refuter :
    ∀ 𝒯 ∈ (rc20_famCylBox rc32_A3 rc32_B3).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc59_nbhd rc32_A3 rc32_B3)).card :=
  rc59_indepHall_fin3_refuter


def rc64_A3ex2 : Finset (Finset (Fin 3)) := {∅, {0}, {1}, {2}}


def rc64_B3ex2 : Finset (Finset (Fin 3)) := {{0, 1}, {0, 2}, {1, 2}, {0, 1, 2}}

set_option maxHeartbeats 4000000 in 
set_option maxRecDepth 10000 in
open Classical in




theorem rc64_marriage_fin3_ex2 :
    ∀ 𝒯 ∈ (rc20_famCylBox rc64_A3ex2 rc64_B3ex2).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc59_nbhd rc64_A3ex2 rc64_B3ex2)).card :=
  (rc59_indepHall_pair_iff rc64_A3ex2 rc64_B3ex2).mpr
    (rc33_hallOneSidedA_prop_of_bool 3 rc64_A3ex2 rc64_B3ex2 (by rw [rc64_A3ex2, rc64_B3ex2]; decide))






















theorem rc64_status :
    
    (rc64_ReimerLeaf → ReimerWprobCore) ∧
    
    (rc64_BoxUnionBound → ReimerWprobCore) ∧
    
    (rc64_ReimerLeaf → rc64_BoxUnionBound) ∧
    
    (∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))) (𝒯 : Finset (Finset (Fin m))),
        𝒯 ⊆ rc20_famCylBox 𝒜 ℬ → 𝒯.card ≤ 1 →
        𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card) ∧
    
    (∀ (𝒜 ℬ : Finset (Finset (Fin 2))), ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
        𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card) ∧
    
    (∀ 𝒯 ∈ (rc20_famCylBox rc32_A3 rc32_B3).powerset,
        𝒯.card ≤ (𝒯.biUnion (rc59_nbhd rc32_A3 rc32_B3)).card) ∧
    
    (∀ (Φ : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)) → ℕ),
        (∀ (i : Fin 2) (p : _), Φ (rc62_step i p) = Φ p) →
        (∀ p, (rc20_famCylBoxComp 2 p.1 p.2).card ≤ Φ p) →
        (∀ p, Φ p ≤ (rc20_reflInterComp 2 p.1 p.2).card) → False) :=
  ⟨rc64_reimerWprobCore_of_leaf,
   rc64_reimerWprobCore_of_boxUnionBound,
   rc64_boxUnionBound_of_leaf,
   fun _ 𝒜 ℬ 𝒯 h𝒯 hcard => rc64_marriage_card_le_one 𝒜 ℬ 𝒯 h𝒯 hcard,
   rc64_marriage_fin2,
   rc64_marriage_fin3_refuter,
   rc62_no_invariant_sandwich⟩

end StatMech.Walls
