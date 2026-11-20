/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































import Code.Walls.rc69doubledmeasure
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}










noncomputable def rc70_wt (n : ℕ) (q : ℚ) (U : Finset (Fin n ⊕ Fin n)) : ℚ :=
  q ^ U.card * (1 - q) ^ (2 * n - U.card)




noncomputable def rc70_measure (n : ℕ) (q : ℚ) (Fam : Finset (Finset (Fin n ⊕ Fin n))) : ℚ :=
  Fam.sum (rc70_wt n q)











theorem rc70_wt_half (U : Finset (Fin n ⊕ Fin n)) :
    rc70_wt n (1/2) U = (1/2) ^ (2 * n) := by
  unfold rc70_wt
  have hcard : U.card ≤ 2 * n := by
    have := Finset.card_le_univ U
    simpa [Fintype.card_sum, Fintype.card_fin, two_mul] using this
  have : (1 : ℚ) - 1/2 = 1/2 := by norm_num
  rw [this, ← pow_add]
  congr 1
  omega





theorem rc70_measure_half (Fam : Finset (Finset (Fin n ⊕ Fin n))) :
    rc70_measure n (1/2) Fam = Fam.card * (1/2) ^ (2 * n) := by
  unfold rc70_measure
  rw [Finset.sum_congr rfl (fun U _ => rc70_wt_half U)]
  rw [Finset.sum_const, nsmul_eq_mul]






theorem rc70_measure_half_invariant (i : Fin n) (Fam : Finset (Finset (Fin n ⊕ Fin n))) :
    rc70_measure n (1/2) (StatMech.doubleCompress i Fam) = rc70_measure n (1/2) Fam := by
  rw [rc70_measure_half, rc70_measure_half, StatMech.doubleCompress_card]














set_option maxRecDepth 4000 in



theorem rc70_witness_compressed :
    StatMech.doubleCompress 0 (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅})
      = {{Sum.inr 0}} := by decide

set_option maxRecDepth 4000 in


theorem rc70_witness_start :
    StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅} = {∅} := by decide



theorem rc70_measure_increases_at_three_quarters :
    rc70_measure 2 (3/4) (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅}) = 1/256
    ∧ rc70_measure 2 (3/4) (StatMech.doubleCompress 0 (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅})) = 3/256 := by
  constructor
  · rw [rc70_witness_start, rc70_measure, Finset.sum_singleton, rc70_wt]
    norm_num
  · rw [rc70_witness_compressed, rc70_measure, Finset.sum_singleton, rc70_wt, Finset.card_singleton]
    norm_num





theorem rc70_measure_decreases_at_one_quarter :
    rc70_measure 2 (1/4) (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅}) = 81/256
    ∧ rc70_measure 2 (1/4) (StatMech.doubleCompress 0 (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅})) = 27/256 := by
  constructor
  · rw [rc70_witness_start, rc70_measure, Finset.sum_singleton, rc70_wt]
    norm_num
  · rw [rc70_witness_compressed, rc70_measure, Finset.sum_singleton, rc70_wt, Finset.card_singleton]
    norm_num







theorem rc70_weighted_measure_not_monotone :
    (rc70_measure 2 (3/4) (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅})
        < rc70_measure 2 (3/4) (StatMech.doubleCompress 0 (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅})))
    ∧ (rc70_measure 2 (1/4) (StatMech.doubleCompress 0 (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅}))
        < rc70_measure 2 (1/4) (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅})) := by
  refine ⟨?_, ?_⟩
  · rw [rc70_measure_increases_at_three_quarters.1, rc70_measure_increases_at_three_quarters.2]
    norm_num
  · rw [rc70_measure_decreases_at_one_quarter.1, rc70_measure_decreases_at_one_quarter.2]
    norm_num















def rc70_DisjPreserving (n : ℕ) (Fam : Finset (Finset (Fin n ⊕ Fin n))) : Prop :=
  ∀ U ∈ Fam, ∀ i : Fin n, ¬ (Sum.inl i ∈ U ∧ Sum.inr i ∈ U)

instance (n : ℕ) (Fam : Finset (Finset (Fin n ⊕ Fin n))) : Decidable (rc70_DisjPreserving n Fam) := by
  unfold rc70_DisjPreserving; infer_instance






theorem rc70_boxDoubled_disjPreserving (𝒜 ℬ : Finset (Finset (Fin n))) :
    rc70_DisjPreserving n (StatMech.boxDoubled 𝒜 ℬ) := by
  intro U hU i
  rw [StatMech.mem_boxDoubled] at hU
  obtain ⟨S, hS, T, hT, hd, rfl⟩ := hU
  rintro ⟨hl, hr⟩
  rw [StatMech.mem_dbl_inl] at hl
  rw [StatMech.mem_dbl_inr] at hr
  exact (Finset.disjoint_left.mp hd hl) hr

set_option maxRecDepth 4000 in








theorem rc70_doubleCompress_breaks_disjPreserving :
    ¬ rc70_DisjPreserving 2
        (StatMech.doubleCompress 0 (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅})) := by
  decide

set_option maxRecDepth 4000 in




theorem rc70_broken_member_exists :
    ∃ U ∈ StatMech.doubleCompress (0 : Fin 2) (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅}),
      (Sum.inl (0 : Fin 2)) ∈ U ∧ (Sum.inr (0 : Fin 2)) ∈ U := by
  decide





theorem rc70_doubleCompress_card_preserved :
    (StatMech.doubleCompress (0 : Fin 2) (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅})).card
      = (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅}).card :=
  StatMech.doubleCompress_card 0 _












theorem rc70_reimerWprobCore_of_boxUnionBound (h : rc60_BoxUnionBound) : ReimerWprobCore :=
  rc60_reimerWprobCore_of_boxUnionBound h



theorem rc70_reimerWprobCore_of_residue (h : rc69_DoubledMeasureResidue) : ReimerWprobCore :=
  rc69_reimerWprobCore_of_residue h

open Classical in
set_option maxRecDepth 4000 in

























theorem rc70_status :
    
    (∀ (m : ℕ) (Fam : Finset (Finset (Fin m ⊕ Fin m))),
        rc70_measure m (1/2) Fam = Fam.card * (1/2) ^ (2 * m)) ∧
    (∀ (m : ℕ) (i : Fin m) (Fam : Finset (Finset (Fin m ⊕ Fin m))),
        rc70_measure m (1/2) (StatMech.doubleCompress i Fam) = rc70_measure m (1/2) Fam) ∧
    
    ((rc70_measure 2 (3/4) (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅})
        < rc70_measure 2 (3/4) (StatMech.doubleCompress 0 (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅})))
      ∧ (rc70_measure 2 (1/4) (StatMech.doubleCompress 0 (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅}))
        < rc70_measure 2 (1/4) (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅}))) ∧
    
    (∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))), rc70_DisjPreserving m (StatMech.boxDoubled 𝒜 ℬ)) ∧
    (¬ rc70_DisjPreserving 2
        (StatMech.doubleCompress 0 (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅}))) ∧
    
    (rc60_BoxUnionBound → ReimerWprobCore) :=
  ⟨fun _m Fam => rc70_measure_half Fam,
   fun _m i Fam => rc70_measure_half_invariant i Fam,
   rc70_weighted_measure_not_monotone,
   fun _m 𝒜 ℬ => rc70_boxDoubled_disjPreserving 𝒜 ℬ,
   rc70_doubleCompress_breaks_disjPreserving,
   rc70_reimerWprobCore_of_boxUnionBound⟩

end StatMech.Walls
