/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Phase-complete regrouping of the actual seventh-state pair contributions. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairAdjacentIndices

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem finite_group_smul {ι κ E : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    [AddCommMonoid E] [Module ℝ E] (p : ι → Prop) [DecidablePred p]
    (f : ι → κ) (c : ι → ℝ) (v : κ → E) :
    (∑ i, if p i then c i • v (f i) else 0) =
      ∑ k, (∑ i, if p i ∧ f i = k then c i else 0) • v k := by
  classical
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : p i
  · simp [h, ite_smul]
  · simp [h]

private theorem conditional_add {E : Type*} [AddZeroClass E]
    (p : Prop) [Decidable p] (a b : E) :
    (if p then a + b else 0) = (if p then a else 0) + (if p then b else 0) := by
  by_cases h : p <;> simp [h]

set_option maxRecDepth 10000 in
/-- All eight grouped matrix coefficients retain exactly the checked source phases. -/
theorem monsterNortonLine01PairSeventhMatrix_grouped (k : Fin 8) :
    (∑ e : Fin 64, if monsterNortonLine01PairInverseIsPair e = true ∧
      monsterNortonLine01PairInversePhysicalSlot e = k then
        monsterNortonLine01PairSixthNumerator e else 0) =
          monsterNortonLine01PairSeventhMatrixNumerator k := by
  revert k
  decide +kernel

set_option maxRecDepth 10000 in
/-- The grouped C coefficients include the actual reached pair-family signs. -/
theorem monsterNortonLine01PairSeventhC_grouped (k : Fin 8) :
    (∑ e : Fin 64, if monsterNortonLine01PairInverseIsPair e = true ∧
      monsterNortonLine01PairInversePhysicalSlot e = k then
        monsterNortonLine01PairSixthNumerator e *
          (if monsterNortonLine01PairInversePairSign e = 0 then (1 : ℤ) else -1)
      else 0) = -1 := by
  revert k
  decide +kernel

/-- The complete actual pair contribution is the original eight A and eight C vectors. -/
theorem monsterNortonLine01PairSeventh_pair_regroup :
    (∑ e : Fin 64, if monsterNortonLine01PairInverseIsPair e then
      ((monsterNortonLine01PairSixthNumerator e : ℝ) / 16) •
        trialityABCBasis 0 (monsterNortonLine01PairInversePhysicalPair e) +
      (((monsterNortonLine01PairSixthNumerator e *
        (if monsterNortonLine01PairInversePairSign e = 0 then (1 : ℤ) else -1) : ℤ) : ℝ) /
          16) • trialityABCBasis 2 (monsterNortonLine01PairInversePhysicalPair e)
      else 0) =
      (∑ k : Fin 8, ((monsterNortonLine01PairSeventhMatrixNumerator k : ℝ) / 16) •
        trialityABCBasis 0 (monsterNortonLine01AdjacentPair k)) +
      ∑ k : Fin 8, (-1 / 16 : ℝ) • trialityABCBasis 2 (monsterNortonLine01AdjacentPair k) := by
  simp only [monsterNortonLine01PairInversePhysicalPair_slot, conditional_add,
    Finset.sum_add_distrib]
  rw [finite_group_smul (fun e => monsterNortonLine01PairInverseIsPair e = true)
    monsterNortonLine01PairInversePhysicalSlot
    (fun e => (monsterNortonLine01PairSixthNumerator e : ℝ) / 16)
    (fun k => trialityABCBasis 0 (monsterNortonLine01AdjacentPair k))]
  rw [finite_group_smul (fun e => monsterNortonLine01PairInverseIsPair e = true)
    monsterNortonLine01PairInversePhysicalSlot
    (fun e => ((monsterNortonLine01PairSixthNumerator e *
      (if monsterNortonLine01PairInversePairSign e = 0 then (1 : ℤ) else -1) : ℤ) : ℝ) / 16)
    (fun k => trialityABCBasis 2 (monsterNortonLine01AdjacentPair k))]
  congr 1
  · apply Finset.sum_congr rfl
    intro k _
    congr 1
    have h := congrArg (fun z : ℤ => (z : ℝ) / 16)
      (monsterNortonLine01PairSeventhMatrix_grouped k)
    simpa only [Int.cast_sum, Int.cast_ite, Int.cast_zero, Finset.sum_div,
      ite_div, zero_div] using h
  · apply Finset.sum_congr rfl
    intro k _
    congr 1
    have h := congrArg (fun z : ℤ => (z : ℝ) / 16)
      (monsterNortonLine01PairSeventhC_grouped k)
    simpa only [Int.cast_sum, Int.cast_ite, Int.cast_zero, Int.cast_neg, Int.cast_one,
      Finset.sum_div, ite_div, zero_div] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
