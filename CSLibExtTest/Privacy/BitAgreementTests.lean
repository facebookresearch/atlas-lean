/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Privacy.BitAgreement
import CSLibExt.Privacy.HypothesisTesting

/-!
# Boundary cases for expected bit agreement

A fixed guess is correct half the time on one fair input bit. Repeating one
fair coin in both output coordinates gives one expected match on two input
bits, despite perfect correlation of the outputs. A mixture of a fixed word
and the input tests the additive privacy budget against the actual score.
-/

namespace CSLibExtTest.Privacy.BitAgreement

open BooleanCube CSLibExt.Privacy.DifferentialPrivacy
open scoped BigOperators

example (G : BoolCube 0 → PMF (BoolCube 0)) : expectedBitAgreement G = 0 := by
  simp [expectedBitAgreement, PMF.expect_const]

private theorem mean_oneBit (f : BoolCube 1 → ℝ) :
    (𝔼 x, f x) = (f (fun _ => true) + f (fun _ => false)) / 2 := by
  have hu : (Finset.univ : Finset (BoolCube 1)) = {fun _ => true, fun _ => false} := by decide
  rw [Fintype.expect_eq_sum_div_card, hu]
  have hne : (fun _ : Fin 1 => true) ≠ (fun _ => false) := by decide
  simp [hne, BoolCube]

example (b : Bool) : expectedBitAgreement (fun _ : BoolCube 1 => PMF.pure (fun _ => b)) = 1/2 := by
  have hp (z : BoolCube 1) (f : BoolCube 1 → ℝ) : (PMF.pure z).expect f = f z := by
    rw [PMF.expect_eq_sum, Finset.sum_eq_single z]
    · simp
    · intro y _ hy
      simp [PMF.pure_apply, hy]
    · simp
  rw [expectedBitAgreement, mean_oneBit, hp, hp]
  cases b <;> norm_num

private theorem coinMean {n : ℕ} (word : Bool → BoolCube n) (f : BoolCube n → ℝ) :
    ((PMF.uniformFintype Bool).map word).expect f = (f (word true) + f (word false)) / 2 := by
  rw [PMF.expect_map, PMF.expect_uniformOfFintype, Fintype.sum_bool, Fintype.card_bool]
  simp [div_eq_inv_mul]

private noncomputable def diagonalCoin : PMF (BoolCube 2) :=
  (PMF.uniformFintype Bool).map (fun b _ => b)

example : IsApproxDP (fun _ : BoolCube 2 => diagonalCoin) ReplaceOne 0 0 ∧
    diagonalCoin.expect (fun y => if y 0 = y 1 then 1 else 0) = 1 ∧
    expectedBitAgreement (fun _ : BoolCube 2 => diagonalCoin) = 1 := by
  refine ⟨isApproxDP_zero_iff.mpr (isDP_const _ _), ?_, ?_⟩
  · norm_num [diagonalCoin, coinMean]
  · unfold expectedBitAgreement
    trans 𝔼 _ : BoolCube 2, (1 : ℝ)
    · apply Finset.expect_congr rfl
      intro x _
      rw [diagonalCoin, coinMean]
      simp only [Fin.sum_univ_two]
      cases x 0 <;> cases x 1 <;> norm_num
    · exact Fintype.expect_const _

-- A single fair choice: output the entire input word or a fixed word.
private noncomputable def halfCopy {n : ℕ} (x : BoolCube n) : PMF (BoolCube n) :=
  (PMF.uniformFintype Bool).map fun b => if b then x else fun _ => false

private theorem halfCopy_private {n : ℕ} : IsApproxDP (@halfCopy n) ReplaceOne 0 (1/2) := by
  apply (CSLibExt.Privacy.HypothesisTesting.isApproxDPFin_iff_isApproxDP ..).mp
  refine ⟨le_rfl, by norm_num, fun x x' _ s => ?_⟩
  have event (z : BoolCube n) : (∑ y ∈ s, (halfCopy z y).toReal) =
      ((if z ∈ s then (1 : ℝ) else 0) + (if (fun _ => false) ∈ s then 1 else 0)) / 2 := by
    simpa [PMF.expect_indicator_decide, halfCopy] using
      coinMean (fun b => if b then z else fun _ => false) (fun y => if y ∈ s then 1 else 0)
  rw [event, event, Real.exp_zero, one_mul]
  split_ifs <;> norm_num

private theorem halfCopy_score : expectedBitAgreement (@halfCopy 1) = 3/4 := by
  rw [expectedBitAgreement, mean_oneBit]
  norm_num [halfCopy, coinMean]

example : IsApproxDP (@halfCopy 1) ReplaceOne 0 (1/2) ∧
    expectedBitAgreement (@halfCopy 1) = (Real.exp 0 + 1/2) / (1 + Real.exp 0) ∧
    ¬IsApproxDP (@halfCopy 1) ReplaceOne 0 0 := by
  refine ⟨halfCopy_private, by norm_num [halfCopy_score], fun h => ?_⟩
  have bad := expectedBitAgreement_le h
  norm_num [halfCopy_score] at bad

end CSLibExtTest.Privacy.BitAgreement
