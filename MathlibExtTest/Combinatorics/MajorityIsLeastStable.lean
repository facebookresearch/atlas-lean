/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.MajorityIsLeastStable
import Mathlib.Tactic.NormNum

open BooleanCube
open MathlibExt.Combinatorics.MajorityIsLeastStableAMR127Problem0009Wanted

-- A tied input takes the positive branch of the threshold.
example : majority 2 ![true, false] = 1 := by
  norm_num [majority, Fin.sum_univ_two]

-- Majority itself is among the linear threshold functions in every dimension.
example (n : ℕ) : IsLinearThresholdFunction (majority n) :=
  ⟨0, fun _ => 1, fun x => by simp [majority]⟩

-- One-bit majority is a single coordinate, so its noise stability is exactly ρ.
example (ρ : ℝ) : noiseStability ρ (majority 1) = ρ := by
  have h : majority 1 = cubeChi 1 {0} := by
    funext x
    cases hx : x 0 <;> norm_num [majority, hx]
  rw [h, noiseStability, Finset.sum_eq_single {0}]
  · simp
  · intro S _ hS
    simp [boolFourierCoeff_cubeChi, hS.symm]
  · simp

-- At the first refuted dimension the inequality is strict in the claimed direction.
example : ∃ (f : BoolCube 5 → ℝ) (ρ : ℝ), IsLinearThresholdFunction f ∧ 0 ≤ ρ ∧ ρ ≤ 1 ∧
    noiseStability ρ f < noiseStability ρ (majority 5) := by
  by_contra! h
  apply majorityIsLeastStableForSomeOddAtLeastFive_refuted
  exact ⟨5, by decide, le_rfl, fun f hf ρ hρ hρ' => h f ρ hf hρ hρ'⟩
