/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.BooleanCubeSpectral
import Mathlib.Tactic.NormNum

open BooleanCube
open scoped BigOperators

/-! ### Spectral structure of Boolean functions -/

/-- Markov's bound on the weight above degree `2`. -/
example (f : BoolCube 4 → ℝ) :
    ∑ S with (2 : ℝ) < (S.card : ℝ), boolFourierCoeff 4 f S ^ 2 ≤ boolTotalInfluence f / 2 :=
  sum_sq_card_gt_le f (by norm_num)

/-- Proposition 3.2 with `ε = 1/10`. -/
example (f : BoolCube 4 → ℝ) :
    ∑ S with boolTotalInfluence f / (1 / 10) < (S.card : ℝ), boolFourierCoeff 4 f S ^ 2 ≤ 1 / 10 :=
  sum_sq_card_gt_le_of_pos f (by norm_num)

/-- A character has total influence at most its degree. -/
example (S : Finset (Fin 3)) : boolTotalInfluence (cubeChi 3 S) ≤ S.card := by
  refine boolTotalInfluence_le_degree (cubeChi_eq_one_or_neg_one S) fun T hT => ?_
  have hne : T ≠ S := by
    rintro rfl
    exact lt_irrefl _ hT
  simp [boolFourierCoeff_cubeChi, Ne.symm hne]

/-- Rounding a function to its sign: `g = f` itself gives distance `0 ≤ 0`. -/
example (f : BoolCube 3 → ℝ) (hf : ∀ x, f x = 1 ∨ f x = -1) :
    boolDist f f ≤ 𝔼 x, (f x - f x) ^ 2 :=
  boolDist_le_expect_sq_sub hf hf fun x => by rcases hf x with h | h <;> simp [h]

/-- A dictator is monotone, so its influence is its degree-1 coefficient. -/
example : boolInfluence (fun x : BoolCube 3 => cubeVal (x 0)) 0 =
    boolFourierCoeff 3 (fun x => cubeVal (x 0)) {0} := by
  refine boolInfluence_eq_boolFourierCoeff_of_monotone (fun x => ?_) (fun x y hxy => ?_) 0
  · cases x 0 <;> simp
  · have h := hxy 0
    cases hx : x 0 <;> cases hy : y 0 <;> simp_all
    exact absurd h (by decide)

/-- Chow's theorem for a dictator: a Boolean function with the dictator's degree-`≤ 1`
coefficients is the dictator. -/
example (g : BoolCube 2 → ℝ) (hg : ∀ x, g x = 1 ∨ g x = -1)
    (hcoeff : ∀ S : Finset (Fin 2), S.card ≤ 1 →
      boolFourierCoeff 2 g S = boolFourierCoeff 2 (cubeChi 2 {0}) S) :
    g = cubeChi 2 {0} := by
  refine eq_of_boolFourierCoeff_eq_of_ltf (ℓ := cubeChi 2 {0}) (fun S hS => ?_)
    (fun x => ?_) (cubeChi_eq_one_or_neg_one _) hg hcoeff
  · have hne : S ≠ {0} := by
      rintro rfl
      simp at hS
    simp [boolFourierCoeff_cubeChi, Ne.symm hne]
  · rw [cubeChi_mul_self]
    norm_num
