/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.BooleanCubeNoiseStability
import Mathlib.Tactic.NormNum

open BooleanCube
open scoped BigOperators

/-! ### Noise stability on the Boolean cube -/

/-- A character has noise stability `ρ ^ |S|`, read off from the Fourier formula. -/
example (ρ : ℝ) (S : Finset (Fin 3)) : boolNoiseStab ρ (cubeChi 3 S) = ρ ^ S.card := by
  rw [boolNoiseStab_eq_sum, Finset.sum_eq_single S]
  · simp
  · intro T _ hT
    simp [boolFourierCoeff_cubeChi, Ne.symm hT]
  · simp

/-- The Fourier formula on a concrete dictator. -/
example (ρ : ℝ) : boolNoiseStab ρ (fun x : BoolCube 2 => cubeVal (x 0)) = ρ := by
  have h : (fun x : BoolCube 2 => cubeVal (x 0)) = cubeChi 2 {0} := by
    funext x
    simp
  rw [h, boolNoiseStab_eq_sum, Finset.sum_eq_single {0}]
  · simp
  · intro T _ hT
    simp [boolFourierCoeff_cubeChi, Ne.symm hT]
  · simp

/-- Self-adjointness of the noise operator, instantiated. -/
example (f g : BoolCube 4 → ℝ) :
    𝔼 x, boolNoiseOp (1 / 2) f x * g x = 𝔼 x, f x * boolNoiseOp (1 / 2) g x :=
  expect_boolNoiseOp_mul_comm _ f g

/-- `Stab_{1/4}[f] = 𝔼[(T_{1/2} f)²]`. -/
example (f : BoolCube 4 → ℝ) :
    boolNoiseStab (1 / 4) f = 𝔼 x, boolNoiseOp (1 / 2) f x ^ 2 := by
  have h : ((1 : ℝ) / 4) = (1 / 2) ^ 2 := by norm_num
  rw [h, boolNoiseStab_sq_eq_expect_sq]

/-- For `|ρ| ≤ 1`, noise stability is bounded by the second moment. -/
example (f : BoolCube 4 → ℝ) : boolNoiseStab (-1 / 3) f ≤ 𝔼 x, f x ^ 2 :=
  boolNoiseStab_le_expect_sq (by rw [abs_le]; constructor <;> norm_num) f
