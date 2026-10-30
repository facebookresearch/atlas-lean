/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.BooleanCubeInfluence
import Mathlib.Algebra.Ring.CharZero
import Mathlib.Tactic.NormNum

open BooleanCube
open scoped BigOperators

/-! ### Coordinate flips -/

/-- A concrete flip of the first of two coordinates. -/
example : flipCoord (n := 2) ![true, false] 0 = ![false, false] := by
  decide

/-- Flips are involutions, by `simp`. -/
example (x : BoolCube 3) (i : Fin 3) : flipCoord (flipCoord x i) i = x := by
  simp

/-- A flip moves every point. -/
example (x : BoolCube 3) : flipCoord x 0 ≠ x :=
  flipCoord_ne_self x 0

/-- Flipping a coordinate inside `S` negates `χ_S`. -/
example (x : BoolCube 2) : cubeChi 2 {0, 1} (flipCoord x 1) = -cubeChi 2 {0, 1} x := by
  simp [cubeChi_flipCoord]

/-! ### Fourier expansion -/

/-- The mean is the empty coefficient. -/
example (f : BoolCube 3 → ℝ) : 𝔼 x, f x = boolFourierCoeff 3 f ∅ :=
  expect_eq_boolFourierCoeff_empty f

/-- Distinct characters are orthogonal. -/
example : ∑ x : BoolCube 2, cubeChi 2 {0} x * cubeChi 2 {1} x = 0 := by
  rw [sum_cubeChi_mul_cubeChi_eq_ite]
  simp

/-- Parseval for a character: `𝔼[χ_S²] = 1`. -/
example (S : Finset (Fin 3)) : 𝔼 x, cubeChi 3 S x ^ 2 = 1 := by
  rw [expect_sq_eq_sum_boolFourierCoeff_sq]
  simp [boolFourierCoeff_cubeChi]

/-- Functions with the same coefficients are equal. -/
example (f g : BoolCube 2 → ℝ) (h : ∀ S, boolFourierCoeff 2 f S = boolFourierCoeff 2 g S) :
    f = g :=
  boolFourierCoeff_injective (funext h)

/-! ### Influences and variance of characters -/

/-- The influence of `i` on `χ_S` is `1` if `i ∈ S` and `0` otherwise. -/
example (n : ℕ) (S : Finset (Fin n)) (i : Fin n) :
    boolInfluence (cubeChi n S) i = if i ∈ S then 1 else 0 := by
  rw [boolInfluence_eq_sum_sq]
  simp [boolFourierCoeff_cubeChi]

/-- The total influence of `χ_S` is `|S|`. -/
example (n : ℕ) (S : Finset (Fin n)) : boolTotalInfluence (cubeChi n S) = S.card := by
  rw [boolTotalInfluence_eq_sum_card_mul_sq]
  simp [boolFourierCoeff_cubeChi]

/-- The variance of `χ_S` is `1` unless `S = ∅`. -/
example (n : ℕ) (S : Finset (Fin n)) (hS : S.Nonempty) : boolVariance (cubeChi n S) = 1 := by
  rw [boolVariance_eq_sum_sq]
  simp [boolFourierCoeff_cubeChi, hS]

/-- Coordinate `0` has influence `1` on the dictator `x ↦ x₀` on two bits. -/
example : boolInfluence (fun x : BoolCube 2 => cubeVal (x 0)) 0 = 1 := by
  rw [boolInfluence_eq_expect_ite_ne fun x => by cases x 0 <;> simp]
  simp [CharZero.neg_eq_self_iff]

/-- Coordinate `1` has influence `0` on the same dictator. -/
example : boolInfluence (fun x : BoolCube 2 => cubeVal (x 0)) 1 = 0 := by
  rw [boolInfluence_eq_expect_ite_ne fun x => by cases x 0 <;> simp]
  simp

/-- Constants have no influence and no variance, by `simp`. -/
example (c : ℝ) : boolInfluence (fun _ : BoolCube 3 => c) 1 = 0 ∧
    boolTotalInfluence (fun _ : BoolCube 3 => c) = 0 ∧
    boolVariance (fun _ : BoolCube 3 => c) = 0 := by
  simp

/-- On the zero-dimensional cube every function has variance zero. -/
example (f : BoolCube 0 → ℝ) : boolVariance f = 0 :=
  le_antisymm ((boolVariance_le_boolTotalInfluence f).trans (by simp [boolTotalInfluence]))
    (boolVariance_nonneg f)

/-- The Poincaré inequality. -/
example (f : BoolCube 4 → ℝ) : boolVariance f ≤ boolTotalInfluence f :=
  boolVariance_le_boolTotalInfluence f

/-- The variance is `𝔼[f²] - (𝔼 f)²`. -/
example (f : BoolCube 4 → ℝ) : boolVariance f = 𝔼 x, f x ^ 2 - (𝔼 x, f x) ^ 2 :=
  boolVariance_eq_expect_sq_sub_sq f

/-! ### The noise operator -/

/-- `T_1 = id` and `T_0 f = 𝔼 f`, by `simp`. -/
example (f : BoolCube 3 → ℝ) (x : BoolCube 3) :
    boolNoiseOp 1 f x = f x ∧ boolNoiseOp 0 f x = 𝔼 y, f y := by
  simp

/-- Characters are eigenfunctions with eigenvalue `ρ ^ |S|`. -/
example (ρ : ℝ) (x : BoolCube 3) :
    boolNoiseOp ρ (cubeChi 3 {0, 2}) x = ρ ^ 2 * cubeChi 3 {0, 2} x := by
  rw [boolNoiseOp_cubeChi]
  simp

/-- `T_ρ T_σ = T_{ρσ}`. -/
example (f : BoolCube 3 → ℝ) :
    boolNoiseOp (1 / 2) (boolNoiseOp (1 / 3) f) = boolNoiseOp (1 / 6) f := by
  rw [boolNoiseOp_boolNoiseOp]
  congr 1
  norm_num

/-- `T_ρ` preserves the mean and, for `|ρ| ≤ 1`, nonnegativity. -/
example (ρ : ℝ) (hρ : |ρ| ≤ 1) (f : BoolCube 3 → ℝ) (hf : ∀ x, 0 ≤ f x) (x : BoolCube 3) :
    𝔼 y, boolNoiseOp ρ f y = 𝔼 y, f y ∧ 0 ≤ boolNoiseOp ρ f x :=
  ⟨expect_boolNoiseOp ρ f, boolNoiseOp_nonneg hρ hf x⟩

/-- For `|ρ| > 1` the operator is not positive: on one bit, `T_{-3}` sends the indicator of
`x₀ = true` to a function that is negative at the all-`true` point. -/
example : boolNoiseOp (-3) (fun x : BoolCube 1 => if x 0 then 1 else 0) (fun _ => true) < 0 := by
  rw [boolNoiseOp, ← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp]
  norm_num [Fintype.sum_bool]
