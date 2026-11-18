/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.BooleanCubeInfluence
import Mathlib.Tactic.Ring

/-!
# Noise stability on the Boolean cube

For `f : BoolCube n → ℝ` and a real `ρ`, the noise stability of `f` at `ρ` is
`Stab_ρ[f] = 𝔼ₓ[f(x) · T_ρ f(x)]`: for `ρ ∈ [-1, 1]` it is the correlation `𝔼[f(x) f(y)]` of
`f` at a `ρ`-correlated pair `(x, y)`. Its Fourier formula
`Stab_ρ[f] = ∑_S ρ^|S| f̂(S)²` is O'Donnell's Theorem 2.49.

## Main definitions

* `BooleanCube.boolNoiseStab ρ f`: the noise stability `Stab_ρ[f] = 𝔼[f · T_ρ f]`.

## Main statements

* `BooleanCube.expect_mul_boolNoiseOp_eq_sum`: `𝔼[f · T_ρ g] = ∑_S ρ^|S| f̂(S) ĝ(S)`.
* `BooleanCube.expect_boolNoiseOp_mul_comm`: `T_ρ` is self-adjoint,
  `𝔼[T_ρ f · g] = 𝔼[f · T_ρ g]`.
* `BooleanCube.boolNoiseStab_eq_sum`: `Stab_ρ[f] = ∑_S ρ^|S| f̂(S)²` (Theorem 2.49).
* `BooleanCube.boolNoiseStab_sq_eq_expect_sq`: `Stab_{σ²}[f] = 𝔼[(T_σ f)²]`.
* `BooleanCube.boolNoiseStab_le_expect_sq`: `Stab_ρ[f] ≤ 𝔼[f²]` for `ρ ∈ [-1, 1]`.

## References

* R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014
  (arXiv:2105.10386), Section 2.4 (Definition 2.46, Fact 2.48, Theorem 2.49).
-/

@[expose] public section

namespace BooleanCube

open scoped BigOperators

variable {n : ℕ}

/-- **Noise stability on the Boolean cube.** For `f : BoolCube n → ℝ` and a real `ρ`,
`Stab_ρ[f] = 𝔼ₓ[f(x) · T_ρ f(x)]`, where `T_ρ` is the noise operator `boolNoiseOp`. For
`ρ ∈ [-1, 1]` this is `𝔼[f(x) f(y)]` for a `ρ`-correlated pair `(x, y)` (R. O'Donnell,
*Analysis of Boolean Functions*, 2014, Section 2.4, Fact 2.48). -/
noncomputable def boolNoiseStab (ρ : ℝ) (f : BoolCube n → ℝ) : ℝ :=
  𝔼 x, f x * boolNoiseOp ρ f x

/-- **Plancherel formula for the noise operator.** For all `f, g : BoolCube n → ℝ` and real
`ρ`, `𝔼[f · T_ρ g] = ∑_S ρ^|S| f̂(S) ĝ(S)` (R. O'Donnell, *Analysis of Boolean Functions*,
2014, Proposition 2.47 combined with Plancherel's Theorem, Section 1.4). -/
theorem expect_mul_boolNoiseOp_eq_sum (ρ : ℝ) (f g : BoolCube n → ℝ) :
    𝔼 x, f x * boolNoiseOp ρ g x =
      ∑ S, ρ ^ S.card * boolFourierCoeff n f S * boolFourierCoeff n g S := by
  rw [expect_mul_eq_sum_boolFourierCoeff_mul]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [boolFourierCoeff_boolNoiseOp]
  ring

/-- **The noise operator is self-adjoint.** For all `f, g : BoolCube n → ℝ` and real `ρ`,
`𝔼[T_ρ f · g] = 𝔼[f · T_ρ g]` (R. O'Donnell, *Analysis of Boolean Functions*, 2014,
Section 2.4; this is the self-adjointness of `T_ρ` used throughout Chapter 2). -/
theorem expect_boolNoiseOp_mul_comm (ρ : ℝ) (f g : BoolCube n → ℝ) :
    𝔼 x, boolNoiseOp ρ f x * g x = 𝔼 x, f x * boolNoiseOp ρ g x := by
  have h : 𝔼 x, boolNoiseOp ρ f x * g x = 𝔼 x, g x * boolNoiseOp ρ f x :=
    Finset.expect_congr rfl fun x _ => mul_comm _ _
  rw [h, expect_mul_boolNoiseOp_eq_sum, expect_mul_boolNoiseOp_eq_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  ring

/-- **Fourier formula for noise stability.** For every `f : BoolCube n → ℝ` and real `ρ`,
`Stab_ρ[f] = ∑_S ρ^|S| f̂(S)²` (R. O'Donnell, *Analysis of Boolean Functions*, 2014,
Theorem 2.49). -/
theorem boolNoiseStab_eq_sum (ρ : ℝ) (f : BoolCube n → ℝ) :
    boolNoiseStab ρ f = ∑ S, ρ ^ S.card * boolFourierCoeff n f S ^ 2 := by
  rw [boolNoiseStab, expect_mul_boolNoiseOp_eq_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  ring

/-- **Noise stability at `ρ = 1`.** `Stab_1[f] = 𝔼[f²]`. -/
@[simp] theorem boolNoiseStab_one (f : BoolCube n → ℝ) :
    boolNoiseStab 1 f = 𝔼 x, f x ^ 2 := by
  simp [boolNoiseStab, sq]

/-- **Noise stability at `ρ = 0`.** `Stab_0[f] = (𝔼 f)²`. -/
@[simp] theorem boolNoiseStab_zero (f : BoolCube n → ℝ) :
    boolNoiseStab 0 f = (𝔼 x, f x) ^ 2 := by
  simp [boolNoiseStab, ← Finset.expect_mul, sq]

/-- **Noise stability as a squared norm.** For every `f : BoolCube n → ℝ` and real `σ`,
`Stab_{σ²}[f] = 𝔼[(T_σ f)²]`; in particular `Stab_ρ[f] ≥ 0` for `ρ ≥ 0` (R. O'Donnell,
*Analysis of Boolean Functions*, 2014, Section 2.4 and the introduction of Chapter 9, where
`Stab_ρ[f] = ‖T_{√ρ} f‖₂²` is the starting point of the (p,2)-Hypercontractivity Theorem). -/
theorem boolNoiseStab_sq_eq_expect_sq (σ : ℝ) (f : BoolCube n → ℝ) :
    boolNoiseStab (σ ^ 2) f = 𝔼 x, boolNoiseOp σ f x ^ 2 := by
  rw [boolNoiseStab_eq_sum, expect_sq_eq_sum_boolFourierCoeff_sq]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [boolFourierCoeff_boolNoiseOp]
  ring

/-- **Noise stability is at most the second moment.** For `ρ ∈ [-1, 1]` and every
`f : BoolCube n → ℝ`, `Stab_ρ[f] ≤ 𝔼[f²]`; for `±1`-valued `f` this says `Stab_ρ[f] ≤ 1`
(R. O'Donnell, *Analysis of Boolean Functions*, 2014, Theorem 2.49 with Parseval's Theorem). -/
theorem boolNoiseStab_le_expect_sq {ρ : ℝ} (hρ : |ρ| ≤ 1) (f : BoolCube n → ℝ) :
    boolNoiseStab ρ f ≤ 𝔼 x, f x ^ 2 := by
  rw [boolNoiseStab_eq_sum, expect_sq_eq_sum_boolFourierCoeff_sq]
  refine Finset.sum_le_sum fun S _ => ?_
  have h : ρ ^ S.card ≤ 1 := by
    calc ρ ^ S.card ≤ |ρ ^ S.card| := le_abs_self _
      _ = |ρ| ^ S.card := abs_pow ρ S.card
      _ ≤ 1 := pow_le_one₀ (abs_nonneg ρ) hρ
  exact mul_le_of_le_one_left (sq_nonneg _) h

end BooleanCube
