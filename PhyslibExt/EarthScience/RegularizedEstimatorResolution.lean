/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Regularized estimator: resolution and bias operators

For a forward operator `A`, noiseless data `d = A *ᵥ s`, and a
regularization parameter `reg`, the damped least-squares estimator is
`ŝ = B⁻¹ *ᵥ (Aᵀ *ᵥ d)` with normal matrix `B = Aᵀ * A + reg • 1`. It is
the resolution operator `R = B⁻¹ * (Aᵀ * A)` applied to the true model,
and its bias is the bias operator `R - 1` applied to the true model.

## i. Overview

The estimator smooths the true model: `ŝ = R *ᵥ s` and
`ŝ - s = (R - 1) *ᵥ s`. Without regularization (`reg = 0` and
`Aᵀ * A` invertible) `R = 1` and the bias vanishes. A regularized
solution is therefore not necessarily the true Earth model: the bias
operator is nonzero in general.

## ii. Key results

- `EarthScience.regularized_estimator_eq_resolution`: `ŝ = R *ᵥ s`.
- `EarthScience.regularized_estimator_bias`: `ŝ - s = (R - 1) *ᵥ s`.

## iii. Table of contents

- A. Resolution and bias

## iv. References

- `Matrix.mulVec_mulVec`, `Matrix.sub_mulVec`, `Matrix.one_mulVec`
  in Mathlib.

## A. Resolution and bias
-/

@[expose] public section

open scoped Matrix

namespace EarthScience

/-- A regularized (damped least-squares) estimator has the derived
resolution operator: with normal matrix `B = Aᵀ * A + reg • 1` invertible,
the estimator from noiseless data `d = A *ᵥ s` equals `R *ᵥ s` where
`R = B⁻¹ * (Aᵀ * A)` is the resolution operator. -/
theorem regularized_estimator_eq_resolution {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (A : Matrix m n ℝ) (s : n → ℝ) {reg : ℝ}
    (hB : IsUnit (Aᵀ * A + reg • (1 : Matrix n n ℝ)).det) :
    (Aᵀ * A + reg • (1 : Matrix n n ℝ))⁻¹ *ᵥ
        (Aᵀ *ᵥ (A *ᵥ s)) =
      ((Aᵀ * A + reg • (1 : Matrix n n ℝ))⁻¹ * (Aᵀ * A)) *ᵥ s := by
  have _ := hB
  have h : Aᵀ *ᵥ (A *ᵥ s) = (Aᵀ * A) *ᵥ s := Matrix.mulVec_mulVec _ _ _
  rw [h]
  exact Matrix.mulVec_mulVec _ _ _

/-- The bias of the regularized estimator is the bias operator applied to
the true model: `ŝ - s = (R - 1) *ᵥ s` where `R` is the resolution
operator above. Without regularization (`reg = 0`, `Aᵀ * A` invertible)
`R = 1` and the bias vanishes. -/
theorem regularized_estimator_bias {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (A : Matrix m n ℝ) (s : n → ℝ) {reg : ℝ}
    (hB : IsUnit (Aᵀ * A + reg • (1 : Matrix n n ℝ)).det) :
    (Aᵀ * A + reg • (1 : Matrix n n ℝ))⁻¹ *ᵥ (Aᵀ *ᵥ (A *ᵥ s)) - s =
      ((Aᵀ * A + reg • (1 : Matrix n n ℝ))⁻¹ * (Aᵀ * A) - 1) *ᵥ s := by
  have h1 := regularized_estimator_eq_resolution A s hB
  rw [h1, Matrix.sub_mulVec, Matrix.one_mulVec]

end EarthScience
