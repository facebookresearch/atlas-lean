/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Derivative of a symmetric quadratic form

## i. Overview

For a constant symmetric matrix `C`, the derivative of
`(1/2) x(t)^T C x(t)` along a componentwise differentiable path is
`dx^T C x(t)`: the two product-rule halves agree by symmetry.

## ii. Key results

- `QuadraticDerivative.hasDerivAt_quadForm`: the derivative.
- `QuadraticDerivative.quadForm_deriv_eq`: `deriv` form.

## iii. Table of contents

- A. Quadratic derivative

## iv. References

- Standard matrix calculus for quadratic forms.

## A. Quadratic derivative
-/

@[expose] public section

namespace QuadraticDerivative

open Finset

/-- Half the quadratic form of a matrix `C` at `x`. -/
noncomputable def quadForm {n : ℕ} (C : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  (∑ i, ∑ j, x i * C i j * x j) / 2

/-- Derivative of the half-quadratic form along componentwise
differentiable `x t`, for symmetric `C`: the derivative is
`∑ i j, dx i * C i j * x j` (one copy of the two symmetric halves). -/
theorem hasDerivAt_quadForm {n : ℕ} (C : Fin n → Fin n → ℝ)
    (hC : ∀ i j : Fin n, C i j = C j i)
    (x : ℝ → Fin n → ℝ) (dx : Fin n → ℝ) (t : ℝ)
    (hx : ∀ i : Fin n, HasDerivAt (fun s => x s i) (dx i) t) :
    HasDerivAt (fun s => quadForm C (x s))
      (∑ i, ∑ j, dx i * C i j * x t j) t := by
  have hterm : ∀ i j : Fin n, HasDerivAt (fun s => x s i * C i j * x s j)
      (dx i * C i j * x t j + x t i * C i j * dx j) t := by
    intro i j
    exact ((hx i).mul_const (C i j)).mul (hx j)
  have hsum : HasDerivAt (fun s => ∑ i, ∑ j, x s i * C i j * x s j)
      (∑ i, ∑ j, (dx i * C i j * x t j + x t i * C i j * dx j)) t := by
    apply HasDerivAt.fun_sum
    intro i _
    apply HasDerivAt.fun_sum
    intro j _
    exact hterm i j
  have hval : (∑ i, ∑ j, (dx i * C i j * x t j + x t i * C i j * dx j)) / 2
      = ∑ i, ∑ j, dx i * C i j * x t j := by
    have hsplit : (∑ i, ∑ j, (dx i * C i j * x t j + x t i * C i j * dx j))
        = (∑ i, ∑ j, dx i * C i j * x t j) + (∑ i, ∑ j, x t i * C i j * dx j) := by
      simp only [Finset.sum_add_distrib]
    have hsym : (∑ i, ∑ j, x t i * C i j * dx j)
        = (∑ i, ∑ j, dx i * C i j * x t j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      show x t b * C b a * dx a = dx a * C a b * x t b
      rw [hC b a]
      ring
    rw [hsplit, hsym]
    ring
  have hdiv := hsum.div_const 2
  rw [hval] at hdiv
  simpa only [quadForm] using hdiv

/-- The derivative formula at a concrete symmetric witness is the
plain quadratic derivative (non-vacuity anchor, same statement). -/
theorem quadForm_deriv_eq {n : ℕ} (C : Fin n → Fin n → ℝ)
    (hC : ∀ i j : Fin n, C i j = C j i)
    (x : ℝ → Fin n → ℝ) (dx : Fin n → ℝ) (t : ℝ)
    (hx : ∀ i : Fin n, HasDerivAt (fun s => x s i) (dx i) t) :
    deriv (fun s => quadForm C (x s)) t
      = ∑ i, ∑ j, dx i * C i j * x t j := by
  exact (hasDerivAt_quadForm C hC x dx t hx).deriv

end QuadraticDerivative
