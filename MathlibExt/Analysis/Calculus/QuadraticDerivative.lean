/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import MathlibExt.LinearAlgebra.Matrix.QuadraticFormCongruence
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Derivative of a symmetric quadratic form

## i. Overview

For a constant symmetric matrix `C`, the derivative of
`quadForm C (x t) / 2` along a componentwise differentiable path is
`dx^T C x(t)`: the two product-rule halves agree by symmetry. Here
`quadForm` is the existing
`MathlibExt.LinearAlgebra.Matrix.QuadraticFormCongruence.quadForm`.

## ii. Key results

- `QuadraticDerivative.quadForm_half_eq_sum`: the double-sum form.
- `QuadraticDerivative.hasDerivAt_quadForm_half`: the derivative.
- `QuadraticDerivative.quadForm_half_deriv_eq`: `deriv` form.

## iii. Table of contents

- A. Quadratic derivative

## iv. References

- Standard matrix calculus for quadratic forms.

## A. Quadratic derivative
-/

@[expose] public section

namespace QuadraticDerivative


open Finset Matrix

/-- The half-quadratic value `MathlibExt.LinearAlgebra.Matrix.QuadraticFormCongruence.quadForm C x / 2` is the explicit
double sum over entries, halved. (At integration this expression is
`QuadraticFormCongruence.quadForm C x / 2`.) -/
theorem quadForm_half_eq_sum {ι : Type*} [Fintype ι] (C : Matrix ι ι ℝ)
    (x : ι → ℝ) :
    MathlibExt.LinearAlgebra.Matrix.QuadraticFormCongruence.quadForm C x / 2 = (∑ i, ∑ j, x i * C i j * x j) / 2 := by
  have h := Matrix.dot_mulVec_eq_sum_sum x C x
  rw [Finset.sum_comm] at h
  exact congrArg (· / 2) h

/-- Derivative of the half-quadratic form along componentwise
differentiable `x t`, for a symmetric matrix `C`
(`Matrix.IsSymm C`): the derivative is `∑ i j, dx i * C i j * x j`. -/
theorem hasDerivAt_quadForm_half {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (hC : C.IsSymm)
    (x : ℝ → ι → ℝ) (dx : ι → ℝ) (t : ℝ)
    (hx : ∀ i : ι, HasDerivAt (fun s => x s i) (dx i) t) :
    HasDerivAt (fun s => MathlibExt.LinearAlgebra.Matrix.QuadraticFormCongruence.quadForm C (x s) / 2)
      (∑ i, ∑ j, dx i * C i j * x t j) t := by
  have hterm : ∀ i j : ι, HasDerivAt (fun s => x s i * C i j * x s j)
      (dx i * C i j * x t j + x t i * C i j * dx j) t := by
    intro i j
    exact HasDerivAt.mul ((hx i).mul_const (C i j)) (hx j)
  have hsum : HasDerivAt (fun s => ∑ i, ∑ j, x s i * C i j * x s j)
      (∑ i, ∑ j, (dx i * C i j * x t j + x t i * C i j * dx j)) t :=
    HasDerivAt.fun_sum (fun i _ => HasDerivAt.fun_sum (fun j _ => hterm i j))
  have hdiv := hsum.div_const (2 : ℝ)
  have hcongr : HasDerivAt (fun s => MathlibExt.LinearAlgebra.Matrix.QuadraticFormCongruence.quadForm C (x s) / 2)
      ((∑ i, ∑ j, (dx i * C i j * x t j + x t i * C i j * dx j)) / 2) t :=
    hdiv.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun s => quadForm_half_eq_sum C (x s)))
  have hswap : (∑ i, ∑ j, x t i * C i j * dx j)
      = ∑ i, ∑ j, dx i * C i j * x t j := by
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hCji : C j i = C i j := by rw [← Matrix.transpose_apply C i j, hC.eq]
    rw [hCji]
    ring
  have hval : (∑ i, ∑ j, (dx i * C i j * x t j + x t i * C i j * dx j)) / 2
      = ∑ i, ∑ j, dx i * C i j * x t j := by
    have hsplit : (∑ i, ∑ j, (dx i * C i j * x t j + x t i * C i j * dx j))
        = (∑ i, ∑ j, dx i * C i j * x t j) + (∑ i, ∑ j, x t i * C i j * dx j) := by
      simp only [Finset.sum_add_distrib]
    rw [hsplit, hswap]
    ring
  rw [hval] at hcongr
  exact hcongr

/-- `deriv` form of the derivative formula. -/
theorem quadForm_half_deriv_eq {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (hC : C.IsSymm)
    (x : ℝ → ι → ℝ) (dx : ι → ℝ) (t : ℝ)
    (hx : ∀ i : ι, HasDerivAt (fun s => x s i) (dx i) t) :
    deriv (fun s => MathlibExt.LinearAlgebra.Matrix.QuadraticFormCongruence.quadForm C (x s) / 2) t
      = ∑ i, ∑ j, dx i * C i j * x t j := by
  exact (hasDerivAt_quadForm_half C hC x dx t hx).deriv

end QuadraticDerivative
