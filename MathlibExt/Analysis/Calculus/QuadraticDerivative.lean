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
`(1/2) x(t)^T C x(t)` along a componentwise differentiable path is
`dx^T C x(t)`: the two product-rule halves agree by symmetry.

## ii. Key results

- `QuadraticDerivative.hasDerivAt_halfQuadForm`: the derivative.
- `QuadraticDerivative.halfQuadForm_deriv_eq`: `deriv` form.
- `QuadraticDerivative.halfQuadForm_eq_quadForm`: bridge to the
  existing `QuadraticFormCongruence.quadForm`.

## iii. Table of contents

- A. Quadratic derivative

## iv. References

- Standard matrix calculus for quadratic forms.

## A. Quadratic derivative
-/

@[expose] public section

namespace QuadraticDerivative

open Finset Matrix

/-- Half the quadratic form of a matrix `C` at `x`, in dot-product
form: `(x ⬝ᵥ (C *ᵥ x)) / 2`. -/
noncomputable def halfQuadForm {ι : Type*} [Fintype ι] (C : Matrix ι ι ℝ)
    (x : ι → ℝ) : ℝ :=
  (x ⬝ᵥ (C *ᵥ x)) / 2

/-- The half-quadratic form is the explicit double sum over entries. -/
theorem halfQuadForm_eq_sum {ι : Type*} [Fintype ι] (C : Matrix ι ι ℝ)
    (x : ι → ℝ) :
    halfQuadForm C x = (∑ i, ∑ j, x i * C i j * x j) / 2 := by
  unfold halfQuadForm dotProduct
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Derivative of the half-quadratic form along componentwise
differentiable `x t`, for a symmetric matrix `C`
(`Matrix.IsSymm C`): the derivative is `∑ i j, dx i * C i j * x j`. -/
theorem hasDerivAt_halfQuadForm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (hC : C.IsSymm)
    (x : ℝ → ι → ℝ) (dx : ι → ℝ) (t : ℝ)
    (hx : ∀ i : ι, HasDerivAt (fun s => x s i) (dx i) t) :
    HasDerivAt (fun s => halfQuadForm C (x s))
      (∑ i, ∑ j, dx i * C i j * x t j) t := by
  have hterm : ∀ i j : ι, HasDerivAt (fun s => x s i * C i j * x s j)
      (dx i * C i j * x t j + x t i * C i j * dx j) t := by
    intro i j
    exact ((hx i).mul_const (C i j)).mul (hx j)
  have hinner : ∀ i : ι, HasDerivAt (fun s => ∑ j, x s i * C i j * x s j)
      (∑ j, (dx i * C i j * x t j + x t i * C i j * dx j)) t := by
    intro i
    exact HasDerivAt.fun_sum (fun j _ => hterm i j)
  have houter : HasDerivAt (fun s => ∑ i, ∑ j, x s i * C i j * x s j)
      (∑ i, ∑ j, (dx i * C i j * x t j + x t i * C i j * dx j)) t :=
    HasDerivAt.fun_sum (fun i _ => hinner i)
  have hdiv : HasDerivAt (fun s => (∑ i, ∑ j, x s i * C i j * x s j) / 2)
      ((∑ i, ∑ j, (dx i * C i j * x t j + x t i * C i j * dx j)) / 2) t :=
    houter.div_const 2
  have hfun : (fun s => halfQuadForm C (x s))
      = (fun s => (∑ i, ∑ j, x s i * C i j * x s j) / 2) := by
    funext s
    exact halfQuadForm_eq_sum C (x s)
  have hsplit : (∑ i, ∑ j, (dx i * C i j * x t j + x t i * C i j * dx j))
      = (∑ i, ∑ j, dx i * C i j * x t j)
        + (∑ i, ∑ j, x t i * C i j * dx j) := by
    simp only [Finset.sum_add_distrib]
  have hsymm : (∑ i, ∑ j, x t i * C i j * dx j)
      = (∑ i, ∑ j, dx i * C i j * x t j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    have h : C b a = C a b := hC.apply a b
    rw [h]
    ring
  have hderiv : ((∑ i, ∑ j, (dx i * C i j * x t j + x t i * C i j * dx j)) / 2)
      = ∑ i, ∑ j, dx i * C i j * x t j := by
    rw [hsplit, hsymm]
    ring
  rw [hfun, ← hderiv]
  exact hdiv

/-- `deriv` form of the derivative formula. -/
theorem halfQuadForm_deriv_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (hC : C.IsSymm)
    (x : ℝ → ι → ℝ) (dx : ι → ℝ) (t : ℝ)
    (hx : ∀ i : ι, HasDerivAt (fun s => x s i) (dx i) t) :
    deriv (fun s => halfQuadForm C (x s)) t
      = ∑ i, ∑ j, dx i * C i j * x t j := by
  exact (hasDerivAt_halfQuadForm C hC x dx t hx).deriv

/-- Bridge: the half-quadratic form is half of the existing
`QuadraticFormCongruence.quadForm` (definitional). -/
lemma halfQuadForm_eq_quadForm {ι : Type*} [Fintype ι] (C : Matrix ι ι ℝ)
    (x : ι → ℝ) :
    halfQuadForm C x
      = MathlibExt.LinearAlgebra.Matrix.QuadraticFormCongruence.quadForm C x / 2 :=
  rfl

end QuadraticDerivative
