/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# LTV homogeneous transition operator

For a fundamental matrix `X` of a linear time-varying
system, the transition operator `Φ(t, s) = X t * (X s)⁻¹`
satisfies `Φ(t, t) = 1`, the composition law
`Φ(t, s) * Φ(s, r) = Φ(t, r)`, and the homogeneous
equation in its first argument.
-/

@[expose] public section

open scoped Matrix

namespace ControlTheory

/-- The transition operator of a fundamental matrix `X`:
`transition X t s = X t * (X s)⁻¹`. -/
noncomputable def transition {n : Type*} [Fintype n] [DecidableEq n]
    (X : ℝ → Matrix n n ℝ) (t s : ℝ) : Matrix n n ℝ :=
  X t * (X s)⁻¹

/-- The transition operator at equal times is the
identity, for an invertible fundamental matrix. -/
theorem transition_self {n : Type*} [Fintype n] [DecidableEq n]
    (X : ℝ → Matrix n n ℝ) (t : ℝ) [Invertible (X t)] :
    transition X t t = 1 := by
  unfold transition
  exact Matrix.mul_inv_of_invertible (X t)

/-- The transition operator composes:
`Φ(t, s) * Φ(s, r) = Φ(t, r)`. -/
theorem transition_mul {n : Type*} [Fintype n] [DecidableEq n]
    (X : ℝ → Matrix n n ℝ) (t s r : ℝ) [Invertible (X s)] :
    transition X t s * transition X s r = transition X t r := by
  unfold transition
  have hinner : (X s)⁻¹ * (X s * (X r)⁻¹) = (X r)⁻¹ := by
    rw [← Matrix.mul_assoc, Matrix.inv_mul_of_invertible, Matrix.one_mul]
  calc (X t * (X s)⁻¹) * (X s * (X r)⁻¹)
      = X t * ((X s)⁻¹ * (X s * (X r)⁻¹)) := by rw [Matrix.mul_assoc]
    _ = X t * (X r)⁻¹ := by rw [hinner]

/-- The transition operator solves the homogeneous
equation in its first argument: if `X` has derivative
`A t * X t` at `t`, then so does `Φ(·, s)`, with
derivative `A t * Φ(t, s)`. -/
theorem transition_hasDerivAt {n : Type*} [Fintype n] [DecidableEq n]
    (X : ℝ → Matrix n n ℝ) (A : ℝ → Matrix n n ℝ) (t s : ℝ)
    (hX : HasDerivAt X (A t * X t) t) :
    HasDerivAt (fun u => transition X u s) (A t * transition X t s) t := by
  unfold transition
  rw [← Matrix.mul_assoc]
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have hXij : ∀ a b, HasDerivAt (fun u => X u a b) ((A t * X t) a b) t := by
    intro a b
    exact hasDerivAt_pi.mp (hasDerivAt_pi.mp hX a) b
  have hterm : ∀ k, HasDerivAt (fun u => X u i k * (X s)⁻¹ k j)
      ((A t * X t) i k * (X s)⁻¹ k j) t :=
    fun k => (hXij i k).mul_const _
  have hsum := HasDerivAt.sum (u := Finset.univ) (fun k _ => hterm k)
  have hfun : Finset.sum Finset.univ (fun k => fun u => X u i k * (X s)⁻¹ k j)
      = (fun x => (X x * (X s)⁻¹) i j) := by
    funext u
    simp [Finset.sum_apply, Matrix.mul_apply]
  have hderiv : Finset.sum Finset.univ (fun k => (A t * X t) i k * (X s)⁻¹ k j)
      = (((A t * X t) * (X s)⁻¹) i j) := by
    simp [Matrix.mul_apply]
  rw [hfun, hderiv] at hsum
  exact hsum

end ControlTheory
