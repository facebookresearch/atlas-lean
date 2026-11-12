/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Calculus.HigherPartials
public import MathlibExt.Analysis.Calculus.HomogeneousEuler

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Tests for Euler's identity for positively homogeneous functions

Compiling checks for `MathlibExt.Analysis.Calculus.HomogeneousEuler`: Euler's identity on linear
functions and on the Euclidean norm of `ℝ²` away from the origin, the differentiated Euler identity
on the Euclidean norm, a Maxwell-style mixed-partial identity (computed directly, and through
`iterated_partialDeriv_commute` from `MathlibExt.Analysis.Calculus.HigherPartials`), and boundary
checks showing that the differentiability hypothesis is needed.
-/

@[expose] public section

open MetaMathlibExt

-- Domain remark: integrability and path-independence statements are only claimed on declared
-- domains. Nothing in this file or in `MathlibExt.Analysis.Calculus.HomogeneousEuler` asserts
-- path-independence.

private lemma linear_isHomogeneousDegreeOne {n : ℕ} (c : Fin n → ℝ) :
    IsHomogeneousDegreeOne fun x : Fin n → ℝ => ∑ i, c i * x i := by
  intro t _ x
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

-- Euler's identity, coordinate-free form, for the linear state function `x ↦ ∑ i, c i * x i`.
example {n : ℕ} (c x : Fin n → ℝ) :
    fderiv ℝ (fun y : Fin n → ℝ => ∑ i, c i * y i) x x = ∑ i, c i * x i :=
  (linear_isHomogeneousDegreeOne c).fderiv_apply_self (by fun_prop)

-- Euler's identity, coordinate form, for the linear state function `x ↦ ∑ i, c i * x i`.
example {n : ℕ} (c x : Fin n → ℝ) :
    ∑ i, x i * deriv (fun t : ℝ =>
      (fun y : Fin n → ℝ => ∑ k, c k * y k) (x + t • Pi.single i (1 : ℝ))) 0 =
      ∑ i, c i * x i :=
  (linear_isHomogeneousDegreeOne c).sum_mul_deriv_axis (by fun_prop)

-- Differentiated Euler identity for the linear state function, which is globally `C^2`.
example {n : ℕ} (c x : Fin n → ℝ) (j : Fin n) :
    ∑ i, x i * deriv (fun s : ℝ => deriv (fun t : ℝ =>
      (fun y : Fin n → ℝ => ∑ k, c k * y k)
        (x + s • Pi.single j (1 : ℝ) + t • Pi.single i (1 : ℝ))) 0) 0 = 0 :=
  (linear_isHomogeneousDegreeOne c).sum_mul_deriv_deriv_axis
    ((by fun_prop : ContDiff ℝ 2 fun y : Fin n → ℝ => ∑ k, c k * y k).contDiffAt) j

private lemma linearExample_isHomogeneousDegreeOne :
    IsHomogeneousDegreeOne fun x : Fin 2 → ℝ => x 0 + 2 * x 1 := by
  intro t _ x
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

-- Euler's identity, both forms, for `x ↦ x 0 + 2 * x 1` on `ℝ²`.
example (x : Fin 2 → ℝ) :
    fderiv ℝ (fun y : Fin 2 → ℝ => y 0 + 2 * y 1) x x = x 0 + 2 * x 1 :=
  linearExample_isHomogeneousDegreeOne.fderiv_apply_self (by fun_prop)

example (x : Fin 2 → ℝ) :
    ∑ i, x i * deriv (fun t : ℝ =>
      (fun y : Fin 2 → ℝ => y 0 + 2 * y 1) (x + t • Pi.single i (1 : ℝ))) 0 =
      x 0 + 2 * x 1 :=
  linearExample_isHomogeneousDegreeOne.sum_mul_deriv_axis (by fun_prop)

-- The axis slices of `x ↦ x 0 + 2 * x 1` vary one coordinate each: the partials are `1` and `2`.
example (x : Fin 2 → ℝ) :
    deriv (fun t : ℝ =>
      (fun y : Fin 2 → ℝ => y 0 + 2 * y 1) (x + t • Pi.single 0 (1 : ℝ))) 0 = 1 := by
  simp

example (x : Fin 2 → ℝ) :
    deriv (fun t : ℝ =>
      (fun y : Fin 2 → ℝ => y 0 + 2 * y 1) (x + t • Pi.single 1 (1 : ℝ))) 0 = 2 := by
  simp

/-! The Euclidean norm of `ℝ²`, a nonlinear homogeneous function, smooth away from the origin. -/

private lemma euclideanNorm_isHomogeneousDegreeOne :
    IsHomogeneousDegreeOne fun x : Fin 2 → ℝ => √(x 0 ^ 2 + x 1 ^ 2) := by
  intro t ht x
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show (t * x 0) ^ 2 + (t * x 1) ^ 2 = t ^ 2 * (x 0 ^ 2 + x 1 ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le]

private lemma sq_add_sq_ne_zero {x : Fin 2 → ℝ} (hx : x ≠ 0) : x 0 ^ 2 + x 1 ^ 2 ≠ 0 := by
  intro h
  have h0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  have h1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  exact hx (funext <| Fin.forall_fin_two.2 ⟨h0, h1⟩)

private lemma euclideanNorm_contDiffAt {x : Fin 2 → ℝ} (hx : x ≠ 0) :
    ContDiffAt ℝ 2 (fun y : Fin 2 → ℝ => √(y 0 ^ 2 + y 1 ^ 2)) x :=
  ContDiffAt.sqrt (by fun_prop) (sq_add_sq_ne_zero hx)

-- Euler's identity, coordinate-free form, for the Euclidean norm at a point `x ≠ 0`.
example (x : Fin 2 → ℝ) (hx : x ≠ 0) :
    fderiv ℝ (fun y : Fin 2 → ℝ => √(y 0 ^ 2 + y 1 ^ 2)) x x = √(x 0 ^ 2 + x 1 ^ 2) :=
  euclideanNorm_isHomogeneousDegreeOne.fderiv_apply_self
    ((euclideanNorm_contDiffAt hx).differentiableAt (by simp))

-- Euler's identity, coordinate form, for the Euclidean norm at a point `x ≠ 0`.
example (x : Fin 2 → ℝ) (hx : x ≠ 0) :
    ∑ i, x i * deriv (fun t : ℝ =>
      (fun y : Fin 2 → ℝ => √(y 0 ^ 2 + y 1 ^ 2)) (x + t • Pi.single i (1 : ℝ))) 0 =
      √(x 0 ^ 2 + x 1 ^ 2) :=
  euclideanNorm_isHomogeneousDegreeOne.sum_mul_deriv_axis
    ((euclideanNorm_contDiffAt hx).differentiableAt (by simp))

-- Differentiated Euler identity, coordinate form, for the Euclidean norm at a point `x ≠ 0`.
example (x : Fin 2 → ℝ) (hx : x ≠ 0) (j : Fin 2) :
    ∑ i, x i * deriv (fun s : ℝ => deriv (fun t : ℝ =>
      (fun y : Fin 2 → ℝ => √(y 0 ^ 2 + y 1 ^ 2))
        (x + s • Pi.single j (1 : ℝ) + t • Pi.single i (1 : ℝ))) 0) 0 = 0 :=
  euclideanNorm_isHomogeneousDegreeOne.sum_mul_deriv_deriv_axis (euclideanNorm_contDiffAt hx) j

-- Differentiated Euler identity, coordinate-free form, for the Euclidean norm at `x ≠ 0`.
example (x : Fin 2 → ℝ) (hx : x ≠ 0) :
    fderiv ℝ (fderiv ℝ fun y : Fin 2 → ℝ => √(y 0 ^ 2 + y 1 ^ 2)) x x = 0 :=
  euclideanNorm_isHomogeneousDegreeOne.fderiv_fderiv_apply_self (euclideanNorm_contDiffAt hx)

-- The coordinate-free differentiated identity read through `iteratedFDeriv`:
-- `iteratedFDeriv ℝ 2 f x ![x, v] = fderiv ℝ (fderiv ℝ f) x x v = 0`.
example {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : IsHomogeneousDegreeOne f) (x v : Fin n → ℝ)
    (hx : ContDiffAt ℝ 2 f x) :
    iteratedFDeriv ℝ 2 f x ![x, v] = 0 := by
  rw [iteratedFDeriv_two_apply]
  simp [hf.fderiv_fderiv_apply_self hx]

-- The global `ContDiff ℝ 2 f` form of the differentiated Euler identity is a special case.
example {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : IsHomogeneousDegreeOne f) (hC : ContDiff ℝ 2 f)
    (x : Fin n → ℝ) (j : Fin n) :
    ∑ i, x i * deriv (fun s : ℝ => deriv (fun t : ℝ =>
      f (x + s • Pi.single j (1 : ℝ) + t • Pi.single i (1 : ℝ))) 0) 0 = 0 :=
  hf.sum_mul_deriv_deriv_axis hC.contDiffAt j

/-! Maxwell-style mixed partials of `U x = x 0 ^ 2 * x 1 + x 1 ^ 3`, computed directly. The inner
slice (variable `t`) varies the first differentiation coordinate and the outer slice (variable
`s`) varies the second; each slice moves exactly one coordinate. -/

-- Direction `0` then `1`: `∂₁ (∂₀ U) x = 2 * x 0`.
private lemma maxwell_deriv_zero_then_one (x : Fin 2 → ℝ) :
    deriv (fun s : ℝ => deriv (fun t : ℝ =>
      (fun y : Fin 2 → ℝ => y 0 ^ 2 * y 1 + y 1 ^ 3)
        (x + s • Pi.single 1 (1 : ℝ) + t • Pi.single 0 (1 : ℝ))) 0) 0 = 2 * x 0 := by
  have hinner : (fun s : ℝ => deriv (fun t : ℝ =>
      (fun y : Fin 2 → ℝ => y 0 ^ 2 * y 1 + y 1 ^ 3)
        (x + s • Pi.single 1 (1 : ℝ) + t • Pi.single 0 (1 : ℝ))) 0) =
      fun s => 2 * x 0 * (x 1 + s) := by
    funext s
    have h := ((((hasDerivAt_id (0 : ℝ)).const_add (x 0)).fun_pow 2).mul_const
      (x 1 + s)).add_const ((x 1 + s) ^ 3)
    convert h.deriv using 1 <;> simp
  rw [hinner]
  have h := ((hasDerivAt_id (0 : ℝ)).const_add (x 1)).const_mul (2 * x 0)
  convert h.deriv using 1 <;> simp

-- Direction `1` then `0`: `∂₀ (∂₁ U) x = 2 * x 0`.
private lemma maxwell_deriv_one_then_zero (x : Fin 2 → ℝ) :
    deriv (fun s : ℝ => deriv (fun t : ℝ =>
      (fun y : Fin 2 → ℝ => y 0 ^ 2 * y 1 + y 1 ^ 3)
        (x + s • Pi.single 0 (1 : ℝ) + t • Pi.single 1 (1 : ℝ))) 0) 0 = 2 * x 0 := by
  have hinner : (fun s : ℝ => deriv (fun t : ℝ =>
      (fun y : Fin 2 → ℝ => y 0 ^ 2 * y 1 + y 1 ^ 3)
        (x + s • Pi.single 0 (1 : ℝ) + t • Pi.single 1 (1 : ℝ))) 0) =
      fun s => (x 0 + s) ^ 2 + 3 * x 1 ^ 2 := by
    funext s
    have h := (((hasDerivAt_id (0 : ℝ)).const_add (x 1)).const_mul ((x 0 + s) ^ 2)).fun_add
      (((hasDerivAt_id (0 : ℝ)).const_add (x 1)).fun_pow 3)
    convert h.deriv using 1 <;> simp
  rw [hinner]
  have h := (((hasDerivAt_id (0 : ℝ)).const_add (x 0)).fun_pow 2).add_const (3 * x 1 ^ 2)
  convert h.deriv using 1 <;> simp

-- Maxwell-style identity: the two mixed partials of `U` agree at every point.
example (x : Fin 2 → ℝ) :
    deriv (fun s : ℝ => deriv (fun t : ℝ =>
      (fun y : Fin 2 → ℝ => y 0 ^ 2 * y 1 + y 1 ^ 3)
        (x + s • Pi.single 1 (1 : ℝ) + t • Pi.single 0 (1 : ℝ))) 0) 0 =
      deriv (fun s : ℝ => deriv (fun t : ℝ =>
        (fun y : Fin 2 → ℝ => y 0 ^ 2 * y 1 + y 1 ^ 3)
          (x + s • Pi.single 0 (1 : ℝ) + t • Pi.single 1 (1 : ℝ))) 0) 0 := by
  rw [maxwell_deriv_zero_then_one, maxwell_deriv_one_then_zero]

-- The same identity through `iterated_partialDeriv_commute` from
-- `MathlibExt.Analysis.Calculus.HigherPartials`, stated for its `partialDeriv`: `U` is globally
-- `C^2`, so its two mixed partials agree at every point.
example (x : Fin 2 → ℝ) :
    partialDeriv (partialDeriv (fun y : Fin 2 → ℝ => y 0 ^ 2 * y 1 + y 1 ^ 3) 0) 1 x =
      partialDeriv (partialDeriv (fun y : Fin 2 → ℝ => y 0 ^ 2 * y 1 + y 1 ^ 3) 1) 0 x :=
  iterated_partialDeriv_commute _ 0 1 x
    (by fun_prop : ContDiff ℝ 2 fun y : Fin 2 → ℝ => y 0 ^ 2 * y 1 + y 1 ^ 3)

/-! Boundary checks: the differentiability hypothesis is load-bearing. -/

-- The Euclidean norm of `ℝ²` is homogeneous of degree one but not differentiable at `0`.
example : IsHomogeneousDegreeOne (fun x : Fin 2 → ℝ => √(x 0 ^ 2 + x 1 ^ 2)) ∧
    ¬ DifferentiableAt ℝ (fun x : Fin 2 → ℝ => √(x 0 ^ 2 + x 1 ^ 2)) 0 := by
  refine ⟨euclideanNorm_isHomogeneousDegreeOne, fun h => not_differentiableAt_abs_zero ?_⟩
  have hline : DifferentiableAt ℝ (fun t : ℝ => t • (Pi.single 0 1 : Fin 2 → ℝ)) 0 := by
    fun_prop
  have h₀ : DifferentiableAt ℝ (fun x : Fin 2 → ℝ => √(x 0 ^ 2 + x 1 ^ 2))
      ((0 : ℝ) • (Pi.single 0 1 : Fin 2 → ℝ)) := by
    rwa [zero_smul]
  have hcomp := h₀.comp (f := fun t : ℝ => t • (Pi.single 0 1 : Fin 2 → ℝ)) (0 : ℝ) hline
  convert hcomp using 1
  funext t
  simp [Real.sqrt_sq_eq_abs]

-- Without differentiability the conclusion of Euler's identity can fail: `x ↦ |x 0| + x 1` is
-- homogeneous of degree one, yet at `e₁ = Pi.single 1 1` it is not differentiable and
-- `fderiv ℝ g e₁ e₁ = 0 ≠ 1 = g e₁`.
example : IsHomogeneousDegreeOne (fun x : Fin 2 → ℝ => |x 0| + x 1) ∧
    fderiv ℝ (fun x : Fin 2 → ℝ => |x 0| + x 1) (Pi.single 1 1) (Pi.single 1 1) ≠
      (fun x : Fin 2 → ℝ => |x 0| + x 1) (Pi.single 1 1) := by
  refine ⟨fun t ht x => ?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos ht]
    ring
  have hnd : ¬ DifferentiableAt ℝ (fun x : Fin 2 → ℝ => |x 0| + x 1) (Pi.single 1 1) := by
    intro h
    apply not_differentiableAt_abs_zero
    have hline : DifferentiableAt ℝ
        (fun t : ℝ => (Pi.single 1 1 : Fin 2 → ℝ) + t • (Pi.single 0 1 : Fin 2 → ℝ)) 0 := by
      fun_prop
    have h₀ : DifferentiableAt ℝ (fun x : Fin 2 → ℝ => |x 0| + x 1)
        ((Pi.single 1 1 : Fin 2 → ℝ) + (0 : ℝ) • (Pi.single 0 1 : Fin 2 → ℝ)) := by
      rwa [zero_smul, add_zero]
    have hcomp := (h₀.comp (f := fun t : ℝ =>
      (Pi.single 1 1 : Fin 2 → ℝ) + t • (Pi.single 0 1 : Fin 2 → ℝ)) (0 : ℝ) hline).sub_const 1
    convert hcomp using 1
    funext t
    simp
  rw [fderiv_zero_of_not_differentiableAt hnd]
  simp

-- A homogeneous function of degree one that is differentiable at `0` is linear: `f = fderiv ℝ f 0`.
-- So the global hypothesis `ContDiff ℝ 2 f` only admits linear `f`, for which the differentiated
-- Euler identity reads `0 = 0`; nonlinear instances such as the Euclidean norm above need the
-- local hypothesis `ContDiffAt ℝ 2 f x` at a point `x ≠ 0`.
example {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : IsHomogeneousDegreeOne f)
    (h0 : DifferentiableAt ℝ f 0) (x : Fin n → ℝ) : f x = fderiv ℝ f 0 x := by
  have hf0 : f 0 = 0 := by
    have h := hf 2 two_pos 0
    rw [smul_zero] at h
    linarith
  have hline : HasDerivAt (fun t : ℝ => t • x) x 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const x
  have hg : HasDerivAt (fun t : ℝ => f (t • x)) (fderiv ℝ f 0 x) 0 :=
    (h0.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp) :)
  have hlin : HasDerivWithinAt (fun t : ℝ => f (t • x)) (f x) (Set.Ioi 0) 0 :=
    (hasDerivAt_mul_const (f x)).hasDerivWithinAt.congr (fun t ht => hf t ht x) (by simp [hf0])
  exact (uniqueDiffWithinAt_Ioi 0).eq_deriv _ hlin hg.hasDerivWithinAt
