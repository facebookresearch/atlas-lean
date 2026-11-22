/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Const

/-!
# The complex Hessian of a real function on `ℂⁿ`

For `u : ℂⁿ → ℝ` (with `ℂⁿ = EuclideanSpace ℂ (Fin n)` viewed as a real normed space), the complex
Hessian is the matrix `u_{j k̄} = ∂²u/∂z_j∂z̄_k`. In real coordinates `z_j = x_j + i y_j` it is
`(u_{x_j x_k} + u_{y_j y_k} + i (u_{x_j y_k} - u_{y_j x_k})) / 4`, computed here from the real
second Fréchet derivative.
-/

@[expose] public section

namespace MetaMathlibExt

/-- The real second derivative `D²u(z)(a, b)` of `u : ℂⁿ → ℝ`. -/
noncomputable def realHessian {n : ℕ} (u : EuclideanSpace ℂ (Fin n) → ℝ)
    (z a b : EuclideanSpace ℂ (Fin n)) : ℝ :=
  fderiv ℝ (fderiv ℝ u) z a b

/-- The complex Hessian `u_{j k̄} = ∂²u/∂z_j∂z̄_k
= (u_{x_j x_k} + u_{y_j y_k} + i (u_{x_j y_k} - u_{y_j x_k})) / 4` of `u : ℂⁿ → ℝ` at `z`. -/
noncomputable def complexHessian {n : ℕ} (u : EuclideanSpace ℂ (Fin n) → ℝ)
    (z : EuclideanSpace ℂ (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  fun j k =>
    let ej : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j 1
    let ek : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single k 1
    ((realHessian u z ej ek + realHessian u z (Complex.I • ej) (Complex.I • ek) : ℝ) +
      ((realHessian u z ej (Complex.I • ek) - realHessian u z (Complex.I • ej) ek : ℝ) : ℂ) *
        Complex.I) / 4

theorem complexHessian_apply {n : ℕ} (u : EuclideanSpace ℂ (Fin n) → ℝ)
    (z : EuclideanSpace ℂ (Fin n)) (j k : Fin n) :
    complexHessian u z j k =
      ((realHessian u z (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) +
          realHessian u z (Complex.I • EuclideanSpace.single j 1)
            (Complex.I • EuclideanSpace.single k 1) : ℝ) +
        ((realHessian u z (EuclideanSpace.single j 1) (Complex.I • EuclideanSpace.single k 1) -
            realHessian u z (Complex.I • EuclideanSpace.single j 1)
              (EuclideanSpace.single k 1) : ℝ) : ℂ) * Complex.I) / 4 :=
  rfl

/-- A constant function has zero real second derivative. -/
@[simp] theorem realHessian_const {n : ℕ} (c : ℝ) (z a b : EuclideanSpace ℂ (Fin n)) :
    realHessian (fun _ => c) z a b = 0 := by
  simp [realHessian]

/-- A constant function has zero complex Hessian. -/
@[simp] theorem complexHessian_const {n : ℕ} (c : ℝ) (z : EuclideanSpace ℂ (Fin n)) :
    complexHessian (fun _ => c) z = 0 := by
  ext j k
  simp [complexHessian_apply]

end MetaMathlibExt
