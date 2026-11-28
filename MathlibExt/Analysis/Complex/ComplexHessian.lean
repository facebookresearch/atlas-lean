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

/-- **Real Hessian.** For a function $u : \mathbb{C}^n \to \mathbb{R}$, with $\mathbb{C}^n$
viewed as a real normed space, write $Du(w)$ for the real Fréchet derivative of $u$ at $w$. For
points $z, a, b \in \mathbb{C}^n$, the real Hessian $D^2u(z)(a, b)$ is the real number obtained
by taking the real Fréchet derivative at $z$ of the map $w \mapsto Du(w)$, applying it to $a$,
and applying the result to $b$.

As usual in Mathlib, a derivative that does not exist is taken to be zero. -/
noncomputable def realHessian {n : ℕ} (u : EuclideanSpace ℂ (Fin n) → ℝ)
    (z a b : EuclideanSpace ℂ (Fin n)) : ℝ :=
  fderiv ℝ (fderiv ℝ u) z a b

/-- **Complex Hessian.** Let $u : \mathbb{C}^n \to \mathbb{R}$ and $z \in \mathbb{C}^n$, write
$e_1, \dots, e_n$ for the standard basis of $\mathbb{C}^n$, write $i$ for the imaginary unit, and
for $a, b \in \mathbb{C}^n$ write $D^2u(z)(a, b)$ for the real Hessian of $u$ at $z$. The complex
Hessian of $u$ at $z$ is the $n \times n$ complex matrix whose $(j, k)$ entry is

$$
u_{j\bar k}(z) = \frac{D^2u(z)(e_j, e_k) + D^2u(z)(i e_j, i e_k) +
i \left(D^2u(z)(e_j, i e_k) - D^2u(z)(i e_j, e_k)\right)}{4}.
$$

When $u$ is of class $C^2$, in real coordinates $z_j = x_j + i y_j$ this is
$\partial^2 u / \partial z_j \partial \bar z_k =
(u_{x_j x_k} + u_{y_j y_k} + i (u_{x_j y_k} - u_{y_j x_k})) / 4$. -/
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

/-- **Constant functions have zero real Hessian.** For every real constant $c$, the function
$u : \mathbb{C}^n \to \mathbb{R}$ with constant value $c$ has real Hessian $D^2u(z)(a, b) = 0$ for
all $z, a, b \in \mathbb{C}^n$. -/
@[simp] theorem realHessian_const {n : ℕ} (c : ℝ) (z a b : EuclideanSpace ℂ (Fin n)) :
    realHessian (fun _ => c) z a b = 0 := by
  simp [realHessian]

/-- **Constant functions have zero complex Hessian.** For every real constant $c$, the function
$u : \mathbb{C}^n \to \mathbb{R}$ with constant value $c$ has complex Hessian equal to the zero
$n \times n$ matrix at every point $z \in \mathbb{C}^n$. -/
@[simp] theorem complexHessian_const {n : ℕ} (c : ℝ) (z : EuclideanSpace ℂ (Fin n)) :
    complexHessian (fun _ => c) z = 0 := by
  ext j k
  simp [complexHessian_apply]

end MetaMathlibExt
