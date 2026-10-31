/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Jacobian matrices

This file relates coordinate Jacobian matrices to Fréchet derivatives and proves their chain rule.
-/

@[expose] public section

namespace MetaMathlibExt

open scoped Matrix

/-- **Jacobian matrix.** For $f : \mathbb{R}^m \to \mathbb{R}^n$ and $x \in \mathbb{R}^m$, the
Jacobian matrix of $f$ at $x$ is the $n \times m$ real matrix whose $(i, j)$ entry is the partial
derivative of the $i$-th component $f_i$ of $f$ in the $j$-th coordinate direction at $x$: the
derivative at $t = 0$ of $t \mapsto f_i(x + t e_j)$, where $e_j$ is the $j$-th standard basis
vector of $\mathbb{R}^m$. A partial derivative that does not exist is taken to be $0$.

Sources: `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` /
`Differential calculus`, entry `Jacobian matrix` (unmapped);
W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 9;
stable ref https://en.wikipedia.org/wiki/Jacobian_matrix_and_determinant. -/
noncomputable def jacobianMatrix {m n : ℕ} (f : (Fin m → ℝ) → (Fin n → ℝ))
    (x : Fin m → ℝ) : Matrix (Fin n) (Fin m) ℝ :=
  fun i j => deriv (fun t : ℝ => f (x + t • Pi.single j (1 : ℝ)) i) 0

/-- **Entries of the Jacobian matrix are partial derivatives.** Let
$f : \mathbb{R}^m \to \mathbb{R}^n$ and $x \in \mathbb{R}^m$. For every row index $i$ and column
index $j$, the $(i, j)$ entry of the Jacobian matrix of $f$ at $x$ is the derivative at $t = 0$
of $t \mapsto f_i(x + t e_j)$, where $f_i$ is the $i$-th component of $f$ and $e_j$ is the
$j$-th standard basis vector of $\mathbb{R}^m$. This derivative is taken to be $0$ when it does
not exist.

Sources: `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` /
`Differential calculus`, entry `Jacobian matrix` (unmapped);
W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 9. -/
theorem jacobianMatrix_apply {m n : ℕ} (f : (Fin m → ℝ) → (Fin n → ℝ))
    (x : Fin m → ℝ) (i : Fin n) (j : Fin m) :
    jacobianMatrix f x i j =
      deriv (fun t : ℝ => f (x + t • Pi.single j (1 : ℝ)) i) 0 := rfl

private theorem jacobian_hasDerivAt_along_single {m n : ℕ}
    (f : (Fin m → ℝ) → (Fin n → ℝ)) (x : Fin m → ℝ)
    (hf : DifferentiableAt ℝ f x) (j : Fin m) :
    HasDerivAt (fun t : ℝ => f (x + t • Pi.single j (1 : ℝ)))
      (fderiv ℝ f x (Pi.single j (1 : ℝ))) 0 := by
  have hline : HasDerivAt (fun t : ℝ => x + t • Pi.single j (1 : ℝ))
      (Pi.single j (1 : ℝ)) 0 := by
    simpa using
      ((hasDerivAt_id' (0 : ℝ)).smul_const (Pi.single j (1 : ℝ))).const_add x
  simpa [Function.comp_def] using
    hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)

/-- **Jacobian entries at a point of differentiability.** Let $f : \mathbb{R}^m \to \mathbb{R}^n$
be differentiable at $x \in \mathbb{R}^m$. Then for every row index $i$ and column index $j$, the
$(i, j)$ entry of the Jacobian matrix of $f$ at $x$ is the $i$-th coordinate of $Df(x)\, e_j$,
where $Df(x)$ is the Fréchet derivative of $f$ at $x$ and $e_j$ is the $j$-th standard basis
vector of $\mathbb{R}^m$. -/
theorem jacobianMatrix_apply_of_differentiableAt {m n : ℕ}
    (f : (Fin m → ℝ) → (Fin n → ℝ)) (x : Fin m → ℝ)
    (hf : DifferentiableAt ℝ f x) (i : Fin n) (j : Fin m) :
    jacobianMatrix f x i j = fderiv ℝ f x (Pi.single j (1 : ℝ)) i := by
  rw [jacobianMatrix_apply]
  exact (hasDerivAt_pi.mp (jacobian_hasDerivAt_along_single f x hf j) i).deriv

/-- **The Jacobian is the matrix of the derivative.** Let $f : \mathbb{R}^m \to \mathbb{R}^n$ be
differentiable at $x \in \mathbb{R}^m$. Then the Jacobian matrix of $f$ at $x$ is the matrix, in
the standard bases of $\mathbb{R}^m$ and $\mathbb{R}^n$, of the Fréchet derivative of $f$ at $x$,
viewed as a linear map $\mathbb{R}^m \to \mathbb{R}^n$. -/
theorem jacobianMatrix_eq_toMatrix'_fderiv {m n : ℕ}
    (f : (Fin m → ℝ) → (Fin n → ℝ)) (x : Fin m → ℝ)
    (hf : DifferentiableAt ℝ f x) :
    jacobianMatrix f x = LinearMap.toMatrix' (fderiv ℝ f x).toLinearMap := by
  ext i j
  rw [jacobianMatrix_apply_of_differentiableAt f x hf, LinearMap.toMatrix'_apply]
  rfl

/-- **Jacobian of a linear map given by a matrix.** Let $M$ be a real $n \times m$ matrix. At every
point $x \in \mathbb{R}^m$, the Jacobian matrix of the map $y \mapsto M y$ from $\mathbb{R}^m$ to
$\mathbb{R}^n$ is $M$. -/
theorem jacobianMatrix_fun_mulVec {m n : ℕ}
    (M : Matrix (Fin n) (Fin m) ℝ) (x : Fin m → ℝ) :
    jacobianMatrix (fun y => M *ᵥ y) x = M := by
  let L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ) :=
    LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)
  change jacobianMatrix (fun y => L y) x = M
  ext i j
  rw [jacobianMatrix_apply_of_differentiableAt (fun y => L y) x L.differentiableAt]
  change (fderiv ℝ L x) (Pi.single j 1) i = M i j
  rw [L.fderiv]
  simp [L]

/-- **The Jacobian matrix computes the derivative.** Let $f : \mathbb{R}^m \to \mathbb{R}^n$ be
differentiable at $x \in \mathbb{R}^m$, and let $J$ be the Jacobian matrix of $f$ at $x$. Then for
every $v \in \mathbb{R}^m$, the product $J v$ equals $Df(x)\, v$, the Fréchet derivative of $f$ at
$x$ applied to $v$.

Proof: The Jacobian is the matrix of the Fréchet derivative (Wikipedia, "Jacobian matrix and
determinant": it represents the total derivative), and multiplying a vector by the matrix of a
linear map applies the map to that vector.

Proves `Wanted` entry `jacobianMatrix_mulVec_eq_fderiv`.

Sources: `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` /
`Differential calculus`, entry `Jacobian matrix` (unmapped);
W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 9.
-/
theorem jacobianMatrix_mulVec_eq_fderiv {m n : ℕ}
    (f : (Fin m → ℝ) → (Fin n → ℝ)) (x : Fin m → ℝ)
    (hf : DifferentiableAt ℝ f x) (v : Fin m → ℝ) :
    (jacobianMatrix f x).mulVec v = fderiv ℝ f x v := by
  rw [jacobianMatrix_eq_toMatrix'_fderiv f x hf, LinearMap.toMatrix'_mulVec]
  rfl

/-- **Chain rule for Jacobian matrices.** Let $f : \mathbb{R}^m \to \mathbb{R}^n$,
$g : \mathbb{R}^n \to \mathbb{R}^p$ and $x \in \mathbb{R}^m$, and write $J_h(y)$ for the Jacobian
matrix of $h$ at $y$. If $f$ is differentiable at $x$ and $g$ is differentiable at $f(x)$, then
$J_{g \circ f}(x) = J_g(f(x))\, J_f(x)$, a product of a $p \times n$ and an $n \times m$ matrix.

Proof: As in Wikipedia, "Jacobian matrix and determinant" (chain rule), write each Jacobian as
the matrix of the Fréchet derivative, then use the chain rule for Fréchet derivatives and the
fact that the matrix of a composition of linear maps is the product of their matrices.

Proves `Wanted` entry `jacobianMatrix_comp`.

Sources: `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` /
`Differential calculus`, entries `Jacobian matrix` and `chain rule`;
W. Rudin, Principles of Mathematical Analysis, 3rd ed., Theorem 9.15.
-/
theorem jacobianMatrix_comp {m n p : ℕ}
    (f : (Fin m → ℝ) → (Fin n → ℝ)) (g : (Fin n → ℝ) → (Fin p → ℝ))
    (x : Fin m → ℝ)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g (f x)) :
    jacobianMatrix (g ∘ f) x =
      (jacobianMatrix g (f x)) * (jacobianMatrix f x) := by
  rw [jacobianMatrix_eq_toMatrix'_fderiv (g ∘ f) x (hg.comp x hf),
    jacobianMatrix_eq_toMatrix'_fderiv g (f x) hg,
    jacobianMatrix_eq_toMatrix'_fderiv f x hf,
    fderiv_comp x hg hf, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.toMatrix'_comp]

end MetaMathlibExt
