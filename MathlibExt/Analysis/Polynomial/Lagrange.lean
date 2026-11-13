/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Evaluated Lagrange basis and Lebesgue function

Shared evaluated-basis wrapper around Mathlib's `Lagrange.basis`, plus the
Lebesgue function and Lagrange interpolant built from it.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Lagrange

@[expose] public section

namespace Lagrange

variable {n : ℕ} (x : Fin n → ℝ)

/-- **Evaluated Lagrange basis polynomial.** For real nodes $x_0, \dots, x_{n-1}$, an index
$k < n$ and a real number $t$, the value at $t$ of the $k$-th Lagrange basis polynomial is
$\ell_k(t) = \prod_{j \ne k} (x_k - x_j)^{-1} (t - x_j)$, the product running over the indices
$j < n$ with $j \ne k$.

The inverse follows the convention $0^{-1} = 0$, so $\ell_k$ is identically $0$ when some other
node equals $x_k$. -/
noncomputable def evalBasis (k : Fin n) (t : ℝ) : ℝ :=
  Polynomial.eval t (Lagrange.basis Finset.univ x k)

/-- **Lebesgue function.** For real nodes $x_0, \dots, x_{n-1}$ and a real number $t$, the
Lebesgue function of the nodes at $t$ is $L_n(t) = \sum_{k < n} |\ell_k(t)|$, where $\ell_k$ is
the $k$-th evaluated Lagrange basis polynomial for these nodes. -/
noncomputable def lebesgueFunction (t : ℝ) : ℝ :=
  ∑ k : Fin n, |Lagrange.evalBasis x k t|

/-- **Lagrange interpolant.** For real nodes $x_0, \dots, x_{n-1}$, a function
$f : \mathbb{R} \to \mathbb{R}$ and a real number $t$, the Lagrange interpolant of $f$ at $t$ is
$\mathcal{L}^n f(t) = \sum_{k < n} f(x_k)\, \ell_k(t)$, where $\ell_k$ is the $k$-th evaluated
Lagrange basis polynomial for these nodes. -/
noncomputable def evalInterpolant (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ k : Fin n, f (x k) * Lagrange.evalBasis x k t

/-- **Lagrange basis polynomials equal one at their own node.** If the real nodes
$x_0, \dots, x_{n-1}$ are pairwise distinct, then $\ell_k(x_k) = 1$ for every $k < n$, where
$\ell_k$ is the $k$-th evaluated Lagrange basis polynomial for these nodes. -/
theorem evalBasis_self (hx : Function.Injective x) (k : Fin n) :
    Lagrange.evalBasis x k (x k) = 1 := by
  unfold Lagrange.evalBasis
  apply Lagrange.eval_basis_self
  · intro i _ j _ h
    exact hx h
  · exact Finset.mem_univ k

/-- **Lagrange basis polynomials vanish at the other nodes.** For real nodes
$x_0, \dots, x_{n-1}$ and indices $k \ne j$ below $n$, the $k$-th evaluated Lagrange basis
polynomial $\ell_k$ for these nodes satisfies $\ell_k(x_j) = 0$.

The nodes need not be distinct. -/
theorem evalBasis_of_ne {k j : Fin n} (hkj : k ≠ j) :
    Lagrange.evalBasis x k (x j) = 0 := by
  unfold Lagrange.evalBasis
  exact Lagrange.eval_basis_of_ne hkj (Finset.mem_univ j)

/-- **The Lagrange interpolant matches the function at the nodes.** If the real nodes
$x_0, \dots, x_{n-1}$ are pairwise distinct, then for every function $f : \mathbb{R} \to \mathbb{R}$
and every $j < n$, the Lagrange interpolant of $f$ on these nodes satisfies
$\mathcal{L}^n f(x_j) = f(x_j)$. -/
theorem evalInterpolant_at_node (hx : Function.Injective x) (f : ℝ → ℝ) (j : Fin n) :
    Lagrange.evalInterpolant x f (x j) = f (x j) := by
  classical
  unfold Lagrange.evalInterpolant
  rw [Finset.sum_eq_single j]
  · rw [Lagrange.evalBasis_self x hx]
    simp
  · intro i _ hij
    rw [Lagrange.evalBasis_of_ne x hij]
    simp
  · simp

/-- **The Lebesgue function equals one at the nodes.** If the real nodes $x_0, \dots, x_{n-1}$
are pairwise distinct, then their Lebesgue function satisfies $L_n(x_j) = 1$ for every $j < n$. -/
theorem lebesgueFunction_at_node (hx : Function.Injective x) (j : Fin n) :
    Lagrange.lebesgueFunction x (x j) = 1 := by
  classical
  unfold Lagrange.lebesgueFunction
  rw [Finset.sum_eq_single j]
  · rw [Lagrange.evalBasis_self x hx]
    simp
  · intro i _ hij
    rw [Lagrange.evalBasis_of_ne x hij]
    simp
  · simp

end Lagrange
