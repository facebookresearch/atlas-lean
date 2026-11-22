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
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Lagrange

@[expose] public section

namespace Lagrange

variable {n : ℕ} (x : Fin n → ℝ)

/-- Lagrange fundamental polynomial `l_k(t)` for nodes `x`, via Mathlib's
`Lagrange.basis` evaluated at `t`. -/
noncomputable def evalBasis (k : Fin n) (t : ℝ) : ℝ :=
  Polynomial.eval t (Lagrange.basis Finset.univ x k)

/-- Lebesgue function `Lₙ(t) = ∑_k |l_k(t)|`. -/
noncomputable def lebesgueFunction (t : ℝ) : ℝ :=
  ∑ k : Fin n, |Lagrange.evalBasis x k t|

/-- Lagrange interpolant `𝓛ⁿf(t) = ∑ₖ f(xₖ) * lₖ(t)`. -/
noncomputable def evalInterpolant (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ k : Fin n, f (x k) * Lagrange.evalBasis x k t

/-- The evaluated basis is `1` at its own node for injective nodes. -/
theorem evalBasis_self (hx : Function.Injective x) (k : Fin n) :
    Lagrange.evalBasis x k (x k) = 1 := by
  unfold Lagrange.evalBasis
  apply Lagrange.eval_basis_self
  · intro i _ j _ h
    exact hx h
  · exact Finset.mem_univ k

/-- The evaluated basis is `0` at other nodes. -/
theorem evalBasis_of_ne {k j : Fin n} (hkj : k ≠ j) :
    Lagrange.evalBasis x k (x j) = 0 := by
  unfold Lagrange.evalBasis
  exact Lagrange.eval_basis_of_ne hkj (Finset.mem_univ j)

/-- For injective nodes, the Lagrange interpolant agrees with the sampled function at each node. -/
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

/-- For injective nodes, the Lebesgue function equals `1` at every node. -/
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
