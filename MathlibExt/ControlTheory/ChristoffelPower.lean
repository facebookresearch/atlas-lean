/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring

/-!
# Christoffel power cancellation

For a derivative tensor `D` of a mass matrix and a velocity
`v`, the Christoffel correction `C` built from the first-kind
symbols `Γ i j k = (D i j k + D i k j - D j k i) / 2` makes the
quadratic power form of `Mdot - 2C` vanish:
`v ⬝ᵥ ((Mdot - 2 • C) *ᵥ v) = 0`. This is the algebraic
cancellation behind the skew-symmetry used in mechanical
energy arguments; identifying `D` with the derivative of a
concrete mass matrix is a separate step.
-/

@[expose] public section

open scoped Matrix

namespace ControlTheory

/-- The first-kind Christoffel symbol built from a derivative
tensor `D`, where `D i j k` represents the derivative of the
`(i, j)` mass-matrix entry along coordinate `k`:
`Γ i j k = (D i j k + D i k j - D j k i) / 2`. -/
noncomputable def christoffel {ι : Type*} (D : ι → ι → ι → ℝ) (i j k : ι) : ℝ :=
  (D i j k + D i k j - D j k i) / 2

/-- The Christoffel correction matrix `C` at velocity `v`,
with `C i j = ∑ k, Γ i j k * v k`. -/
noncomputable def christoffelMatrix {ι : Type*} [Fintype ι]
    (D : ι → ι → ι → ℝ) (v : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => ∑ k, christoffel D i j k * v k

/-- The mass-matrix rate at velocity `v`, with
`Mdot i j = ∑ k, D i j k * v k`. -/
def massMatrixRate {ι : Type*} [Fintype ι]
    (D : ι → ι → ι → ℝ) (v : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => ∑ k, D i j k * v k

private theorem sum_eq_zero_of_antisymm {ι : Type*} [Fintype ι] (F : ι → ι → ι → ℝ)
    (h : ∀ a b k, F a b k = -F b a k) :
    ∑ a, ∑ b, ∑ k, F a b k = 0 := by
  have hanti : ∀ a b, (∑ k, F b a k) = -(∑ k, F a b k) := by
    intro a b
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun k _ => h b a k)
  have hSS : (∑ a, ∑ b, ∑ k, F a b k) = -(∑ a, ∑ b, ∑ k, F a b k) := by
    have h1 : (∑ a, ∑ b, ∑ k, F a b k) = ∑ a, ∑ b, ∑ k, F b a k := by
      rw [Finset.sum_comm]
    have h2 : (∑ a, ∑ b, ∑ k, F b a k) = -(∑ a, ∑ b, ∑ k, F a b k) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun b _ => hanti a b)
    exact h1.trans h2
  exact eq_zero_of_neg_eq hSS.symm

/-- Power cancellation for the Christoffel correction: the
quadratic form of `Mdot - 2C` at `v` vanishes,
`v ⬝ᵥ ((Mdot - 2 • C) *ᵥ v) = 0`, by antisymmetry of the
summand under swapping the two outer indices. -/
theorem christoffelCancellation_dotProduct_eq_zero
    {ι : Type*} [Fintype ι] (D : ι → ι → ι → ℝ) (v : ι → ℝ) :
    v ⬝ᵥ ((massMatrixRate D v - 2 • christoffelMatrix D v) *ᵥ v) = 0 := by
  have hsub : ∀ i j, (massMatrixRate D v - 2 • christoffelMatrix D v) i j
      = ∑ k, ((D j k i - D i k j) * v k) := by
    intro i j
    simp only [massMatrixRate, christoffelMatrix, christoffel, Matrix.sub_apply,
      two_nsmul, Matrix.add_apply]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [Matrix.dot_mulVec_eq_sum_sum]
  simp only [hsub, Finset.mul_sum, Finset.sum_mul]
  apply sum_eq_zero_of_antisymm
  intro a b k
  ring

end ControlTheory
