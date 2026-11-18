/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Real.Basic
public import MathlibExt.LinearAlgebra.Matrix.FullRankLinearSystem

open scoped Matrix

/-!
# First-order form of the mass equation

The pointwise inversion of the mass equation is
`Matrix.mulVec_eq_iff_inv_mulVec`: under `IsUnit M.det`,
`M *ᵥ a = F ↔ a = M⁻¹ *ᵥ F`. This module adds the first-order
packaging used by state-space models: `firstOrderRhs M F v`
names the derivative pair `(v, M⁻¹ *ᵥ F)`, and
`eq_firstOrderRhs_iff` characterizes the pairs equal to it.
Deriving the mechanics equation itself is out of scope.
-/

@[expose] public section

namespace ControlTheory

/-- The first-order right-hand side of the mass equation at
velocity `v` under net force `F`: the pair `(v, M⁻¹ *ᵥ F)` of
velocity and acceleration. -/
noncomputable def firstOrderRhs {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (F v : n → ℝ) : (n → ℝ) × (n → ℝ) :=
  (v, M⁻¹ *ᵥ F)

/-- A derivative pair `(x, y)` is the first-order right-hand side
if and only if the position derivative is the velocity and the
velocity derivative solves the mass equation. -/
theorem eq_firstOrderRhs_iff {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (hM : IsUnit M.det) (F v x y : n → ℝ) :
    (x, y) = firstOrderRhs M F v ↔ x = v ∧ M *ᵥ y = F := by
  unfold firstOrderRhs
  simp only [Prod.mk.injEq, Matrix.mulVec_eq_iff_inv_mulVec hM]

end ControlTheory
