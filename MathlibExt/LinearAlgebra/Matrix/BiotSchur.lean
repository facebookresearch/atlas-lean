/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Biot Schur-complement reduction

## i. Overview

For a block system `K u + Q p = f`, `Q^T u - C p = g` with invertible
`K` (supplied two-sided inverse), elimination recovers
`u = K^{-1} (f - Q p)` and the Schur-complement equation
`(Q^T K^{-1} Q + C) p = Q^T K^{-1} f - g`. This is the algebraic step
behind the Biot storage reduction at each time step.

## ii. Key results

- `BiotSchur.biot_schur`: elimination and recovery.

## iii. Table of contents

- A. Schur reduction

## iv. References

- M. A. Biot, general theory of three-dimensional consolidation,
  *J. Appl. Phys.* 12, 1941 (algebraic reduction as stated here).

## A. Schur reduction
-/

@[expose] public section

namespace BiotSchur

open Matrix

/-- Biot Schur-complement reduction. Unknowns `u, p` satisfy
`K *ᵥ u + Q *ᵥ p = f` and `Qᵀ *ᵥ u - C *ᵥ p = g` (sign convention:
storage equation as written). With `K` invertible, elimination gives
`u = K⁻¹ *ᵥ (f - Q *ᵥ p)` and the reduced equation
`(Qᵀ K⁻¹ Q + C) *ᵥ p = Qᵀ K⁻¹ f - g`. All statements are the
algebraic identities under the supplied two-sided inverse. -/
theorem biot_schur {n m : Type*} [Fintype n] [Fintype m]
[DecidableEq n] [DecidableEq m]
(K : Matrix n n ℝ) (Kinv : Matrix n n ℝ)
(hK : K * Kinv = 1) (hK' : Kinv * K = 1)
(Q : Matrix n m ℝ) (C : Matrix m m ℝ)
(u : n → ℝ) (p : m → ℝ) (f : n → ℝ) (g : m → ℝ)
(h1 : K *ᵥ u + Q *ᵥ p = f)
(h2 : Qᵀ *ᵥ u - C *ᵥ p = g) :
u = Kinv *ᵥ (f - Q *ᵥ p)
∧ (Qᵀ * Kinv * Q + C) *ᵥ p = Qᵀ *ᵥ (Kinv *ᵥ f) - g := by
  have _hk := hK
  have hKu : K *ᵥ u = f - Q *ᵥ p := by
    rw [← h1]
    exact (add_sub_cancel_right _ _).symm
  have hu : u = Kinv *ᵥ (f - Q *ᵥ p) := by
    rw [← hKu, Matrix.mulVec_mulVec, hK', Matrix.one_mulVec]
  refine ⟨hu, ?_⟩
  have hsplit : (Qᵀ * Kinv * Q + C) *ᵥ p
      = Qᵀ *ᵥ (Kinv *ᵥ (Q *ᵥ p)) + C *ᵥ p := by
    rw [Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hKf : Kinv *ᵥ f = u + Kinv *ᵥ (Q *ᵥ p) := by
    have hsub := Matrix.mulVec_sub Kinv f (Q *ᵥ p)
    rw [hsub] at hu
    rw [hu]
    exact (sub_add_cancel _ _).symm
  have hQu : Qᵀ *ᵥ u = g + C *ᵥ p := by
    rw [← h2]
    exact (sub_add_cancel _ _).symm
  rw [hsplit, hKf, Matrix.mulVec_add, hQu]
  rw [add_comm (g + C *ᵥ p) _, add_sub_assoc, add_comm g _,
    add_sub_assoc, sub_self, add_zero]

end BiotSchur
