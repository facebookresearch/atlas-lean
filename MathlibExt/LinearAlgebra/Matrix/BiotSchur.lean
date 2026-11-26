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
public import MathlibExt.LinearAlgebra.Matrix.BlockSolutionEquiv
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

- `BiotSchur.biot_schur`: elimination and recovery (derived from
  `BlockSolutionEquiv.elim_forward`).
- `BiotSchur.biot_rate_equation`: the dynamic Biot rate form.

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
  have : Invertible K := ⟨Kinv, hK', hK⟩
  have hKinv : K⁻¹ = Kinv := Matrix.inv_eq_right_inv hK
  have h1' : (-C) *ᵥ p + Qᵀ *ᵥ u = g := by
    rw [Matrix.neg_mulVec, add_comm (-(C *ᵥ p)) (Qᵀ *ᵥ u), ← sub_eq_add_neg]
    exact h2
  have h2' : Q *ᵥ p + K *ᵥ u = f := by
    rw [add_comm (Q *ᵥ p) (K *ᵥ u)]
    exact h1
  obtain ⟨hschur, hrec⟩ :=
    MathlibExt.LinearAlgebra.Matrix.BlockSolutionEquiv.elim_forward
      (A := -C) (B := Qᵀ) (C := Q) (D := K)
      (x := p) (y := u) (u := g) (v := f) h1' h2'
  have hschur2 : ((-C) - Qᵀ * K⁻¹ * Q) *ᵥ p = g - Qᵀ *ᵥ (K⁻¹ *ᵥ f) := hschur
  rw [hKinv] at hrec hschur2
  refine ⟨hrec, ?_⟩
  have hmat : (-C) - Qᵀ * Kinv * Q = -(Qᵀ * Kinv * Q + C) := by
    rw [sub_eq_add_neg, neg_add_rev]
  rw [hmat, Matrix.neg_mulVec] at hschur2
  apply neg_inj.mp
  rw [neg_sub]
  exact hschur2


/-- Biot rate form: at each time step (or for the differentiated
system), with rates `du, dp, df` satisfying `K *ᵥ du + Q *ᵥ dp = df`
and the storage balance `Qᵀ *ᵥ du - C *ᵥ dp = s - H *ᵥ p`, the
pressure rate solves the Biot storage equation
`(Qᵀ K⁻¹ Q + C) *ᵥ dp = Qᵀ K⁻¹ df - s + H *ᵥ p`, and `du` is
recovered from the first equation. This is block elimination with
signed forcing: with the left side of the second equation as written,
the dissipative storage balance of `EarthScience.SatisfiesBiotRateSystem`
has right-hand side `H *ᵥ p - s`. -/
theorem biot_rate_equation {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (K : Matrix n n ℝ) (Kinv : Matrix n n ℝ)
    (hK : K * Kinv = 1) (hK' : Kinv * K = 1)
    (Q : Matrix n m ℝ) (C H : Matrix m m ℝ)
    (du : n → ℝ) (dp : m → ℝ) (df : n → ℝ) (s : m → ℝ) (p : m → ℝ)
    (h1 : K *ᵥ du + Q *ᵥ dp = df)
    (h2 : Qᵀ *ᵥ du - C *ᵥ dp = s - H *ᵥ p) :
    du = Kinv *ᵥ (df - Q *ᵥ dp)
      ∧ (Qᵀ * Kinv * Q + C) *ᵥ dp
        = Qᵀ *ᵥ (Kinv *ᵥ df) - s + H *ᵥ p := by
  obtain ⟨hdu, hdp⟩ := biot_schur K Kinv hK hK' Q C du dp df (s - H *ᵥ p) h1 h2
  refine ⟨hdu, ?_⟩
  rw [hdp]
  abel

end BiotSchur
