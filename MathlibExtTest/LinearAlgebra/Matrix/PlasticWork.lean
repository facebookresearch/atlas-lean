/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.NormNum

import MathlibExt.LinearAlgebra.Matrix.PlasticWork

/-!
# Plastic-work checks

Focused checks for `MathlibExt.LinearAlgebra.Matrix.PlasticWork`:
the all-ones scalar case attains equality, and doubling the capacity
makes the bound strict (`1 < 2` through the public bound).

These are elaboration and non-vacuity checks, not new results.
-/

open PlasticWork Matrix

/-- Equality in the all-ones scalar case. -/
example : (1 : ℝ) = ∑ e : Fin 1, (fun _ : Fin 1 => (1 : ℝ)) e
    * |((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (fun _ : Fin 1 => (1 : ℝ))) e| := by
  have hmv : (1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (fun _ : Fin 1 => (1 : ℝ))
      = fun _ : Fin 1 => (1 : ℝ) := by
    ext i
    fin_cases i
    simp [mulVec, dotProduct, Matrix.one_apply]
  exact loadFactor_eq_of_complementary
    (B := (1 : Matrix (Fin 1) (Fin 1) ℝ)) (sigma := fun _ : Fin 1 => (1 : ℝ))
    (y := fun _ : Fin 1 => (1 : ℝ)) (f := fun _ : Fin 1 => (1 : ℝ))
    (v := fun _ : Fin 1 => (1 : ℝ)) (lam := (1 : ℝ))
    (by ext i; fin_cases i; norm_num [mulVec, dotProduct, Matrix.one_apply])
    (fun e => by fin_cases e; simp only [abs_one]; exact le_refl _)
    (by simp [dotProduct])
    (fun e => by fin_cases e; rw [hmv]; norm_num)

/-- The bound is strict in the slack case: the dissipation sum
evaluates to `2 > 1`. -/
example : (1 : ℝ) < ∑ e : Fin 1, (fun _ : Fin 1 => (2 : ℝ)) e
    * |((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (fun _ : Fin 1 => (1 : ℝ))) e| := by
  have hsum : ∑ e : Fin 1, (fun _ : Fin 1 => (2 : ℝ)) e
      * |((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (fun _ : Fin 1 => (1 : ℝ))) e|
      = 2 := by
    simp [Finset.sum, mulVec, dotProduct]
  rw [hsum]
  norm_num

/-- The bound in a slack case: `1 ≤ 2`. -/
example : (1 : ℝ) ≤ ((∑ e : Fin 1, (fun _ : Fin 1 => (2 : ℝ)) e
    * |((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (fun _ : Fin 1 => (1 : ℝ))) e|) : ℝ) :=
  loadFactor_le
    (B := (1 : Matrix (Fin 1) (Fin 1) ℝ)) (sigma := fun _ : Fin 1 => (1 : ℝ))
    (y := fun _ : Fin 1 => (2 : ℝ)) (f := fun _ : Fin 1 => (1 : ℝ))
    (v := fun _ : Fin 1 => (1 : ℝ)) (lam := (1 : ℝ))
    (by ext i; fin_cases i; norm_num [mulVec, dotProduct, Matrix.one_apply])
    (fun e => by fin_cases e; simp only [abs_one]; norm_num)
    (by simp [dotProduct])
