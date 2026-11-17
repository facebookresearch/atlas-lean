/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.NormNum

import MathlibExt.LinearAlgebra.Matrix.BiotSchur

/-!
# Biot Schur checks

Focused checks for `MathlibExt.LinearAlgebra.Matrix.BiotSchur`: the
scalar (`Fin 1`) identity-block case recovers `u` and the reduced
equation by computation.

These are elaboration and non-vacuity checks, not new results.
-/

open BiotSchur Matrix

/-- Scalar witness: `u = 3`, `p = 1` from `f = 4`, `g = 2` with
unit blocks and `Q = C = 1`. -/
example : (3 : Fin 1 → ℝ) = (1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ ((4 : Fin 1 → ℝ) - (1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (1 : Fin 1 → ℝ)) := by
  have h := biot_schur (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 (by simp) (by simp)
    1 1 (3 : Fin 1 → ℝ) (1 : Fin 1 → ℝ) 4 2 (by ext i; fin_cases i; norm_num [mulVec, dotProduct])
    (by ext i; fin_cases i; norm_num [mulVec, dotProduct])
  exact h.1

/-- The reduced Schur equation in the same scalar case: `(1+1) • p`
with `p = 1` equals `4 - 2`. -/
example : ((1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * (1 : Matrix (Fin 1) (Fin 1) ℝ)
      * (1 : Matrix (Fin 1) (Fin 1) ℝ) + 1) *ᵥ (1 : Fin 1 → ℝ)
    = (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ *ᵥ
      ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (4 : Fin 1 → ℝ)) - 2 := by
  have h := biot_schur (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 (by simp) (by simp)
    1 1 (3 : Fin 1 → ℝ) (1 : Fin 1 → ℝ) 4 2 (by ext i; fin_cases i; norm_num [mulVec, dotProduct])
    (by ext i; fin_cases i; norm_num [mulVec, dotProduct])
  exact h.2

/-- Rate form on scalar data: `du = 7`, `dp = 1`, `df = 8`,
`H = 3`, `p = 5`, `s = 21`, through `biot_rate_equation`. -/
example : (7 : Fin 1 → ℝ)
    = (1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ
        ((8 : Fin 1 → ℝ) - (1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (1 : Fin 1 → ℝ))
    ∧ ((1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * (1 : Matrix (Fin 1) (Fin 1) ℝ)
          * (1 : Matrix (Fin 1) (Fin 1) ℝ) + 1) *ᵥ (1 : Fin 1 → ℝ)
      = (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ *ᵥ
          ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (8 : Fin 1 → ℝ))
        - (fun _ : Fin 1 => (21 : ℝ))
        + (fun _ _ : Fin 1 => (3 : ℝ)) *ᵥ (fun _ : Fin 1 => (5 : ℝ)) := by
  have h := biot_rate_equation (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 (by simp)
    (by simp) 1 1 (fun _ _ : Fin 1 => (3 : ℝ)) (7 : Fin 1 → ℝ)
    (1 : Fin 1 → ℝ) 8 (fun _ : Fin 1 => (21 : ℝ)) 5
    (by ext i; fin_cases i; norm_num [mulVec, dotProduct])
    (by ext i; fin_cases i; norm_num [mulVec, dotProduct])
  exact h
