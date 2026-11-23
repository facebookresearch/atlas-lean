/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.NormNum

import MathlibExt.LinearAlgebra.Matrix.SinkhornMargins

/-!
# Sinkhorn margin checks

Focused checks for `MathlibExt.LinearAlgebra.Matrix.SinkhornMargins`:
unit scalings reproduce the kernel margins, and gauge scaling by `2`
leaves the table unchanged.

These are elaboration and non-vacuity checks, not new results.
-/

open SinkhornMargins

/-- Unit scalings: row sums are the kernel row sums. -/
example (K : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2) :
    ∑ j, scaledTable (fun _ => (1 : ℝ)) K (fun _ => (1 : ℝ)) i j
      = ∑ j, K i j :=
  scaledTable_row_sum (fun _ => (1 : ℝ)) K (fun _ => (1 : ℝ))
    (fun i => ∑ j, K i j) (fun i => by simp) i

/-- Gauge invariance at `t = 2`, entrywise through the theorem. -/
example (a : Fin 2 → ℝ) (K : Matrix (Fin 2) (Fin 2) ℝ) (b : Fin 2 → ℝ) :
    scaledTable (fun i => 2 * a i) K (fun j => (2 : ℝ)⁻¹ * b j)
      = scaledTable a K b :=
  scaledTable_gauge a K b (by norm_num)
