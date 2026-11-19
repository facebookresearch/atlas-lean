/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.NormNum

import MathlibExt.Combinatorics.Additive.Convolution

/-!
# Sum-convolution total checks

Focused checks for `AdditiveCombinatorics.sum_range_sumConv`: a numeric
case over `ℕ`, the empty-support boundary, and a noncommutative
matrix-semiring case showing no commutativity is used.

These are elaboration and non-vacuity checks, not new results.
-/

open AdditiveCombinatorics

/-- Numeric total over `ℕ`: `(1) * (1 + 1) = 2` through the horizon. -/
example : ∑ k ∈ Finset.range (1 + 2),
      sumConv (fun i => if i = 0 then (1 : ℕ) else 0)
        (fun j => if j < 2 then (1 : ℕ) else 0) k = 2 := by
  have h := sum_range_sumConv (R := ℕ)
    (f := fun i => if i = 0 then (1 : ℕ) else 0)
    (g := fun j => if j < 2 then (1 : ℕ) else 0) (n := 1) (m := 2)
    (by intro i hi; simp [show i ≠ 0 by omega])
    (by intro j hj; simp [show ¬ j < 2 by omega])
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- Empty-support boundary: with `n = 0` both sides are zero. -/
example : ∑ k ∈ Finset.range (0 + 2),
      sumConv (fun _ : ℕ => (0 : ℕ)) (fun j => if j < 2 then (1 : ℕ) else 0) k
    = 0 := by
  have h := sum_range_sumConv (R := ℕ)
    (f := fun _ : ℕ => (0 : ℕ))
    (g := fun j => if j < 2 then (1 : ℕ) else 0) (n := 0) (m := 2)
    (by intro i _; rfl)
    (by intro j hj; simp [show ¬ j < 2 by omega])
  rw [h]
  norm_num

/-- Noncommutative generality: the same total over `2 × 2` matrices. -/
example : ∑ k ∈ Finset.range (1 + 1),
      sumConv (fun i => if i = 0 then (1 : Matrix (Fin 2) (Fin 2) ℕ) else 0)
        (fun j => if j = 0 then (1 : Matrix (Fin 2) (Fin 2) ℕ) else 0) k
    = 1 := by
  have h := sum_range_sumConv (R := Matrix (Fin 2) (Fin 2) ℕ)
    (f := fun i => if i = 0 then (1 : Matrix (Fin 2) (Fin 2) ℕ) else 0)
    (g := fun j => if j = 0 then (1 : Matrix (Fin 2) (Fin 2) ℕ) else 0)
    (n := 1) (m := 1)
    (by intro i hi; simp [show i ≠ 0 by omega])
    (by intro j hj; simp [show j ≠ 0 by omega])
  rw [h]
  simp [Finset.sum_range_succ]
