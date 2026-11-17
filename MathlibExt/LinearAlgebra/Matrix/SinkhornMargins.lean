/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Sinkhorn-scaled table margins and gauge

## i. Overview

For a scaled table `T_ij = a_i * K_ij * b_j`, the row and column
margin equations follow from the supplied scaled-kernel equations,
and the table is invariant under the reciprocal gauge
`a -> t * a`, `b -> t^-1 * b`. No existence of factors is asserted.

## ii. Key results

- `SinkhornMargins.scaledTable_row_sum`: row margins.
- `SinkhornMargins.scaledTable_col_sum`: column margins.
- `SinkhornMargins.scaledTable_gauge`: gauge invariance.

## iii. Table of contents

- A. Scaled tables

## iv. References

- R. Sinkhorn and P. Knopp, concerning nonnegative matrices and
  doubly stochastic matrices, *Pacific J. Math.* 21, 1967.

## A. Scaled tables
-/

@[expose] public section

namespace SinkhornMargins

open Finset Matrix

/-- The scaled table `T_ij = a_i * K_ij * b_j`. -/
noncomputable def scaledTable {m n : ℕ} (a : Fin m → ℝ) (K : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin n → ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j => a i * K i j * b j

/-- Row margins: if every `a`-scaled kernel row sums to the target
`r i` in the supplied form `a i * ∑ j, K i j * b j = r i` (no division
by `a i` is used or claimed), the scaled table has row sums `r`. -/
theorem scaledTable_row_sum {m n : ℕ} (a : Fin m → ℝ)
    (K : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (r : Fin m → ℝ)
    (hrow : ∀ i : Fin m, a i * (∑ j, K i j * b j) = r i) (i : Fin m) :
    ∑ j, scaledTable a K b i j = r i := by
  have hterm : ∀ j : Fin n, scaledTable a K b i j = a i * (K i j * b j) := by
    intro j
    simp only [scaledTable]
    ring
  have hsum : ∑ j, scaledTable a K b i j = ∑ j, a i * (K i j * b j) :=
    Finset.sum_congr rfl (fun j _ => hterm j)
  rw [hsum, ← Finset.mul_sum]
  exact hrow i

/-- Column margins, symmetric to the row form. -/
theorem scaledTable_col_sum {m n : ℕ} (a : Fin m → ℝ)
    (K : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) (c : Fin n → ℝ)
    (hcol : ∀ j : Fin n, b j * (∑ i, K i j * a i) = c j) (j : Fin n) :
    ∑ i, scaledTable a K b i j = c j := by
  have hterm : ∀ i : Fin m, scaledTable a K b i j = b j * (K i j * a i) := by
    intro i
    simp only [scaledTable]
    ring
  have hsum : ∑ i, scaledTable a K b i j = ∑ i, b j * (K i j * a i) :=
    Finset.sum_congr rfl (fun i _ => hterm i)
  rw [hsum, ← Finset.mul_sum]
  exact hcol j

/-- Reciprocal gauge invariance: scaling `a` by `t` and `b` by
`t⁻¹` (with `t ≠ 0`) leaves the table unchanged. -/
theorem scaledTable_gauge {m n : ℕ} (a : Fin m → ℝ)
    (K : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) {t : ℝ} (ht : t ≠ 0) :
    scaledTable (fun i => t * a i) K (fun j => t⁻¹ * b j) = scaledTable a K b := by
  funext i j
  simp only [scaledTable]
  calc (t * a i) * K i j * (t⁻¹ * b j)
      = (t * t⁻¹) * (a i * K i j * b j) := by ring
    _ = a i * K i j * b j := by rw [mul_inv_cancel₀ ht, one_mul]

end SinkhornMargins
