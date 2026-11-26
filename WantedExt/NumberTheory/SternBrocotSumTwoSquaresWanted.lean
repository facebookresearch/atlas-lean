/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.LinearAlgebra.Matrix.Notation
public import MathlibExt.NumberTheory.PerronPalindrome
public import MathlibExt.NumberTheory.SternBrocotPathSquares
public import MathlibExt.NumberTheory.SternBrocotSumTwoSquares

/-!
# Binary trees, continued fractions and sums of two squares

Statements from Hongshen Chua, *Binary Trees and Sum of Two Squares*, INTEGERS 26 (2026),
Article A76. A path in the matrix binary tree is a product of the moves
`R = !![1, 1; 0, 1]` and `L = !![1, 0; 1, 1]` (post-multiplication, starting from the identity);
the Stern–Brocot fraction of a path matrix `P` is the column vector `P (1, 1)ᵀ`. A finite
continued fraction `[q₀; q₁, …, q_m]` is evaluated as the right fold
`q₀ + (q₁ + ⋯ + (q_m + 0⁻¹)⁻¹ ⋯)⁻¹` (with `0⁻¹ = 0`). Theorem 2 (Fermat's two squares theorem)
is Mathlib's `Nat.Prime.sq_add_sq`.
-/
