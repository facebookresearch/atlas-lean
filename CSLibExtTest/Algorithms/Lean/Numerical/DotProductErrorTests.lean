/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Numerical.DotProductError
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

open Finset Cslib.Algorithms.Lean.FloatingPoint Cslib.Algorithms.Lean.FloatingPoint.DotProductError

namespace CSLibExtTest.Algorithms.Lean.Numerical.DotProductErrorTests

/-- `γ₁ = u / (1 - u)`; with `p = 1`, `u = 1/2` and `γ₁ = 1`. -/
example : (gamma 1 1 : ℝ) = 1 := by
  norm_num [gamma]

/-- The hypothesis `n u < 1` holds in IEEE double precision (`p = 53`) for a dot product of
length `10⁶`, and the bound then applies. -/
example (x y : ℕ → ℝ) :
    |dotFl 53 x y (10 ^ 6) - ∑ i ∈ range (10 ^ 6), x i * y i| ≤
      gamma 53 (10 ^ 6) * ∑ i ∈ range (10 ^ 6), |x i * y i| :=
  abs_dotFl_sub_le (by norm_num) x y _ (by norm_num)

/-- A dot product of length `0` is computed exactly. -/
example (x y : ℕ → ℝ) : dotFl 53 x y 0 = 0 := rfl

/-- The entrywise matrix-product bound in double precision for `3 × 3` real matrices. -/
example (A B : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    |matMulFl 53 A B i j - (A * B) i j| ≤ gamma 53 3 * ∑ k, |A i k| * |B k j| :=
  abs_matMulFl_sub_le (by norm_num) A B (by norm_num) i j

end CSLibExtTest.Algorithms.Lean.Numerical.DotProductErrorTests
