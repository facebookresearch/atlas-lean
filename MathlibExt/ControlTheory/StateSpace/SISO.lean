/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Real.Basic

/-!
# Real single-input single-output linear systems

A finite-dimensional state space with matrix dynamics and scalar feedthrough.
-/

@[expose] public section

open Matrix

namespace MathlibExt.Biology.Dynamics.IntegralFeedback

/-- A single-input single-output linear time-invariant system `ẋ = A x + u b`,
`y = c ⬝ x + d u` with state space `n → ℝ`. -/
structure LinearSystem (n : Type*) where
  /-- The state matrix. -/
  A : Matrix n n ℝ
  /-- The input vector. -/
  b : n → ℝ
  /-- The output functional. -/
  c : n → ℝ
  /-- The direct feedthrough from input to output. -/
  d : ℝ

variable {n : Type*} [Fintype n] (S : LinearSystem n)

namespace LinearSystem

/-- The vector field `A x + u b` at state `x` and input `u`. -/
def field (x : n → ℝ) (u : ℝ) : n → ℝ :=
  S.A *ᵥ x + u • S.b

/-- The output `c ⬝ x + d u`, measured from its adapted value. -/
def output (x : n → ℝ) (u : ℝ) : ℝ :=
  S.c ⬝ᵥ x + S.d * u

end LinearSystem

end MathlibExt.Biology.Dynamics.IntegralFeedback
