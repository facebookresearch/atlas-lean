/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.AutomorphicForm.SatakePow

public import Mathlib.Algebra.Ring.Int.Defs

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

namespace AutomorphicFormSatakePowTest

/-- `exactSource` consumer with the original binders. -/
public theorem exactSource {R : Type*} [CommRing R] (α β : R) :
    ∀ n : ℕ, AutomorphicForm.satakePow n (α + β) (α * β) = α ^ n + β ^ n :=
  AutomorphicForm.satakePow_add_pow α β

/-- Higher-universe consumer. -/
public theorem exactSourceTypeOne {R : Type 1} [CommRing R] (α β : R) :
    ∀ n : ℕ, AutomorphicForm.satakePow n (α + β) (α * β) = α ^ n + β ^ n :=
  AutomorphicForm.satakePow_add_pow α β

/-- Repeated parameters: the value is twice the common power. -/
public example {R : Type*} [CommRing R] (α : R) (n : ℕ) :
    AutomorphicForm.satakePow n (α + α) (α * α) = 2 * α ^ n := by
  rw [AutomorphicForm.satakePow_add_pow]
  ring

/-- Zero parameters at positive exponent. -/
public example (n : ℕ) :
    AutomorphicForm.satakePow (n + 1) (0 + 0 : ℤ) (0 * 0) = 0 := by
  rw [AutomorphicForm.satakePow_add_pow]
  simp

/-- Concrete value: for `α = 2` and `β = 3`, the second power sum is `13`. -/
public example :
    AutomorphicForm.satakePow 2 (2 + 3 : ℤ) (2 * 3) = 13 := by
  rw [AutomorphicForm.satakePow_add_pow]
  norm_num

/-- The initial value is `2`, so the recurrence does not start at `1`. -/
public example (s e : ℤ) : AutomorphicForm.satakePow 0 s e ≠ 1 := by
  rw [AutomorphicForm.satakePow_zero]
  norm_num

end AutomorphicFormSatakePowTest
