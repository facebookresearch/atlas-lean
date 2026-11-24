/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.IrrationalStartProgressions

open MetaMathlibExt

-- A positive integer step is allowed, including at index zero in the doubled progression.
example : Real.sqrt 2 + 1 ∉ Set.range ((↑) : ℕ → ℝ) ∧
    2 * Real.sqrt 2 ∉ Set.range ((↑) : ℕ → ℝ) := by
  simpa using add_mul_not_mem_nat_of_irrational_of_rat _ 1 irrational_sqrt_two
    ⟨1, Rat.cast_one⟩ 1 0
