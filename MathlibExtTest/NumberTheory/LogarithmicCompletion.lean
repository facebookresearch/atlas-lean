/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LogarithmicCompletion

/-! # Endpoint tests for logarithmic completion of quadratic exponential sums -/

namespace MathlibExtTest.NumberTheory.LogarithmicCompletion

open Complex Finset Polynomial

private noncomputable def quadraticMax (p : ℕ) : ℝ :=
  ((range p).sup fun y : ℕ =>
    ‖∑ x ∈ Icc 1 p, exp (2 * Real.pi * I * ((x : ℂ) ^ 2 + y * x) / p)‖₊ : NNReal)

-- At the smallest prime and shortest length the incomplete sum has norm exactly one.
example : 1 < quadraticMax 5 * Real.log 5 := by
  have : Fact (1 < (5 : ℕ)) := ⟨by decide⟩
  have h := MetaMathlibExt.norm_incompleteSum_lt_sup_mul_log 5 (by decide) le_rfl
    (X ^ 2) (by simp) 1 le_rfl (by decide)
  simpa [quadraticMax, norm_exp] using h

-- The closed upper endpoint includes the representative of zero modulo the prime.
example : ‖∑ x ∈ Icc 1 (37 : ℕ), exp (2 * Real.pi * I * (x : ℂ) ^ 2 / 37)‖ <
    quadraticMax 37 * Real.log 37 := by
  have : Fact (1 < (37 : ℕ)) := ⟨by decide⟩
  have h := MetaMathlibExt.norm_incompleteSum_lt_sup_mul_log 37 (by decide) (by decide)
    (X ^ 2) (by simp) 37 (by decide) le_rfl
  simpa [quadraticMax] using h

end MathlibExtTest.NumberTheory.LogarithmicCompletion
