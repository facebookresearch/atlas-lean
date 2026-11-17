/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DirichletCharacter.PolyaVinogradov

/-!
# Tests for the Pólya–Vinogradov inequality

The cosecant bound at `θ = π/2` (alternating sums of `±1` are bounded by `1`), and
instantiations of the Pólya–Vinogradov inequality.
-/

@[expose] public section

open Finset Complex

namespace PolyaVinogradovTest

/-- `‖∑_{a ≤ n < b} e^{iπn}‖ ≤ 1`. -/
example (a b : ℕ) : ‖∑ n ∈ Ico a b, exp (2 * (Real.pi / 2) * n * I)‖ ≤ 1 := by
  have h := Complex.norm_sum_Ico_exp_mul_I_le (θ := Real.pi / 2) (by simp) a b
  simpa using h

example {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, χ n‖ ≤ 2 * Real.sqrt q * (1 + Real.log q) :=
  DirichletCharacter.norm_sum_Icc_le hχ N

example {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (a b : ℕ) :
    ‖∑ n ∈ Ico a b, χ n‖ ≤ 10 * Real.sqrt q * Real.log q :=
  DirichletCharacter.norm_sum_Ico_le_sqrt_mul_log hχ a b

/-- The primitive form at the (vacuous) boundary `q = 1`: there is no nontrivial character. -/
example (χ : DirichletCharacter ℂ 1) : χ = 1 := DirichletCharacter.level_one χ

end PolyaVinogradovTest
