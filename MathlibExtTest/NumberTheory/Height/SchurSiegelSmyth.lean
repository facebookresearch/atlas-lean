/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Height.SchurSiegelSmyth

/-!
# Schur--Siegel--Smyth constant public-API and boundary checks

Exact-statement exercises for totally positive algebraic integers, their
absolute traces, admissible trace bounds, and the extended-real
Schur--Siegel--Smyth constant.
-/

@[expose] public section

namespace SchurSiegelSmythTest

open MathlibExt.NumberTheory.SchurSiegelSmyth

/-- Total positivity is witnessed by `1`. -/
example : IsTotallyPositive (1 : ℂ) :=
  isTotallyPositive_one

/-- The conjugates of `1` are just `{1}`, of degree `1`. -/
example : conjugates (1 : ℂ) = {1} ∧ degree (1 : ℂ) = 1 :=
  ⟨conjugates_one, degree_one⟩

/-- The absolute trace of `1` is `1`. -/
example : absoluteTrace (1 : ℂ) = 1 :=
  absoluteTrace_one

/-- Absolute traces of totally positive algebraic integers are
positive. -/
example {α : ℂ} (hα : IsTotallyPositive α) : 0 < absoluteTrace α :=
  absoluteTrace_pos hα

/-- Every totally positive algebraic integer occurs among its own
conjugates. -/
example {α : ℂ} (hα : IsTotallyPositive α) : α ∈ conjugates α :=
  self_mem_conjugates hα.1

/-- Bound `0` is admissible, and admissibility is downward closed. -/
example : IsAdmissible 0 ∧
    ∀ {ρ ρ' : ℝ}, IsAdmissible ρ → ρ' ≤ ρ → 0 ≤ ρ' → IsAdmissible ρ' :=
  ⟨isAdmissible_zero, fun h hle h0 => h.mono hle h0⟩

/-- Every admissible bound is at most the constant; in particular the
constant is nonnegative. -/
example {ρ : ℝ} (hρ : IsAdmissible ρ) :
    (ρ : EReal) ≤ schurSiegelSmythConstant ∧
      (0 : EReal) ≤ schurSiegelSmythConstant :=
  ⟨coe_le_schurSiegelSmythConstant hρ, zero_le_schurSiegelSmythConstant⟩

/-- Upper bounds on the constant are checked against admissible bounds
only. -/
example {b : EReal} :
    schurSiegelSmythConstant ≤ b ↔
      ∀ ρ : ℝ, IsAdmissible ρ → (ρ : EReal) ≤ b :=
  schurSiegelSmythConstant_le_iff

end SchurSiegelSmythTest
