/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.FreeGroupAlgebraTwistedIdealsKourovka12Problem46

open MathlibExt.GroupTheory.FreeGroupAlgebraTwistedIdealsKourovka12Problem46Wanted
open MonoidAlgebra

local notation "R" => MonoidAlgebra ℂ (FreeGroup (Fin 2))
local notation "x" => (FreeGroup.of (0 : Fin 2))
local notation "y" => (FreeGroup.of (1 : Fin 2))

-- A negative exponent contributes the inverse character value.
example (a b : ℂˣ) (c : ℂ) :
    theta a b (single (x * y⁻¹) c) = single (x * y⁻¹) ((a * (b : ℂ)⁻¹) * c) := by
  classical
  simp [theta, twistCharacter, Finsupp.sum_single_index]

-- Specialize the refutation to the admissible sign change on both generators.
example : ∃ α : R, α ≠ 0 ∧ ∀ β γ : R, α * β = theta (-1) (-1) α * γ → α * β = 0 := by
  by_contra! h
  apply twistedRightIdealsIntersect_refuted
  intro α hα
  refine ⟨-1, -1, ?_, ?_, ?_, ?_, h α hα⟩ <;> norm_num [Complex.norm_def]
