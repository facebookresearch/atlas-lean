/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Modular.HalfOpenFundamentalDomain

open UpperHalfPlane

open scoped MatrixGroups

/-- Every orbit meets the half-open domain. -/
example (τ : ℍ) :
    ∃ γ : SL(2, ℤ), (γ • τ).re ∈ Set.Ico (-(1 / 2) : ℝ) (1 / 2) ∧ 1 ≤ ‖((γ • τ : ℍ) : ℂ)‖ ∧
      (0 < (γ • τ).re → 1 < ‖((γ • τ : ℍ) : ℂ)‖) :=
  (ModularGroup.exists_smul_mem_halfOpen_and_eq τ).1

/-- `I` lies in the half-open domain, so every element moving `I` into it fixes `I`. -/
example (γ : SL(2, ℤ))
    (h : (γ • I).re ∈ Set.Ico (-(1 / 2) : ℝ) (1 / 2) ∧ 1 ≤ ‖((γ • I : ℍ) : ℂ)‖ ∧
      (0 < (γ • I).re → 1 < ‖((γ • I : ℍ) : ℂ)‖)) :
    γ • I = I :=
  (ModularGroup.exists_smul_mem_halfOpen_and_eq I).2 γ (by norm_num) h

/-- Two points of the half-open domain in one orbit are equal. -/
example (τ : ℍ) (γ : SL(2, ℤ))
    (hτ : τ.re ∈ Set.Ico (-(1 / 2) : ℝ) (1 / 2) ∧ 1 ≤ ‖(τ : ℂ)‖ ∧ (0 < τ.re → 1 < ‖(τ : ℂ)‖))
    (hγτ : (γ • τ).re ∈ Set.Ico (-(1 / 2) : ℝ) (1 / 2) ∧ 1 ≤ ‖((γ • τ : ℍ) : ℂ)‖ ∧
      (0 < (γ • τ).re → 1 < ‖((γ • τ : ℍ) : ℂ)‖)) :
    γ • τ = τ :=
  (ModularGroup.exists_smul_mem_halfOpen_and_eq τ).2 γ hτ hγτ
