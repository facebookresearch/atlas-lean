/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.ContDiffOnPi

@[expose] public section

open scoped ContDiff

universe u

/-! The source statements, with their original binders. -/

example {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : (Fin n → ℂ) → E} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) : ContDiffOn ℂ 1 f U :=
  Complex.contDiffOn_one_of_differentiableOn_pi hU hf

example {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : (Fin n → ℂ) → E} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) : ContDiffOn ℂ ∞ f U :=
  Complex.contDiffOn_infty_of_differentiableOn_pi hU hf

/-! The codomain may live in any universe. -/

example {n : ℕ} {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : (Fin n → ℂ) → E} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) : ContDiffOn ℂ ∞ f U :=
  Complex.contDiffOn_infty_of_differentiableOn_pi hU hf
