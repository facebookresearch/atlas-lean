/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.ConjNowhereDifferentiable
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-! # Tests for complex differentiability of conjugation -/

open scoped ComplexConjugate
open MathlibExt.Analysis.Complex.ConjNowhereDifferentiableWanted

-- Even at a fixed point on the real axis, the choice of scalar field matters.
example (x : ℝ) :
    DifferentiableAt ℝ (conj : ℂ → ℂ) (x : ℂ) ∧ ¬ DifferentiableAt ℂ (conj : ℂ → ℂ) (x : ℂ) :=
  ⟨Complex.conjCLE.differentiableAt, not_differentiableAt_conj _ (fun _ => rfl) x⟩
