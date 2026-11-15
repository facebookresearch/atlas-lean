/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.ModelLineMetrics
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic.NormNum

/-! The actual 2-adic integral ring contains two and excludes its inverse.
Its scalar norm also survives every actual completed residue-field fibre.
These fixtures require no metric, model-frame or analytic provider. -/

open MathlibExt.AlgebraicGeometry.ModelLineMetrics
open MathlibExt.AlgebraicGeometry.ValuedLineFibres
open CategoryTheory AlgebraicGeometry

private theorem ultra : ∀ a b : ℚ_[2], ‖a + b‖ ≤ max ‖a‖ ‖b‖ :=
  Padic.nonarchimedean

private theorem normTwo : ‖(2 : ℚ_[2])‖ = (1 / 2 : ℝ) := by
  have h := Padic.norm_p (p := 2)
  norm_num at h
  exact h

example : (2 : ℚ_[2]) ∈ integerRing ℚ_[2] ultra := by
  change ‖(2 : ℚ_[2])‖ ≤ 1
  rw [normTwo]
  norm_num

example : (2 : ℚ_[2])⁻¹ ∉ integerRing ℚ_[2] ultra := by
  change ¬ ‖(2 : ℚ_[2])⁻¹‖ ≤ 1
  rw [norm_inv, normTwo]
  norm_num

example (X : Over (Spec (.of ℚ_[2]))) (p : Point ℚ_[2] X) :
    ‖completedScalar ℚ_[2] X p (2 : ℚ_[2])‖ = (1 / 2 : ℝ) := by
  rw [completedScalar_norm, normTwo]
