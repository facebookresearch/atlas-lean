/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Dynamics.Epidemiology.NextGenerationMatrixBasic

open MathlibExt.Biology.Epidemiology

/-! Compile checks for the definition of `R₀ = ρ(F V⁻¹)`. -/

/-- `R0` is the real spectral radius of `F V⁻¹`, read as a complex matrix. -/
example {ι : Type*} [Fintype ι] [DecidableEq ι] (F V : Matrix ι ι ℝ) :
    NextGenerationMatrix.R0 F V =
      (spectralRadius ℂ ((F * V⁻¹).map (algebraMap ℝ ℂ))).toReal :=
  rfl

/-- With `V = 1`, `R0 F 1` is the spectral radius of `F` itself. -/
example {ι : Type*} [Fintype ι] [DecidableEq ι] (F : Matrix ι ι ℝ) :
    NextGenerationMatrix.R0 F 1 = (spectralRadius ℂ (F.map (algebraMap ℝ ℂ))).toReal := by
  simp [NextGenerationMatrix.R0]
