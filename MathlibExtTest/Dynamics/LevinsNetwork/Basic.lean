/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Dynamics.LevinsNetwork.Basic
import Mathlib.Analysis.Calculus.Deriv.Pi

open MathlibExt.Biology.Ecology MathlibExt.Biology.Epidemiology

/-! Compile checks for the network Levins definitions. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The empty landscape is a rest point of the vector field. -/
example (C : Matrix ι ι ℝ) (e : ι → ℝ) : LevinsNetwork.field C e 0 = 0 := by
  ext i
  simp [LevinsNetwork.field]

/-- The empty landscape, held constant, is a solution. -/
example (C : Matrix ι ι ℝ) (e : ι → ℝ) : LevinsNetwork.IsSolution C e fun _ => 0 :=
  ⟨fun t _ => by
    have h : LevinsNetwork.field C e 0 = 0 := by
      ext i
      simp [LevinsNetwork.field]
    simpa [h] using hasDerivAt_const t (0 : ι → ℝ)⟩

/-- The persistence number is `R0` with new colonizations `C` and losses `diag e`. -/
example (C : Matrix ι ι ℝ) (e : ι → ℝ) :
    LevinsNetwork.persistenceNumber C e = NextGenerationMatrix.R0 C (Matrix.diagonal e) :=
  rfl
