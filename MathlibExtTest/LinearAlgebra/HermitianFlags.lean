/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.HermitianFlags

/-!
# Tests for Hermitian projector flags
-/

open MathlibExt.LinearAlgebra.HermitianFlags

/-- The dimensions of the standard flag of `ℂ³` come from the projector traces. -/
example : Module.finrank ℂ (subspace standardFlag 1) = 1 ∧
    Module.finrank ℂ (subspace standardFlag 2) = 2 :=
  ⟨subspace_rank _ _, subspace_rank _ _⟩

/-- The standard line lies in the standard plane. -/
example : subspace standardFlag 1 ≤ subspace standardFlag 2 :=
  subspace_mono _ (by decide)

/-- The first coordinate vector spans the standard line. -/
example : (Pi.single 0 1 : Fin 3 → ℂ) ∈ subspace standardFlag 1 := by
  refine ⟨Pi.single 0 1, ?_⟩
  ext i
  fin_cases i <;> simp [standardFlag, standardMatrices, Matrix.toLin'_apply]
