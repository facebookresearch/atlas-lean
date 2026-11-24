/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Lidskii
import Mathlib.LinearAlgebra.Matrix.Notation

open Matrix MathlibExt.LinearAlgebra.LidskiiWanted.LinearAlgebra

-- A perturbation supported on one conjugate pair contributes twice the norm of its entry.
example (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian) (z : ℂ) :
    let E : Matrix (Fin 2) (Fin 2) ℂ := !![0, z; star z, 0]
    ∃ h : (A + E).IsHermitian, ∑ j, |h.eigenvalues₀ j - hA.eigenvalues₀ j| ≤ 2 * ‖z‖ := by
  intro E
  have hE : E.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [E]
  refine ⟨hA.add hE, ?_⟩
  simpa [Matrix.add_apply, E, Fin.sum_univ_two, two_mul] using lidskii_last (hA.add hE) hA

-- The theorem also covers an empty index type.
example {A B : Matrix Empty Empty ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∑ j, |hA.eigenvalues₀ j - hB.eigenvalues₀ j| ≤ 0 := by
  simpa only [Finset.univ_eq_empty, Finset.sum_empty] using lidskii_last hA hB
