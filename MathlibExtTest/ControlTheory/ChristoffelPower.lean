/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.ControlTheory.ChristoffelPower
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

open ControlTheory
open scoped Matrix

/-- A concrete derivative tensor over `Fin 2` with entries
`D i j k = 4i + 2j + k + 1` (so the entries run from 1 to 8). -/
private def tensorEx : Fin 2 → Fin 2 → Fin 2 → ℝ :=
  fun i j k => ((4 * i.val + 2 * j.val + k.val + 1 : ℕ) : ℝ)

private def velEx : Fin 2 → ℝ := ![3, -2]

-- The mass-matrix rate and Christoffel correction entries:
-- `Mdot = !![-1, 1; 3, 5]` and `C = !![-1/2, -1; 3, 5/2]`, so
-- `Mdot - 2C = !![0, 3; -3, 0]` is skew.
example : massMatrixRate tensorEx velEx = !![-1, 1; 3, 5] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [massMatrixRate, tensorEx, velEx, Fin.sum_univ_two] <;> norm_num

example : christoffelMatrix tensorEx velEx = !![-1 / 2, -1; 3, 5 / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [christoffelMatrix, christoffel, tensorEx, velEx, Fin.sum_univ_two] <;>
    norm_num

-- Cancellation on the concrete data, from the theorem.
example :
    velEx ⬝ᵥ ((massMatrixRate tensorEx velEx
      - 2 • christoffelMatrix tensorEx velEx) *ᵥ velEx) = 0 :=
  christoffelCancellation_dotProduct_eq_zero tensorEx velEx

-- Without the correction the power does not cancel: it is -13.
example : velEx ⬝ᵥ (massMatrixRate tensorEx velEx *ᵥ velEx) = -13 := by
  have hM : massMatrixRate tensorEx velEx = !![-1, 1; 3, 5] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [massMatrixRate, tensorEx, velEx, Fin.sum_univ_two] <;> norm_num
  rw [hM]
  simp [velEx, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  norm_num

-- When `D` is symmetric in its first two indices, the
-- Christoffel symbol is symmetric in its last two indices.
example {ι : Type*} (D : ι → ι → ι → ℝ)
    (hD : ∀ i j k, D i j k = D j i k) (i j k : ι) :
    christoffel D i j k = christoffel D i k j := by
  unfold christoffel
  rw [hD j k i]
  ring

#print axioms christoffelCancellation_dotProduct_eq_zero
