/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.RademacherTypeCotype

/-!
# Tests for Rademacher type and cotype 2 of Hilbert spaces

* Concrete second-moment computations: real scalars `![3, 4]` (sum `100`),
  complex scalars `![1, 2]` (sum `20`), the empty family (`0`).
* The unit vector family `![1, I]` in `ℂ`: the average squared Rademacher
  sum equals `2`.
* The average-norm bound on `![3, 4]` in `ℝ`: the average Rademacher norm
  is at most `5`.
* `#print axioms` for the main theorem: standard triple only.
-/

open Finset
open MathlibExt.Analysis.InnerProductSpace.RademacherTypeCotype

namespace MathlibExtTest.Analysis.InnerProductSpace.RademacherTypeCotypeTests

/-- Real scalars `![3, 4]`: the four signed sums are `7, -1, 1, -7`,
squares `49, 1, 1, 49`, total `100 = 4 * (9 + 16)`. -/
example : ∑ ε : Fin 2 → Bool, (∑ i, (if ε i then (![3, 4] : Fin 2 → ℝ) i
      else -(![3, 4] : Fin 2 → ℝ) i)) ^ 2 = 100 := by
  rw [sum_rademacher_sq_real]
  norm_num [Fin.sum_univ_two]

/-- Complex scalars `![1, 2]`: total `20 = 4 * (1 + 4)`. -/
example : ∑ ε : Fin 2 → Bool, ‖∑ i, rademacherSign ℂ ε i •
      (![1, 2] : Fin 2 → ℂ) i‖ ^ 2 = 20 := by
  rw [sum_rademacher_sq_norm_eq]
  norm_num [Fin.sum_univ_two]

/-- The empty family: the (single) empty Rademacher sum is `0`. -/
example : ∑ ε : Fin 0 → Bool, ‖∑ i, rademacherSign ℝ ε i •
      (![] : Fin 0 → ℝ) i‖ ^ 2 = 0 := by
  rw [sum_rademacher_sq_norm_eq]
  simp

/-- Unit vector pair `![1, I]` in `ℂ`: the average squared Rademacher
sum equals `2`. -/
example : ((2 : ℝ) ^ 2) ⁻¹ * ∑ ε : Fin 2 → Bool, ‖∑ i, rademacherSign ℂ ε i •
      (![1, Complex.I] : Fin 2 → ℂ) i‖ ^ 2 = 2 := by
  apply average_rademacher_sq_norm_eq_of_norm_eq_one
  intro i
  fin_cases i <;> simp [Complex.norm_I]

/-- Type 2 on the complex example: the average is at most `1 + 4`. -/
example : ((2 : ℝ) ^ 2) ⁻¹ * ∑ ε : Fin 2 → Bool, ‖∑ i, rademacherSign ℂ ε i •
      (![1, 2] : Fin 2 → ℂ) i‖ ^ 2 ≤ 5 := by
  rw [average_rademacher_sq_norm_eq]
  norm_num [Fin.sum_univ_two]

/-- Cotype 2 on the complex example: `1 + 4` is at most the average. -/
example : (5 : ℝ) ≤ ((2 : ℝ) ^ 2) ⁻¹ * ∑ ε : Fin 2 → Bool, ‖∑ i,
      rademacherSign ℂ ε i • (![1, 2] : Fin 2 → ℂ) i‖ ^ 2 := by
  rw [average_rademacher_sq_norm_eq]
  norm_num [Fin.sum_univ_two]

/-- Average-norm bound on `![3, 4]` in `ℝ`: the average Rademacher norm
is at most `√25 = 5`. -/
example : ((2 : ℝ) ^ 2) ⁻¹ * ∑ ε : Fin 2 → Bool, ‖∑ i, rademacherSign ℝ ε i •
      (![3, 4] : Fin 2 → ℝ) i‖ ≤ 5 := by
  have h := average_rademacher_norm_le (𝕜 := ℝ) (E := ℝ) 2 (![3, 4] : Fin 2 → ℝ)
  have hsum : (∑ i, ‖(![3, 4] : Fin 2 → ℝ) i‖ ^ 2) = 25 := by
    norm_num [Fin.sum_univ_two]
  rw [hsum] at h
  have hsqrt : Real.sqrt (25 : ℝ) = 5 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rwa [hsqrt] at h

#print axioms sum_rademacher_sq_norm_eq

#print axioms average_rademacher_sq_norm_eq

end MathlibExtTest.Analysis.InnerProductSpace.RademacherTypeCotypeTests
