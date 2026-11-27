/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.QuadraticForm.Isotropic
import Mathlib.LinearAlgebra.QuadraticForm.Basis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.LinearAlgebra.QuadraticForm.Isotropic` -/

namespace MathlibExtTest.QuadraticFormIsotropic

-- `x² - y²` over `ℚ` has the nonzero zero `(1, 1)`, and `-(1 · (-1)) = 1` is a square.
example : ∃ x y : ℚ, (x, y) ≠ (0, 0) ∧ 1 * x ^ 2 + (-1) * y ^ 2 = 0 :=
  (exists_ne_zero_mul_sq_add_mul_sq_eq_zero_iff (1 : ℚ) (-1)).mpr ⟨1, by norm_num⟩

-- `x² + y²` over `ℚ` has no nonzero zero, as `-1` is not a square in `ℚ`.
example : ¬∃ x y : ℚ, (x, y) ≠ (0, 0) ∧ 1 * x ^ 2 + 1 * y ^ 2 = 0 := by
  rw [exists_ne_zero_mul_sq_add_mul_sq_eq_zero_iff]
  rintro ⟨c, hc⟩
  nlinarith [mul_self_nonneg c]

-- `2x² - 8y²` over `ℚ` is isotropic: `-(2 · (-8)) = 16 = 4²`.
example : ∃ x y : ℚ, (x, y) ≠ (0, 0) ∧ 2 * x ^ 2 + (-8) * y ^ 2 = 0 :=
  (exists_ne_zero_mul_sq_add_mul_sq_eq_zero_iff (2 : ℚ) (-8)).mpr ⟨4, by norm_num⟩

-- The degenerate cases need no hypothesis: with `b = 0` both sides hold.
example (a : ℚ) : ∃ x y : ℚ, (x, y) ≠ (0, 0) ∧ a * x ^ 2 + 0 * y ^ 2 = 0 :=
  (exists_ne_zero_mul_sq_add_mul_sq_eq_zero_iff a 0).mpr ⟨0, by simp⟩

-- A nondegenerate isotropic form over a field of characteristic `≠ 2` takes the value `1`, and
-- with it every value.
example {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Invertible (2 : K)]
    {Q : QuadraticForm K V} (hQ : Q.Nondegenerate) {v : V} (hv : v ≠ 0) (hQv : Q v = 0) :
    ∃ w : V, Q w = 1 :=
  hQ.exists_apply_eq_of_isotropic hv hQv 1

example {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Invertible (2 : K)]
    {Q : QuadraticForm K V} (hQ : Q.Nondegenerate) {v : V} (hv : v ≠ 0) (hQv : Q v = 0) :
    Function.Surjective Q :=
  fun c => QuadraticMap.Nondegenerate.exists_apply_eq_of_isotropic hQ hv hQv c

-- A concrete nondegenerate isotropic form, so the hypotheses are satisfiable: `x² - y²` on `ℚ²`
-- is nondegenerate (its radical is `0`, as no weight vanishes) and vanishes at `(1, 1)`.
example (c : ℚ) : ∃ w : Fin 2 → ℚ, QuadraticMap.weightedSumSquares ℚ ![(1 : ℚ), -1] w = c := by
  let _ : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero
  have hQ : (QuadraticMap.weightedSumSquares ℚ ![(1 : ℚ), -1]).Nondegenerate := by
    rw [QuadraticMap.nondegenerate_iff_radical_eq_bot, QuadraticForm.radical_weightedSumSquares]
    have hempty : {i : Fin 2 | ![(1 : ℚ), -1] i = 0} = ∅ := by
      ext i
      fin_cases i <;> simp
    rw [hempty]
    simp [Pi.spanSubset]
  refine hQ.exists_apply_eq_of_isotropic (v := ![1, 1]) ?_ ?_ c
  · intro h
    simpa using congrFun h 0
  · simp [QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_two]

end MathlibExtTest.QuadraticFormIsotropic
