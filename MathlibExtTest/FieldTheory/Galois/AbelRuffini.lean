/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.FieldTheory.Galois.AbelRuffini
import Mathlib.Tactic.NormNum

open Polynomial MathlibExt.Algebra.AbelRuffiniWanted

-- A nonmonic linear polynomial exercises normalization by its leading coefficient.
example : (3 / 2 : ℂ) ∈ solvableByRad ℚ ℂ := by
  apply (abel_ruffini 1 (by decide)).mpr (by decide) (C 2 * X + C (-3))
  · exact natDegree_linear (by decide : (2 : ℚ) ≠ 0)
  · norm_num [aeval_def]

-- The depressed cubic has P = 0 and a triple root; the proof never divides by a cube root.
example : (2 : ℂ) ∈ solvableByRad ℚ ℂ := by
  apply (abel_ruffini 3 (by decide)).mpr (by decide) ((X - C 2) ^ 3)
  · rw [natDegree_pow, natDegree_X_sub_C]
  · norm_num [aeval_def]

-- A root of X⁴ + X - 2 exercises the nonzero-linear-term branch of Ferrari's reduction.
example : (1 : ℂ) ∈ solvableByRad ℚ ℂ := by
  apply (abel_ruffini 4 (by decide)).mpr (by decide) (X ^ 4 + X + C (-2))
  · rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_add_eq_left_of_natDegree_lt,
      natDegree_X_pow]
    · simp
    · rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow, natDegree_C]
      · decide
      · simp
  · norm_num [aeval_def]

-- The biquadratic branch also handles a repeated nonreal root.
example : Complex.I ∈ solvableByRad ℚ ℂ := by
  apply (abel_ruffini 4 (by decide)).mpr (by decide) ((X ^ 2 + 1) ^ 2)
  · rw [natDegree_pow, natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
    simp
  · norm_num [aeval_def, Complex.I_sq]

-- At the cutoff there is a degree-five polynomial with a nonradical complex root.
example : ∃ p : ℚ[X], p.natDegree = 5 ∧ ∃ x : ℂ, aeval x p = 0 ∧ x ∉ solvableByRad ℚ ℂ := by
  by_contra! h
  exact (by decide : ¬ 5 ≤ 4) ((abel_ruffini 5 (by decide)).mp h)
