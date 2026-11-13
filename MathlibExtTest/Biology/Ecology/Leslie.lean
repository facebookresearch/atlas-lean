/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Ecology.Leslie
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Tests for the Leslie matrix and the discrete Euler–Lotka equation.

Ground-truth computations (explicit entries, a hand-computed population update, survivorship
values, and Euler–Lotka sums checked directly) are kept separate from applications of the main
theorems. Examples:

* two classes, `f = (1, 3/2)`, `s = (1/2, ·)`: `λ = 3/2`, stable vector `v = (3, 1)`;
* three classes, `f = (0, 1, 2)`, `s = (1/2, 1/2, ·)`: `λ = 1`, stable vector `v = (4, 2, 1)`;
* zero fertility (no births), and the one-class case `L = (f 0)`. -/

open Matrix

namespace MathlibExtTest.Biology.Ecology.Leslie

open MathlibExt.Biology.Ecology.Leslie

/-! ### Ground truth: entries -/

/-- Two classes: `L = [[1, 3/2], [1/2, 0]]`; the last survival probability (here `5`) is
unused. -/
example : leslieMatrix ![1, 3 / 2] ![1 / 2, 5] = !![1, 3 / 2; 1 / 2, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leslieMatrix]

/-- Three classes: `L = [[0, 1, 2], [1/2, 0, 0], [0, 1/2, 0]]`; `s 2 = 7` is unused. -/
example :
    leslieMatrix ![0, 1, 2] ![1 / 2, 1 / 2, 7] = !![0, 1, 2; 1 / 2, 0, 0; 0, 1 / 2, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leslieMatrix]

/-- One class: `L = (f 0)`. -/
example (a b : ℝ) : leslieMatrix ![a] ![b] = !![a] := by
  ext i j
  fin_cases i; fin_cases j
  simp [leslieMatrix]

/-- Zero fertility: the first row vanishes. -/
example (s : Fin 3 → ℝ) (j : Fin 3) : leslieMatrix 0 s 0 j = 0 := by
  simp [leslieMatrix]

/-! ### Ground truth: population update and survivorship -/

/-- Hand computation: `(10, 20, 30) ↦ (0·10 + 1·20 + 2·30, ½·10, ½·20) = (80, 5, 10)`. -/
example : leslieMatrix ![0, 1, 2] ![1 / 2, 1 / 2, 7] *ᵥ ![10, 20, 30] = ![80, 5, 10] := by
  ext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three, leslieMatrix] <;> norm_num

/-- Survivorship from the definition: `l = (1, 1/2, 1/4)` for `s = (1/2, 1/2, ·)`. -/
example : survivorship ![1 / 2, 1 / 2, 7] (2 : Fin 3) = 1 / 4 := by
  have : Finset.Iio (2 : Fin 3) = {0, 1} := by decide
  rw [survivorship, this, Finset.prod_pair (by decide)]
  norm_num

/-! ### Ground truth: eigenpairs and Euler–Lotka sums checked directly -/

example : leslieMatrix ![1, 3 / 2] ![1 / 2, 5] *ᵥ ![3, 1] = (3 / 2 : ℝ) • ![3, 1] := by
  ext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two, leslieMatrix] <;> norm_num

/-- `1 · 1 / (3/2) + (3/2) · (1/2) / (3/2)² = 2/3 + 1/3 = 1`, from the definitions. -/
example : ∑ i : Fin 2, (![1, 3 / 2] : Fin 2 → ℝ) i * survivorship ![1 / 2, 5] i /
    (3 / 2 : ℝ) ^ (i.val + 1) = 1 := by
  have h0 : Finset.Iio (0 : Fin 2) = ∅ := by decide
  have h1 : Finset.Iio (1 : Fin 2) = {0} := by decide
  simp [Fin.sum_univ_two, survivorship, h0, h1]
  norm_num

example : leslieMatrix ![0, 1, 2] ![1 / 2, 1 / 2, 7] *ᵥ ![4, 2, 1] = (1 : ℝ) • ![4, 2, 1] := by
  ext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three, leslieMatrix] <;> norm_num

/-! ### Applications of the main theorems -/

/-- Births with zero fertility vanish. -/
example (s v : Fin 3 → ℝ) : (leslieMatrix 0 s *ᵥ v) 0 = 0 := by
  simp

/-- Survivors move one class up: `(L v) 1 = s 0 v 0`. -/
example (f s v : Fin 3 → ℝ) : (leslieMatrix f s *ᵥ v) 1 = s 0 * v 0 :=
  leslieMatrix_mulVec_succ f s v (0 : Fin 2)

example (f s : Fin 3 → ℝ) (hf : ∀ j, 0 ≤ f j) (hs : ∀ j, 0 ≤ s j) (i j : Fin 3) :
    0 ≤ leslieMatrix f s i j :=
  leslieMatrix_nonneg f s hf hs i j

/-- Euler–Lotka for the two-class eigenpair `λ = 3/2`, `v = (3, 1)`. -/
example : ∑ i : Fin 2, (![1, 3 / 2] : Fin 2 → ℝ) i * survivorship ![1 / 2, 5] i /
    (3 / 2 : ℝ) ^ (i.val + 1) = 1 := by
  refine sum_fertility_mul_survivorship_div_pow_eq_one _ _ (v := ![3, 1]) ?_ (by norm_num)
    (by norm_num)
  ext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two, leslieMatrix] <;> norm_num

/-- Euler–Lotka for the three-class eigenpair `λ = 1`, `v = (4, 2, 1)`. -/
example : ∑ i : Fin 3, (![0, 1, 2] : Fin 3 → ℝ) i * survivorship ![1 / 2, 1 / 2, 7] i /
    (1 : ℝ) ^ (i.val + 1) = 1 := by
  refine sum_fertility_mul_survivorship_div_pow_eq_one _ _ (v := ![4, 2, 1]) ?_ one_ne_zero
    (by norm_num)
  ext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three, leslieMatrix] <;> norm_num

/-- One class: Euler–Lotka reduces to `f 0 / λ = 1`. -/
example (a b lam : ℝ) (v : Fin 1 → ℝ) (hv : leslieMatrix ![a] ![b] *ᵥ v = lam • v)
    (hlam : lam ≠ 0) (hv0 : v 0 ≠ 0) : a / lam = 1 := by
  simpa using sum_fertility_mul_survivorship_div_pow_eq_one _ _ hv hlam hv0

/-- Stable age distribution for the three-class example: `v 2 · λ² = v 0 · l 2`. -/
example : (![4, 2, 1] : Fin 3 → ℝ) 2 * 1 ^ (2 : Fin 3).val =
    (![4, 2, 1] : Fin 3 → ℝ) 0 * survivorship ![1 / 2, 1 / 2, 7] 2 := by
  refine eigenvector_mul_pow_eq ![0, 1, 2] _ ?_ 2
  ext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three, leslieMatrix] <;> norm_num

/-- **Non-vacuity of the Perron corollary.** The two-class Leslie matrix is irreducible
(`f 1 = 3/2 > 0`, `s 0 = 1/2 > 0`), so its Perron root satisfies Euler–Lotka. -/
example : (leslieMatrix ![1, 3 / 2] ![1 / 2, 5]).IsIrreducible :=
  isIrreducible_leslieMatrix (fun j => by fin_cases j <;> norm_num) (by norm_num)
    (fun j => by fin_cases j; norm_num)

example : ∃ (r : ℝ) (v : Fin 2 → ℝ), 0 < r ∧ (∀ i, 0 < v i) ∧
    leslieMatrix ![1, 3 / 2] ![1 / 2, 5] *ᵥ v = r • v ∧
    ∑ i, (![1, 3 / 2] : Fin 2 → ℝ) i * survivorship ![1 / 2, 5] i / r ^ (i.val + 1) = 1 := by
  obtain ⟨r, v, hr, hv, hev, -, hEL⟩ := exists_perron_root_sum_eq_one
    (isIrreducible_leslieMatrix (f := ![1, 3 / 2]) (s := ![1 / 2, 5])
      (fun j => by fin_cases j <;> norm_num) (by norm_num [Fin.last])
      (fun j => by fin_cases j; norm_num))
  exact ⟨r, v, hr, hv, hev, hEL⟩

end MathlibExtTest.Biology.Ecology.Leslie
