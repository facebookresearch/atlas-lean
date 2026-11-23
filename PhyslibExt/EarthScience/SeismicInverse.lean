/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Capstone: synthetic seismic inverse problem

## i. Overview

Exact rational synthetic two-cell model; no full-wave or real-data
correctness claim. Lengths in one length unit, slowness in time / length.
`A = [[1, 1], [1, 2]]`, slowness `s = [1 / 2, 1 / 4]`; travel times
are `[3 / 4, 1]` and full-rank inversion recovers `s`; retaining only
row `[1, 1]` admits null direction `[1, -1]`. The perturbations
`s + t • [1, -1]` with `t ≠ 0` and `-1 / 2 < t < 1 / 4` retain positive
slowness, so the single row cannot distinguish two physically admissible
positive-slowness models. All results are synthetic computations for this
chosen model, hence stated as lemmas. This capstone is proved
self-contained from Mathlib primitives; it does not depend on any
sibling development.

## ii. Key results

- `EarthScience.travel_times_value`: `A *ᵥ s = [3 / 4, 1]`.
- `EarthScience.inversion_recovers_slowness`: full-rank inversion
  recovers `s`.
- `EarthScience.single_row_null_direction`: `[1, 1] ⬝ᵥ [1, -1] = 0`
  and `[1, -1] ≠ 0`.
- `EarthScience.single_row_ambiguity`: the single row cannot
  distinguish `s` from `s + t * [1, -1]`.
- `EarthScience.single_row_positive_ambiguity`: for `t ≠ 0` with
  `-1 / 2 < t < 1 / 4`, `s + t * [1, -1]` is a distinct positive-slowness
  model with the same single-row travel time.

## iii. Table of contents

- A. Travel times and inversion
- B. Single-row ambiguity

## iv. References

- `Matrix.mulVec`, `Matrix.dotProduct`, `Fin.sum_univ_two` in Mathlib.

## A. Travel times and inversion
-/

@[expose] public section

namespace EarthScience


/-- Capstone (synthetic seismic inverse problem): with
`A = [[1, 1], [1, 2]]` and slowness `s = [1 / 2, 1 / 4]`, the travel
times `A *ᵥ s` are `[3 / 4, 1]`. -/
lemma travel_times_value :
    Matrix.mulVec (!![1, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℚ)
        (![1 / 2, 1 / 4] : Fin 2 → ℚ)
      = ![3 / 4, 1] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num

/-- Full-rank inversion recovers `s`: if `A *ᵥ x = [3 / 4, 1]` then
`x = [1 / 2, 1 / 4]`. -/
lemma inversion_recovers_slowness {x : Fin 2 → ℚ}
    (h : Matrix.mulVec (!![1, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℚ) x
      = ![3 / 4, 1]) :
    x = ![1 / 2, 1 / 4] := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  have hx1 : x 1 = 1 / 4 := by linarith
  have hx0 : x 0 = 1 / 2 := by linarith
  funext i
  fin_cases i <;> simp_all

/-! ## B. Single-row ambiguity -/

/-- Null direction of the single retained row `[1, 1]`:
`[1, 1] ⬝ᵥ [1, -1] = 0` and `[1, -1] ≠ 0`. -/
lemma single_row_null_direction :
    (![1, 1] : Fin 2 → ℚ) ⬝ᵥ (![1, -1] : Fin 2 → ℚ) = (0 : ℚ) ∧
      (![1, -1] : Fin 2 → ℚ) ≠ 0 := by
  constructor
  · simp [dotProduct, Fin.sum_univ_two]
  · intro h
    have := congrFun h 0
    simp at this

/-- Retaining only row `[1, 1]` cannot distinguish `s` from
`s + t * [1, -1]`: for every `t`,
`[1, 1] ⬝ᵥ ([1 / 2, 1 / 4] + t • ![1, -1])
= [1, 1] ⬝ᵥ [1 / 2, 1 / 4]`. -/
lemma single_row_ambiguity {t : ℚ} :
    (![1, 1] : Fin 2 → ℚ) ⬝ᵥ
        ((![1 / 2, 1 / 4] : Fin 2 → ℚ) + t • (![1, -1] : Fin 2 → ℚ))
      = (![1, 1] : Fin 2 → ℚ) ⬝ᵥ (![1 / 2, 1 / 4] : Fin 2 → ℚ) := by
  rw [dotProduct_add, dotProduct_smul, single_row_null_direction.1,
    smul_zero, add_zero]

/-- Positive-slowness ambiguity: for every nonzero `t` with
`-1 / 2 < t < 1 / 4`, the perturbed model
`[1 / 2, 1 / 4] + t • ![1, -1] = [1 / 2 + t, 1 / 4 - t]` has positive
slowness in both cells, differs from `s = [1 / 2, 1 / 4]`, and gives the
same travel time as `s` on the single retained row `[1, 1]`. -/
lemma single_row_positive_ambiguity {t : ℚ} (ht : t ≠ 0) (hlo : -1 / 2 < t)
    (hhi : t < 1 / 4) :
    (∀ i, 0 < ((![1 / 2, 1 / 4] : Fin 2 → ℚ) + t • (![1, -1] : Fin 2 → ℚ)) i) ∧
      (![1 / 2, 1 / 4] : Fin 2 → ℚ) + t • (![1, -1] : Fin 2 → ℚ)
        ≠ (![1 / 2, 1 / 4] : Fin 2 → ℚ) ∧
      (![1, 1] : Fin 2 → ℚ) ⬝ᵥ
          ((![1 / 2, 1 / 4] : Fin 2 → ℚ) + t • (![1, -1] : Fin 2 → ℚ))
        = (![1, 1] : Fin 2 → ℚ) ⬝ᵥ (![1 / 2, 1 / 4] : Fin 2 → ℚ) := by
  refine ⟨?_, ?_, single_row_ambiguity⟩
  · intro i
    fin_cases i <;> simp <;> linarith
  · intro h
    apply ht
    simpa using congrFun h 0

end EarthScience
