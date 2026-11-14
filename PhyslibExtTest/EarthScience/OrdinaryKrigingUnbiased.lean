/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Def
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import PhyslibExt.EarthScience.OrdinaryKrigingUnbiased

/-!
# Ordinary kriging is unbiased

Concrete consumers of `PhyslibExt.EarthScience.OrdinaryKrigingUnbiased`.

## i. Overview

Two-point kriging system `C = [[2, 1], [1, 2]]`, weights `[0.5, 0.5]`,
multiplier `0.5`, right-hand side `[2, 2]`, constant observations of mean
`5`; and the single-site boundary case with weight `1` and mean `7`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric and boundary checks

## iv. References

- `PhyslibExt.EarthScience.OrdinaryKrigingUnbiased`
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix

/-- Two-point kriging: weights `[0.5, 0.5]` satisfy the ordinary kriging
system with `C = [[2, 1], [1, 2]]`, `m = 0.5`, `c = [2, 2]`, and constant
observations of mean `5` give estimator mean `5`. -/
example :
    ∫ _ : ℝ, ∑ i : Fin 2, (![0.5, 0.5] : Fin 2 → ℝ) i * (5 : ℝ) ∂(Measure.dirac 0) = 5 := by
  have hSys : (∀ i : Fin 2,
        ((!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ (![0.5, 0.5] : Fin 2 → ℝ)) i
          + (0.5 : ℝ) = (![2, 2] : Fin 2 → ℝ) i) ∧
      ∑ i : Fin 2, (![0.5, 0.5] : Fin 2 → ℝ) i = 1 := by
    constructor
    · intro i
      fin_cases i <;> norm_num [Matrix.mulVec, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.tail_cons]
    · rw [Fin.sum_univ_two]
      norm_num
  have h := EarthScience.ordinary_kriging_unbiased (ι := Fin 2) (Ω := ℝ)
    (μ := Measure.dirac 0) (Z := fun _ _ => (5 : ℝ)) (mean := 5)
    (C := !![2, 1; 1, 2]) (c := ![2, 2]) (m := 0.5) (lam := ![0.5, 0.5])
    (hMean := fun _ => by simp) (hInt := fun _ => integrable_const 5) hSys
  simpa using h

/-- Single-site boundary case: weight `1` satisfies the kriging system
with `C = [[1]]`, `m = 0`, `c = [1]`, and a constant observation of mean
`7` gives estimator mean `7`. -/
example :
    ∫ _ : ℝ, ∑ i : Fin 1, (![1] : Fin 1 → ℝ) i * (7 : ℝ) ∂(Measure.dirac 0) = 7 := by
  have hSys : (∀ i : Fin 1,
        ((!![1] : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (![1] : Fin 1 → ℝ)) i
          + (0 : ℝ) = (![1] : Fin 1 → ℝ) i) ∧
      ∑ i : Fin 1, (![1] : Fin 1 → ℝ) i = 1 := by
    constructor
    · intro i
      fin_cases i
      norm_num [Matrix.mulVec, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.tail_cons]
    · rw [Fin.sum_univ_one]
      norm_num
  have h := EarthScience.ordinary_kriging_unbiased (ι := Fin 1) (Ω := ℝ)
    (μ := Measure.dirac 0) (Z := fun _ _ => (7 : ℝ)) (mean := 7)
    (C := !![1]) (c := ![1]) (m := 0) (lam := ![1])
    (hMean := fun _ => by simp) (hInt := fun _ => integrable_const 7) hSys
  exact h
