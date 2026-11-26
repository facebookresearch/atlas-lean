/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp

/-!
# Finite-population moment closure counterexample

For a nonlinear activation, replacing the expected birth rate by its mean-field closure at the mean is not exact: an explicit two-point law gives exact rate 0 and closure value 1/4.
-/

@[expose] public section

open Finset

namespace MathlibExt.Biology.Dynamics.FiniteActivePopulation.Moment

/-- The mean-field closure counterexample distribution on
`Fin 3`: half mass at `0`, half at `2`. -/
noncomputable def momentWitness : Fin 3 → ℝ :=
  fun i => if i = 0 then 1 / 2 else if i = 2 then 1 / 2 else 0


/-- The witness is nonnegative in every state. -/
lemma momentWitness_nonneg (i : Fin 3) : 0 ≤ momentWitness i := by
  unfold momentWitness
  split_ifs <;> norm_num

/-- The witness has total mass one: it is a probability law on
`Fin 3`. -/
lemma momentWitness_sum_one :
    (∑ i : Fin 3, momentWitness i) = 1 := by
  rw [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ]
  simp only [momentWitness, Finset.sum_range_zero]
  norm_num

/-- **Moment closure is not exact.** For `N = 2`, `alpha = 0`,
and the nonlinear activation `f x = (x / 2) ^ 2`, the exact
initial mean birth rate under the witness law,
`sum_i p_i * (2 - i) * f i`, is `0`, while the mean-field closure
substitution at the mean `E[n] = 1` gives `(2 - 1) * f 1 = 1 / 4`.
Hence replacing the expectation by the closure is not exact. -/
theorem moment_closure_counterexample :
    (∑ i : Fin 3, momentWitness i * ((2 - (i : ℝ)) * ((i : ℝ) / 2) ^ 2)) = 0 ∧
      (2 - (1 : ℝ)) * ((1 : ℝ) / 2) ^ 2 = 1 / 4 ∧
      (∑ i : Fin 3, momentWitness i * (i : ℝ)) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ]
    simp only [momentWitness, Finset.sum_range_zero]
    norm_num
  · norm_num
  · rw [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ]
    simp only [momentWitness, Finset.sum_range_zero]
    norm_num


end MathlibExt.Biology.Dynamics.FiniteActivePopulation.Moment
