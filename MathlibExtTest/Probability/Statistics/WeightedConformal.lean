/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.WeightedConformal
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

@[expose] public section

open Finset MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.WeightedConformal

namespace MathlibExtTest.Probability.Statistics.WeightedConformal

/-! ### A worked example

Scores `(1, 2, 3)` with weight `1/4` each and the remaining `1/4` at `+∞`. The cumulative weight
is `1/4` at `1`, `1/2` at `2` and `3/4` at `3`. -/

/-- At level `1/2`, `2` lies below the quantile: only the weight `1/4` of the score `1` is strictly
below `2`. -/
example : ((2 : ℝ) : WithTop ℝ) ≤ weightedQuantile (1 / 2) ![(1 : ℝ), 2, 3] fun _ => 1 / 4 := by
  rw [coe_le_weightedQuantile_iff (by norm_num) _ (fun _ => by norm_num)]
  simp only [Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num

/-- At level `1/2`, `5/2` does not lie below the quantile: the weight strictly below it is
`1/2`. So the quantile is `2`. -/
example :
    ¬ ((5 / 2 : ℝ) : WithTop ℝ) ≤ weightedQuantile (1 / 2) ![(1 : ℝ), 2, 3] fun _ => 1 / 4 := by
  rw [coe_le_weightedQuantile_iff (by norm_num) _ (fun _ => by norm_num)]
  simp only [Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num

/-- At level `9/10` the finite weight `3/4` is short, so the quantile is `+∞` (the atom at
infinity is needed). -/
example : weightedQuantile (9 / 10) ![(1 : ℝ), 2, 3] (fun _ => 1 / 4) = ⊤ := by
  rw [weightedQuantile_eq_top_iff (by norm_num) _ (fun _ => by norm_num)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num

/-- At level `β = 0` the quantile is the least score `1`, so `1` lies below it, although no sum of
nonnegative weights is `< 0`: this is why `coe_le_weightedQuantile_iff` assumes `0 < β`. -/
example : weightedQuantile 0 ![(1 : ℝ), 2, 3] (fun _ => 1 / 4) = ((1 : ℝ) : WithTop ℝ) := by
  have : (univ.filter fun j : Fin 3 => (0 : ℝ) ≤
      ∑ i ∈ univ.filter (fun i => ![(1 : ℝ), 2, 3] i ≤ ![(1 : ℝ), 2, 3] j), (1 / 4 : ℝ)) =
      univ := by
    ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact Finset.sum_nonneg fun _ _ => by norm_num
  rw [weightedQuantile, this]
  simp [Fin.univ_succ]

/-! ### The covariate-shift hypotheses are jointly satisfiable

No shift (`P̃_X = P_X`, so `w = 1`) and a constant conditional law. -/

example : (Measure.dirac (0 : ℝ)) ≪ Measure.dirac (0 : ℝ) := Measure.AbsolutelyContinuous.rfl

example : IsMarkovKernel (Kernel.const ℝ (Measure.dirac (0 : ℝ))) := inferInstance

end MathlibExtTest.Probability.Statistics.WeightedConformal
