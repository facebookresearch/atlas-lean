/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.PopulationGenetics.FloatLoglik
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.Abs

@[expose] public section

namespace CslibExtTest.Bioinformatics.PopulationGenetics.FloatLoglik

open Cslib.Algorithms.Lean.Numerical.Summation
open Cslib.Bioinformatics.PopulationGenetics.FloatLoglik

/-- One exact site value: the enclosure is the one-step rounded-summation
bound `u * |l₁|`. -/
example (p : ℕ) :
    |rsum p (List.ofFn (fun _ : Fin 1 => (-5 : ℝ))) - ∑ _ : Fin 1, (-5 : ℝ)| ≤
      ((1 + unitRoundoff p) ^ 1 - 1) * (∑ _ : Fin 1, |(-5 : ℝ)|) +
        ∑ _ : Fin 1, (0 : ℝ) :=
  abs_rsum_sub_sum_le p (fun _ => (-5 : ℝ)) (fun _ => (-5 : ℝ)) (fun _ => (0 : ℝ))
    fun i => by fin_cases i; norm_num

/-- The same one-site case, simplified to the usual `u |l₁|` form via the
underlying rounded-summation theorem. -/
example (p : ℕ) (x : ℝ) : |rsum p [x] - x| ≤ unitRoundoff p * |x| := by
  have h := rsum_abs_sub_le p [x]
  simpa using h

end CslibExtTest.Bioinformatics.PopulationGenetics.FloatLoglik
