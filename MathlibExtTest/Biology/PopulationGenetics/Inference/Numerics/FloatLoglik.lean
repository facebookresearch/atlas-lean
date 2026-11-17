/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Inference.Numerics.FloatLoglik
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.Ineq

@[expose] public section

namespace MathlibExtTest.Biology.PopulationGenetics.Inference.Numerics

open MathlibExt.Biology.PopulationGenetics.Inference.Numerics

/-- One-site enclosure with a nonzero evaluation error and a nonzero
accumulation error. -/
example :
    |( -5 : ℝ) - ∑ _ : Fin 1, (-5 : ℝ)| ≤ (1 / 10 : ℝ) + ∑ _ : Fin 1, (1 / 5 : ℝ) :=
  abs_sub_sum_le_enclosure (fun _ => (-5 : ℝ)) (fun _ => (-51 / 10 : ℝ))
    (fun _ => (1 / 5 : ℝ)) (-5) (1 / 10)
    (fun i => by fin_cases i; norm_num)
    (by norm_num)

/-- Empty-site boundary case. -/
example :
    |(0 : ℝ) - ∑ _ : Fin 0, (0 : ℝ)| ≤ (0 : ℝ) + ∑ _ : Fin 0, (0 : ℝ) :=
  abs_sub_sum_le_enclosure (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
    0 0 (fun i => Fin.elim0 i) (by simp)

/-- A certified likelihood comparison: the exact difference is positive
because the computed gap, `3`, exceeds the total enclosure width, `2`. -/
example :
    SignType.sign ((-1001 : ℝ) - (-1003 : ℝ)) =
      SignType.sign ((-1000 : ℝ) - (-1003 : ℝ)) :=
  sign_sub_eq_of_enclosure (-1000) (-1003) (-1001) (-1003) 2 0
    (by norm_num) (by norm_num) (by norm_num)

end MathlibExtTest.Biology.PopulationGenetics.Inference.Numerics
