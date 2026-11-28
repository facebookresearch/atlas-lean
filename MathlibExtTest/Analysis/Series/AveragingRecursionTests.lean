/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Series.AveragingRecursion

/-!
# Tests for averaging recursions with divergent gains

The gains below sit at both ends of `[0, 1]`: `a 0 = 0` and `a (t + 1) = 1`. With zero input and
the initial value `x 0 = 1`, the iterates are `1, 1, 0, 0, …`. Both averaging lemmas apply to
these data, so a hypothesis excluding endpoint gains or a nonzero initial value would break the
tests.
-/

namespace MathlibExtTest.AveragingRecursion

open Filter Topology

/-- Gains at both endpoints of `[0, 1]`: `0` at time `0`, then `1`. -/
private def gain (t : ℕ) : ℝ := if t = 0 then 0 else 1

/-- The iterates from `x 0 = 1` with zero input: `1, 1, 0, 0, …`. -/
private def iterate (t : ℕ) : ℝ := if t ≤ 1 then 1 else 0

private theorem gain_mem (t : ℕ) : gain t ∈ Set.Icc (0 : ℝ) 1 := by
  unfold gain
  split_ifs <;> norm_num

private theorem sum_gain (n : ℕ) : ∑ t ∈ Finset.range (n + 1), gain t = n := by
  induction n with
  | zero => simp [gain]
  | succ n ih => rw [Finset.sum_range_succ, ih]; simp [gain]

private theorem tendsto_sum_gain :
    Tendsto (fun n => ∑ t ∈ Finset.range n, gain t) atTop atTop := by
  rw [← tendsto_add_atTop_iff_nat 1]
  simpa only [sum_gain] using tendsto_natCast_atTop_atTop

private theorem iterate_succ (t : ℕ) :
    iterate (t + 1) = (1 - gain t) * iterate t + gain t * 0 := by
  rcases t with _ | t <;> simp [iterate, gain]

/-- The data take the edge values: the gains are `0` and `1`, and the iterates start at `1`. -/
example : gain 0 = 0 ∧ gain 1 = 1 ∧ iterate 0 = 1 ∧ iterate 1 = 1 ∧ iterate 2 = 0 := by
  simp [gain, iterate]

/-- `tendsto_zero_of_averaging` with endpoint gains, zero input and `x 0 = 1`. -/
example : Tendsto iterate atTop (𝓝 0) :=
  MetaMathlibExt.tendsto_zero_of_averaging (z := fun _ => 0) gain_mem tendsto_sum_gain
    tendsto_const_nhds iterate_succ

/-- `tendsto_zero_of_averaging_of_tendsto_sum` on the same data: the weighted noise series of the
zero noise converges to `0`. -/
example : Tendsto iterate atTop (𝓝 0) :=
  MetaMathlibExt.tendsto_zero_of_averaging_of_tendsto_sum (w := fun _ => 0) (l := 0) gain_mem
    tendsto_sum_gain (by simp) iterate_succ

end MathlibExtTest.AveragingRecursion
