/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Streaming.ReservoirSampling

/-!
# Reservoir sampling tests

Exact point probabilities test joint sampling without replacement; tagged states test
that equal values at different positions survive as distinct occurrences.
-/

namespace Cslib.Algorithms.Lean.ReservoirSampling

open Finset
open scoped ENNReal

-- The replacement threshold at capacity one and the resulting uniform index law.
example : (draw 4).toOuterMeasure (↑({2} : Finset ℕ) : Set ℕ) = 1 / (5 : ℝ≥0∞) := by
  rw [hit_probability (s := {2}) (m := 4) (by decide)]
  norm_num

example : positions 1 5 {2} = (5 : ℝ≥0∞)⁻¹ := one_position (by decide)

-- The whole initial prefix is present at capacity.
example : positions 3 3 = PMF.pure {0, 1, 2} := by
  simp [positions, PMF.pure_map]
  congr 1
  decide

-- A draw hitting an old position evicts it; an unretained old index or the new index is a miss.
example : replacePosition 4 1 {0, 1} = {0, 4} ∧
    replacePosition 4 3 {0, 1} = {0, 1} ∧ replacePosition 4 4 {0, 1} = {0, 1} := by decide

-- Equal inclusion marginals alone would also allow a coin flip between {0,1} and {2,3}.
-- The cross-pair {0,2} has mass zero in that model but 1/6 in the reservoir.
example : positions 2 4 {0, 2} = (6 : ℝ≥0∞)⁻¹ := by
  rw [positions_uniform (by decide), Cslib.Probability.PMF.uniformOfFinset_apply,
    ite_eq_left (by decide), card_powersetCard, card_range]
  rfl

-- Both equal values remain visible when the capacity equals the prefix length.
example : sample 2 (fun _ => 'a') 2 = PMF.pure {(0, 'a'), (1, 'a')} := by
  simp [sample, step, PMF.pure_bind]
  congr 1
  decide

-- A subsequent replacement reads only the incoming item and the previous tagged state.
example : (sample 2 (fun _ => 'a') 4) (tagged (fun _ => 'a') {0, 2}) = (6 : ℝ≥0∞)⁻¹ := by
  rw [sample_eq_tagged, PMF.map_apply, tsum_eq_single {0, 2}]
  · rw [ite_eq_left rfl, positions_uniform (by decide), Cslib.Probability.PMF.uniformOfFinset_apply,
      ite_eq_left (by decide), card_powersetCard, card_range]
    rfl
  · intro s hs
    exact ite_eq_right fun he => hs (Finset.map_injective _ he.symm)

end Cslib.Algorithms.Lean.ReservoirSampling
