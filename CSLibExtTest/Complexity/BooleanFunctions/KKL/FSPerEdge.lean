/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.FSPerEdge
public import CSLibExtTest.Complexity.BooleanFunctions.Hypercontractivity.PBiasedTensorize

/-!
# Tests for the damped KKL inequality under `p`-biased measures

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.FSPerEdge`:

* `fpe_dampedVarLogGain`, which is proved for every `p ∈ (0, 1)`, at the `AND` function on
  `{0, 1}^Bool`: the damped variance is `p²/2 + p²(1-p)²`, the maximal influence `p` and the
  total influence `2p`, so the conclusion is `2 (p²/2 + p²(1-p)²) log (1/p) ≤ 2p` for every
  `p ∈ (0, 1)`; at `p = 3/4` this is `2 · 81/256 · log (4/3) ≤ 3/2`, with a positive left side;
* at `p = 1/2` the damped variance equals the variance (`3/16`);
* `fpe_kklGain_at_half` at `AND` and `fpe_master_sub` instantiated at `p = 3/4`, `u = 1/2`.

The helper `cappedSum_andInd` evaluates the left side of the capped estimates at `AND`; the
test files for the modules downstream of this one reuse it.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.Probability

/-- The damped variance of `AND` under `μ_p`. -/
lemma dampedVar_andInd {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∑ S ∈ Finset.univ.erase (∅ : Finset Bool),
        ((4 * p * (1 - p)) ^ (S.card - 1) / (4 * p * (1 - p))) * (ptn_coeff p andInd S) ^ 2
      = p ^ 2 / 2 + p ^ 2 * (1 - p) ^ 2 := by
  have : 0 < 1 - p := by linarith
  rw [sum_erase_empty_finset_bool, ptn_coeff_andInd_true_sq hp0 hp1,
    ptn_coeff_andInd_false_sq hp0 hp1, ptn_coeff_andInd_univ_sq hp0 hp1]
  simp
  field_simp
  ring

/-- The left side `∑_S 4 |S| (1-u)^{|S|-1} f̂(S)²` of the capped estimates at `AND` under `μ_p`. -/
lemma cappedSum_andInd {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (u : ℝ) :
    ∑ S : Finset Bool, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p andInd S) ^ 2
      = 8 * p ^ 3 * (1 - p) + 8 * (1 - u) * p ^ 2 * (1 - p) ^ 2 := by
  rw [sum_finset_bool, ptn_coeff_andInd_true_sq hp0 hp1, ptn_coeff_andInd_false_sq hp0 hp1,
    ptn_coeff_andInd_univ_sq hp0 hp1]
  simp
  ring

/-- `fpe_dampedVarLogGain` at `AND`, for every `p ∈ (0, 1)`. -/
lemma fpe_at_andFun {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    2 * (p ^ 2 / 2 + p ^ 2 * (1 - p) ^ 2) * Real.log (1 / p) ≤ 2 * p := by
  have h := fpe_dampedVarLogGain hp0 hp1 andFun
  rwa [dampedVar_andInd hp0 hp1, maxInfl_andInd_p, totalInfl_andInd_p] at h

example : 2 * (81 / 256) * Real.log (4 / 3) ≤ (3 / 2 : ℝ) := by
  have h := fpe_at_andFun (p := 3 / 4) (by norm_num) (by norm_num)
  norm_num at h ⊢
  linarith

example : 0 < 2 * (81 / 256) * Real.log (4 / 3 : ℝ) := by
  have := Real.log_pos (show (1 : ℝ) < 4 / 3 by norm_num)
  positivity

/-- At `p = 1/2` the damped variance of `AND` is its variance `3/16`. -/
example : (1 / 2 : ℝ) ^ 2 / 2 + (1 / 2) ^ 2 * (1 - 1 / 2) ^ 2 = 3 / 16 := by norm_num

/-- `fpe_kklGain_at_half` at `AND`: `2 · 3/16 · log 2 ≤ 1`. -/
example : 2 * (3 / 16) * Real.log 2 ≤ (1 : ℝ) := by
  have h := fpe_kklGain_at_half andFun
  rw [var_andFun, maxInfl_andInd, totalInfl_andInd] at h
  simpa using h

example :
    (∑ S : Finset Bool, 4 * (S.card : ℝ)
        * ((4 * (3 / 4) * (1 - 3 / 4)) ^ (S.card - 1) / (4 * (3 / 4) * (1 - 3 / 4)))
        * (1 - 1 / 2) ^ (S.card - 1) * (ptn_coeff (3 / 4) andInd S) ^ 2)
      ≤ (maxInfl (bernoulliWeight (3 / 4)) andInd) ^ ((1 / 2 : ℝ) / (2 - 1 / 2))
        * totalInfl (bernoulliWeight (3 / 4)) andInd :=
  fpe_master_sub (by norm_num) (by norm_num) andFun _ (by norm_num) (by norm_num)

end StatMechTest.BooleanFunctions
