/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.FullRangeHC
public import CSLibExtTest.Complexity.BooleanFunctions.KKL.FSPerEdge

/-!
# Tests for the capped estimate in the hypercontractive range

Tests for `CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.FullRangeHC` at the `AND`
function on `{0, 1}^Bool` under `μ_p`, where the capped left side is
`8p³(1-p) + 8(1-u)p²(1-p)²`, the maximal influence `p` and the total influence `2p`:

* `frh_perCoordWeight` is `p` at `u = 0` (the influence) and `p²` at `u = 1`;
* `frh_at_zero` and `frh_endpoint_one` reduce to `4p(1-p) ≤ 1`, with equality at `p = 1/2`;
* `frh_capped_martingale` instantiated at `p = 3/4`, `q' = 2`, `u = 1/4`;
* `frh_openResidue q` is proved here for no `q > 1/2`; it holds for `q ≤ 1/2` because `(1/2, q)`
  is empty, and `frh_martingaleHC_of_openResidue` transfers it.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.Probability

lemma frh_perCoordWeight_andFun {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (u : ℝ) (hu : u ≤ 1)
    (e : Bool) :
    frh_perCoordWeight p u andFun e = p ^ 2 + (1 - u) * (p * (1 - p)) := by
  have : 0 < 1 - p := by linarith
  have hs : Real.sqrt (1 - u) ^ 2 = 1 - u := Real.sq_sqrt (by linarith)
  cases e <;>
  · rw [frh_perCoordWeight, Finset.sum_filter, sum_finset_bool]
    simp only [div_pow, ptn_sigma_sq hp0 hp1]
    rw [ptn_coeff_andInd_true_sq hp0 hp1, ptn_coeff_andInd_false_sq hp0 hp1,
      ptn_coeff_andInd_univ_sq hp0 hp1]
    simp [hs]
    field_simp

example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (e : Bool) :
    frh_perCoordWeight p 0 andFun e = infl (bernoulliWeight p) andInd e := by
  rw [frh_perCoordWeight_andFun hp0 hp1 0 zero_le_one, infl_andInd]; ring

example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (e : Bool) :
    frh_perCoordWeight p 1 andFun e = p ^ 2 := by
  rw [frh_perCoordWeight_andFun hp0 hp1 1 le_rfl]; ring

/-- `frh_at_zero` at `AND`: `8p²(1-p) ≤ 2p`. -/
example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : 8 * p ^ 2 * (1 - p) ≤ 2 * p := by
  have h := frh_at_zero hp0 hp1 andFun
  rw [cappedSum_andInd hp0 hp1, totalInfl_andInd_p] at h
  linarith

/-- `frh_endpoint_one` at `AND`: `8p³(1-p) ≤ p · 2p`. -/
example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : 8 * p ^ 3 * (1 - p) ≤ p * (2 * p) := by
  have h := frh_endpoint_one hp0 hp1 andFun
  rw [cappedSum_andInd hp0 hp1, maxInfl_andInd_p, totalInfl_andInd_p] at h
  norm_num at h
  linarith

/-- At `p = 1/2` both endpoint estimates are equalities for `AND`. -/
example : 8 * (1 / 2 : ℝ) ^ 2 * (1 - 1 / 2) = 2 * (1 / 2) ∧
    8 * (1 / 2 : ℝ) ^ 3 * (1 - 1 / 2) = 1 / 2 * (2 * (1 / 2)) := by norm_num

example :
    (∑ S : Finset Bool, 4 * (S.card : ℝ) * (1 - 1 / 4) ^ (S.card - 1)
        * (ptn_coeff (3 / 4) andInd S) ^ 2)
      ≤ 4 * (ptn_sigma (3 / 4)) ^ 2
        * ((maxInfl (bernoulliWeight (3 / 4)) andInd) ^ (2 / 2 - 1 : ℝ)
          * totalInfl (bernoulliWeight (3 / 4)) andInd) :=
  frh_capped_martingale (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num)
    (by norm_num) (by norm_num) andFun

/-- `frh_openResidue q` for `q ≤ 1/2` holds vacuously. -/
lemma frh_openResidue_of_le_half {q : ℝ} (hq : q ≤ 1 / 2) : frh_openResidue q :=
  fun _ hp => absurd (hp.1.trans hp.2) (not_lt.mpr hq)

example : mxd_martingaleHC_statement (1 / 2) :=
  frh_martingaleHC_of_openResidue (frh_openResidue_of_le_half le_rfl)

end StatMechTest.BooleanFunctions
