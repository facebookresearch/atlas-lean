/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.ConvexGapHC
public import CSLibExtTest.Complexity.BooleanFunctions.KKL.FSPerEdge

/-!
# Tests for the convexity argument for the capped estimate

Tests for `CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.ConvexGapHC`:

* `cvg_Q_concaveOn` at `m = -1` and `m = 0`, and `cvg_L_convexOn` at the `AND` function, where
  the damped total weight `u ↦ 8p³(1-p) + 8(1-u)p²(1-p)²` is affine;
* `cvg_openResidue_largeDelta` at `AND`: for every `p ∈ (1/2, 1)` the maximal influence `p`
  exceeds `e^{-1}`, so the capped estimate holds for all `u ∈ (0, 1)`; at `p = 3/4`, `u = 1/2`
  it reads `63/64 ≤ (3/4)^{1/3} · 3/2`. In particular `AND` never satisfies the small-`δ`
  hypothesis `maxₑ Infₑ < e^{-1}` of `cvg_smallDeltaResidue` for `p > 1/2`;
* `cvg_smallDeltaResidue q` is proved here for no `q > 1/2`; it holds for `q ≤ 1/2` because
  `(1/2, q)` is empty, and `cvg_openResidue_of_smallDelta`, `cvg_martingaleHC_of_smallDelta`
  transfer it.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.Probability Set

example : ConcaveOn ℝ (Icc (0 : ℝ) 1) (fun u : ℝ => Real.exp (-1 * (u / (2 - u)))) :=
  cvg_Q_concaveOn (by norm_num) le_rfl

example : ConcaveOn ℝ (Icc (0 : ℝ) 1) (fun u : ℝ => Real.exp (0 * (u / (2 - u)))) :=
  cvg_Q_concaveOn le_rfl (by norm_num)

example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ConvexOn ℝ (Icc (0 : ℝ) 1)
      (fun u => 8 * p ^ 3 * (1 - p) + 8 * (1 - u) * p ^ 2 * (1 - p) ^ 2) := by
  have h := cvg_L_convexOn p andFun
  simp only [cappedSum_andInd hp0 hp1] at h
  exact h

lemma exp_neg_one_le_half : Real.exp (-1) ≤ 1 / 2 := by
  have := Real.exp_neg_one_lt_d9
  linarith

/-- The capped estimate at `AND`, for every `p ∈ (1/2, 1)` and `u ∈ (0, 1)`. -/
lemma capped_andFun {p : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    8 * p ^ 3 * (1 - p) + 8 * (1 - u) * p ^ 2 * (1 - p) ^ 2 ≤ p ^ (u / (2 - u)) * (2 * p) := by
  have hp0 : 0 < p := by linarith
  have h := cvg_openResidue_largeDelta hp0 hp1 andFun
    (by rw [maxInfl_andInd_p]; linarith [exp_neg_one_le_half]) hu0 hu1
  rwa [cappedSum_andInd hp0 hp1, maxInfl_andInd_p, totalInfl_andInd_p] at h

example : (63 / 64 : ℝ) ≤ (3 / 4) ^ ((1 / 2 : ℝ) / (2 - 1 / 2)) * (3 / 2) := by
  have h := capped_andFun (p := 3 / 4) (by norm_num) (by norm_num) (u := 1 / 2) (by norm_num)
    (by norm_num)
  norm_num at h ⊢
  linarith

/-- `cvg_smallDeltaResidue q` for `q ≤ 1/2` holds vacuously. -/
lemma cvg_smallDeltaResidue_of_le_half {q : ℝ} (hq : q ≤ 1 / 2) : cvg_smallDeltaResidue q :=
  fun _ hp => absurd (hp.1.trans hp.2) (not_lt.mpr hq)

example : frh_openResidue (1 / 2) :=
  cvg_openResidue_of_smallDelta (cvg_smallDeltaResidue_of_le_half le_rfl)

example : mxd_martingaleHC_statement (1 / 2) :=
  cvg_martingaleHC_of_smallDelta (cvg_smallDeltaResidue_of_le_half le_rfl)

end StatMechTest.BooleanFunctions
