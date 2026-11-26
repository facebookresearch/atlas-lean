/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.PBiasedKKLImplications
public import CSLibExtTest.Complexity.BooleanFunctions.KKL.KKLpBiased
public import CSLibExtTest.Complexity.BooleanFunctions.Hypercontractivity.ConvexGapHC

/-!
# Tests for the large-influence `p`-biased KKL gain and the damping-hard chain

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.PBiasedKKLImplications`:

* `pkc_threshold_le_exp_neg_two` at `p = 3/4` and `pkc_threshold_antitone_to_one` at
  `1/2 < 3/4`;
* the unconditional `pkc_kkl_logGain_largeInfl` at the `AND` function on `{0, 1}^Bool`, whose
  maximal influence `p` exceeds the threshold `exp(-1/(2p(1-p)))` for every `p ∈ [1/2, 1)`:
  at `p = 1/2` it reads `2 · 3/16 · log 2 ≤ 1`, at `p = 3/4` it reads
  `2 · 63/256 · log(4/3) ≤ 3/2`;
* `esa_DampingHard q` is proved in this library for no `q > 1/2` (nor refuted); for `q ≤ 1/2`
  it holds because `(1/2, q)` is empty. The chain `pkc_PBiasedHC_of_hard`,
  `pkc_sharpThreshold_of_hard` is instantiated at that degenerate `q = 1/2` (the latter for the
  dictator event); `pkc_kklHC_of_hard` quantifies over `p ∈ (1/2, q)` and has no instance here.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.Probability

example : Real.exp (-(1 / (2 * ((3 / 4 : ℝ) * (1 - 3 / 4))))) ≤ Real.exp (-2) :=
  pkc_threshold_le_exp_neg_two (by norm_num) (by norm_num)

example : Real.exp (-(1 / (2 * ((3 / 4 : ℝ) * (1 - 3 / 4)))))
    ≤ Real.exp (-(1 / (2 * ((1 / 2 : ℝ) * (1 - 1 / 2))))) :=
  pkc_threshold_antitone_to_one le_rfl (by norm_num) (by norm_num)

/-- The `AND` function satisfies the large-influence hypothesis for every `p ∈ [1/2, 1)`. -/
lemma pkct_largeInfl_andFun {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p < 1) :
    Real.exp (-(1 / (2 * (p * (1 - p))))) ≤ maxInfl (bernoulliWeight p) andInd := by
  have hp0 : 0 < p := by linarith
  rw [maxInfl_andInd_p]
  have hq : 0 < 1 - p := by linarith
  have hx : 0 < 2 * (p * (1 - p)) := by positivity
  have hle : Real.exp (-(1 / (2 * (p * (1 - p))))) ≤ 2 * (p * (1 - p)) := by
    have h1 := Real.add_one_le_exp (1 / (2 * (p * (1 - p))))
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) hx, one_div]
    have : (2 * (p * (1 - p)))⁻¹ ≤ Real.exp (2 * (p * (1 - p)))⁻¹ := by
      rw [one_div] at h1; linarith
    exact this
  nlinarith

/-- `pkc_kkl_logGain_largeInfl` at `AND`, for every `p ∈ [1/2, 1)`. -/
lemma pkct_logGain_andFun {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p < 1) :
    2 * (p ^ 2 * (1 - p ^ 2)) * Real.log (1 / p) ≤ 2 * p := by
  have h := pkc_kkl_logGain_largeInfl (by linarith) hp1 andFun (pkct_largeInfl_andFun hp hp1)
  rwa [var_andInd, maxInfl_andInd_p, totalInfl_andInd_p] at h

example : 2 * (3 / 16 : ℝ) * Real.log 2 ≤ 1 := by
  have h := pkct_logGain_andFun (p := 1 / 2) le_rfl (by norm_num)
  norm_num at h ⊢
  linarith

example : 2 * (63 / 256 : ℝ) * Real.log (4 / 3) ≤ 3 / 2 := by
  have h := pkct_logGain_andFun (p := 3 / 4) (by norm_num) (by norm_num)
  norm_num at h ⊢
  linarith

/-- `esa_DampingHard q` for `q ≤ 1/2` holds vacuously. -/
lemma pkct_dampingHard_of_le_half {q : ℝ} (hq : q ≤ 1 / 2) : esa_DampingHard q :=
  fun _ hp => absurd (hp.1.trans hp.2) (not_lt.mpr hq)

example : kpb_PBiasedHC (1 / 2) :=
  pkc_PBiasedHC_of_hard (by norm_num) (pkct_dampingHard_of_le_half le_rfl)

example : 1 / 2 + (2 * 1 * 1) * ((1 / 2 : ℝ) - 1 / 2) ≤ StatMech.prob (1 / 2) dictEvent := by
  classical
  exact pkc_sharpThreshold_of_hard (by norm_num) (pkct_dampingHard_of_le_half le_rfl) dictEvent
    dictEvent_isIncreasing le_rfl zero_le_one zero_le_one prob_dictEvent (by simp) (by simp)

end StatMechTest.BooleanFunctions
