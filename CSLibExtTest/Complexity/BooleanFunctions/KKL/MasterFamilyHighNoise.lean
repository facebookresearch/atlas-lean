/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.MasterFamilyHighNoise
public import CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.CoupledTensorizeWitness
public import CSLibExtTest.Complexity.BooleanFunctions.Hypercontractivity.FullRangeHC

/-!
# Tests for the per-coordinate high-noise route

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.MasterFamilyHighNoise`, at the `AND` function
on `{0, 1}^Bool` (influences `1/2` at `p = 1/2`):

* `mfp2_noiseGap_pos` at `p = 3/4`, `u = 1/2`;
* `mfp2_perCoordHighNoise_half` at `AND`: `(2 - u)/4 ≤ (1/2)^{2/(2-u)}` for `u ∈ (0, 1)`;
* `mfp2_master_half_via_perCoord` at `AND`;
* `mfp2_singleBit_q_gt_2_false`;
* the window predicate `mfp2_PerCoordHighNoise q` holds for `q ≤ 1/2` (empty window) and fails for
  every `q > 9/10` (`ctp_perCoordHighNoise_false`, from the two-bit `OR` function at `p = 9/10`);
  for `q ∈ (1/2, 9/10]` it is neither proved nor refuted here. The conditional theorems
  (`mfp2_openResidue_of_perCoordHighNoise`, `mfp2_kesten_of_perCoordHighNoise`,
  `mfp2_kkl_logGain_of_perCoordHighNoise`) therefore have only the degenerate instance `q = 1/2`,
  recorded for `mfp2_openResidue_of_perCoordHighNoise`.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.Probability

example : 0 < (1 - 1 / 2) - (1 - 1 / 2) * (4 * (3 / 4) * (1 - 3 / 4) : ℝ) :=
  mfp2_noiseGap_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The per-coordinate sum of `mfp2_PerCoordHighNoise` is `frh_perCoordWeight`. -/
lemma mfp2t_perCoordSum_eq {p u : ℝ} (hu : u ≤ 1) (φ : ConfigSpace Bool → Bool) (e : Bool) :
    (∑ S ∈ Finset.univ.filter (fun S : Finset Bool => e ∈ S),
        (1 - u) ^ (S.erase e).card * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S
          / ptn_sigma p) ^ 2) = frh_perCoordWeight p u φ e := by
  unfold frh_perCoordWeight
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← pow_mul, mul_comm (S.erase e).card, pow_mul, Real.sq_sqrt (by linarith)]

/-- `mfp2_perCoordHighNoise_half` at `AND`. -/
example {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (e : Bool) :
    (2 - u) / 4 ≤ (1 / 2 : ℝ) ^ (2 / (2 - u)) := by
  have h := mfp2_perCoordHighNoise_half andFun hu0 hu1 e
  rw [mfp2t_perCoordSum_eq hu1.le, frh_perCoordWeight_andFun (by norm_num) (by norm_num) u hu1.le,
    infl_andFun] at h
  convert h using 1
  ring

/-- `mfp2_master_half_via_perCoord` at `AND`. -/
example {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    8 * (1 / 2 : ℝ) ^ 3 * (1 - 1 / 2) + 8 * (1 - u) * (1 / 2) ^ 2 * (1 - 1 / 2) ^ 2
      ≤ (1 / 2 : ℝ) ^ (u / (2 - u)) * 1 := by
  have h := mfp2_master_half_via_perCoord andFun hu0 hu1
  rwa [cappedSum_andInd (by norm_num) (by norm_num), maxInfl_andInd, totalInfl_andInd] at h

example : ¬ mfp_SingleBitQGt2 (9 / 10) := mfp2_singleBit_q_gt_2_false

/-- `mfp2_PerCoordHighNoise q` for `q ≤ 1/2` holds vacuously. -/
lemma mfp2t_perCoordHighNoise_of_le_half {q : ℝ} (hq : q ≤ 1 / 2) : mfp2_PerCoordHighNoise q :=
  fun _ hp => absurd (hp.1.trans hp.2) (not_lt.mpr hq)

example : ¬ mfp2_PerCoordHighNoise 1 := ctp_perCoordHighNoise_false (by norm_num)

example : frh_openResidue (1 / 2) :=
  mfp2_openResidue_of_perCoordHighNoise (mfp2t_perCoordHighNoise_of_le_half le_rfl)

end StatMechTest.BooleanFunctions
