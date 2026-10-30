/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.MasterFamilyImplications
public import CSLibExt.Complexity.BooleanFunctions.KKL.MasterFamilyHighNoise
public import CSLibExtTest.Complexity.BooleanFunctions.Hypercontractivity.FullRangeHC

/-!
# Tests for the master family, the chord route and the single-bit test

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.MasterFamilyImplications`:

* `mfp_chord_bound` for `x ↦ x²` on `[0, 1]` at `u = 1/2`, anchor `1`;
* `mfp_L_chord_bound` at the `AND` function on `{0, 1}^Bool` under `μ_p`, where it reads
  `8p³(1-p) + 8(1-u)p²(1-p)² ≤ ((1-u) + up) · 2p`;
* `mfp_chord_route_dead` at `T = 1`: `e^{-1} < 1/2`;
* the predicate `mfp_SingleBitQGt2` holds at `p = 1/2` (`mfp_singleBit_q_gt_2_value`, evaluated at
  `u = 1/2`, `u₀ = 1`, `v₀ = 0`) and fails at `p = 9/10` (`mfp2_singleBit_q_gt_2_false`), so it is
  neither vacuous nor a tautology;
* `mfp_masterFamily_half` at `AND`;
* `mfp_masterFamily q` (definitionally `frh_openResidue q`) is proved here for no `q > 1/2`; it
  holds for `q ≤ 1/2` because `(1/2, q)` is empty. `mfp_martingaleHC_of_masterFamily` is
  instantiated at `q = 1/2`. `mfp_kkl_logGain_of_masterFamily` and `mfp_kesten_of_masterFamily` quantify over `p ∈ (1/2, q)` and so have no instance here.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.Probability Set

/-- `mfp_chord_bound` for the convex function `x ↦ x²`: `(1/2)² ≤ 1/2 · 0 + 1/2 · 1`. -/
example : ((1 : ℝ) / 2) ^ 2 ≤ (1 - (1 / 2) / 1) * 0 ^ 2 + ((1 / 2) / 1) * 1 ^ 2 :=
  mfp_chord_bound (G := fun x : ℝ => x ^ 2)
    ((convexOn_pow 2).subset Icc_subset_Ici_self (convex_Icc 0 1)) one_pos le_rfl
    (by norm_num) (by norm_num)

/-- `mfp_L_chord_bound` at `AND`. -/
example {p u : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    8 * p ^ 3 * (1 - p) + 8 * (1 - u) * p ^ 2 * (1 - p) ^ 2 ≤ ((1 - u) + u * p) * (2 * p) := by
  have h := mfp_L_chord_bound hp0 hp1 andFun hu0 hu1
  rwa [cappedSum_andInd hp0 hp1, maxInfl_andInd_p, totalInfl_andInd_p] at h

example : Real.exp (-3) ^ (((1 : ℝ) / 2) / (2 - 1 / 2)) * 1 < (1 - (1 : ℝ) / 2) * 1 :=
  mfp_chord_route_dead one_pos

/-- `mfp_SingleBitQGt2 (1/2)` at `u = 1/2`, `u₀ = 1`, `v₀ = 0`: `3/8 ≤ (1/2)^{4/3}`. -/
example : (3 / 8 : ℝ) ≤ (1 / 2 : ℝ) ^ ((2 : ℝ) / (2 - 1 / 2)) := by
  have h := mfp_singleBit_q_gt_2_value (1 / 2) (by norm_num) (by norm_num) 1 0
  norm_num at h ⊢
  linarith

example : mfp_SingleBitQGt2 (1 / 2) ∧ ¬ mfp_SingleBitQGt2 (9 / 10) :=
  ⟨mfp_singleBit_q_gt_2_value, mfp2_singleBit_q_gt_2_false⟩

/-- `mfp_masterFamily_half` at `AND`. -/
example {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    8 * (1 / 2 : ℝ) ^ 3 * (1 - 1 / 2) + 8 * (1 - u) * (1 / 2) ^ 2 * (1 - 1 / 2) ^ 2
      ≤ (1 / 2 : ℝ) ^ (u / (2 - u)) * 1 := by
  have h := mfp_masterFamily_half andFun hu0 hu1
  rwa [cappedSum_andInd (by norm_num) (by norm_num), maxInfl_andInd, totalInfl_andInd] at h

example : mfp_masterFamily (1 / 2) := frh_openResidue_of_le_half le_rfl

example : mxd_martingaleHC_statement (1 / 2) :=
  mfp_martingaleHC_of_masterFamily (frh_openResidue_of_le_half le_rfl)

end StatMechTest.BooleanFunctions
