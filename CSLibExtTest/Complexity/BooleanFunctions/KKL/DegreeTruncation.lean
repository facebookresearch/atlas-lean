/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.DegreeTruncation
public import CSLibExtTest.Complexity.BooleanFunctions.Hypercontractivity.ConvexGapHC

/-!
# Tests for the degree truncation of the capped estimate

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.DegreeTruncation`:

* `dtr_qstar` at `p = 1/2` (`2 - u`) and at `p = 3/4`, `u = 1/4` (`2`);
* `dtr_full_weight_eq` at the `AND` function reproduces `8p²(1-p) = 4p(1-p) · 2p`;
* `dtr_high_part_le` at `AND` with `k = 1`: `8(1-u)p²(1-p)² ≤ (1-u) · 8p²(1-p)`;
* `dtr_trunc_split` and `dtr_residue_c0` instantiated at `p = 3/4`;
* `dtr_lowDegreeResidue q` is proved here for no `q > 1/2`; it holds for `q ≤ 1/2` because
  `(1/2, q)` is empty, and `dtr_lowDegree_of_residue`, `dtr_smallDelta_of_residue`,
  `dtr_martingaleHC_of_residue` transfer it.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.Probability

example (u : ℝ) : dtr_qstar (1 / 2) u = 2 - u := by
  rw [dtr_qstar]; ring

example : dtr_qstar (3 / 4) (1 / 4) = 2 := by
  rw [dtr_qstar]; norm_num

/-- `dtr_full_weight_eq` at `AND`. -/
example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    4 * (2 * (p ^ 3 * (1 - p)) + 2 * (p ^ 2 * (1 - p) ^ 2)) = 4 * p * (1 - p) * (2 * p) := by
  have h := dtr_full_weight_eq hp0 hp1 andFun
  rw [sum_finset_bool, ptn_coeff_andInd_true_sq hp0 hp1, ptn_coeff_andInd_false_sq hp0 hp1,
    ptn_coeff_andInd_univ_sq hp0 hp1, totalInfl_andInd_p] at h
  simp at h
  linarith

/-- `dtr_high_part_le` at `AND`, `k = 1`: only `S = {true, false}` has degree above `1`. -/
example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    8 * (1 - u) * (p ^ 2 * (1 - p) ^ 2) ≤ (1 - u) * (4 * p * (1 - p) * (2 * p)) := by
  have h := dtr_high_part_le hp0 hp1 andFun hu0 hu1 1
  rw [Finset.sum_filter, sum_finset_bool, ptn_coeff_andInd_univ_sq hp0 hp1,
    totalInfl_andInd_p] at h
  simp at h
  linarith

example :
    (∑ S : Finset Bool, 4 * (S.card : ℝ) * (1 - 1 / 2) ^ (S.card - 1)
        * (ptn_coeff (3 / 4) andInd S) ^ 2)
      ≤ (4 * ∑ S ∈ Finset.univ.filter (fun S : Finset Bool => 1 ≤ S.card ∧ S.card ≤ 1),
            (S.card : ℝ) * (1 - 1 / 2) ^ (S.card - 1) * (ptn_coeff (3 / 4) andInd S) ^ 2)
        + (1 - 1 / 2) ^ 1 * (4 * (3 / 4) * (1 - 3 / 4)
            * totalInfl (bernoulliWeight (3 / 4)) andInd) :=
  dtr_trunc_split (by norm_num) (by norm_num) andFun (by norm_num) (by norm_num) 1

example : ∃ k : ℕ, (0 : ℝ)
    ≤ ((maxInfl (bernoulliWeight (3 / 4)) andInd) ^ ((1 / 2 : ℝ) / (2 - 1 / 2))
        - 4 * (3 / 4) * (1 - 3 / 4) * (1 - 1 / 2) ^ k)
      * totalInfl (bernoulliWeight (3 / 4)) andInd :=
  dtr_residue_c0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) andFun
    (by rw [maxInfl_andInd_p]; positivity)

/-- `dtr_lowDegreeResidue q` for `q ≤ 1/2` holds vacuously. -/
lemma dtr_lowDegreeResidue_of_le_half {q : ℝ} (hq : q ≤ 1 / 2) : dtr_lowDegreeResidue q :=
  fun _ hp => absurd (hp.1.trans hp.2) (not_lt.mpr hq)

example : hcq_lowRangeResidue (1 / 2) :=
  dtr_lowDegree_of_residue (dtr_lowDegreeResidue_of_le_half le_rfl)

example : cvg_smallDeltaResidue (1 / 2) :=
  dtr_smallDelta_of_residue (dtr_lowDegreeResidue_of_le_half le_rfl)

example : mxd_martingaleHC_statement (1 / 2) :=
  dtr_martingaleHC_of_residue (dtr_lowDegreeResidue_of_le_half le_rfl)

end StatMechTest.BooleanFunctions
