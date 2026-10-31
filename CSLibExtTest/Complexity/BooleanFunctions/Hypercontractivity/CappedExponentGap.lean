/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.CappedExponentGap
public import CSLibExtTest.Complexity.BooleanFunctions.Hypercontractivity.ConvexGapHC

/-!
# Tests for the capped estimate under the exponent-gap condition

Tests for `CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.TwoPointHCqGt2`:

* `hcq_exponent_le` at `p = 3/4`, `q' = 2`, `u = 1/4`;
* `hcq_residue_proper` and `hcq_antecedent_not_tautology` at `p = 3/4`, `δ = 1/2`;
* `hcq_star_capped_threshold` at the `AND` function with `p = 3/4`: the parameter `u` produced
  by `hcq_residue_proper` (with `δ = maxₑ Infₑ = 3/4`) and the matching exponent `q'` satisfy all
  hypotheses, so the capped estimate is derived at a nondegenerate point;
* `hcq_smallDelta_p_half` at `AND`, `u = 1/2`: `3/4 ≤ (1/2)^{1/3}`, a nearly tight instance;
* `hcq_lowRangeResidue q` is proved here for no `q > 1/2`; it holds for `q ≤ 1/2` because
  `(1/2, q)` is empty, and `hcq_smallDelta_of_lowRange`, `hcq_martingaleHC_of_lowRange` transfer
  it. `hcq_lowRange_nonvacuous` (nonnegativity of the right side) at `AND`.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.Probability

example : 2 / (2 : ℝ) - 1 ≤ (1 / 4) / (2 - 1 / 4) :=
  hcq_exponent_le (p := 3 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : ∃ u : ℝ, (0 < u ∧ u < 1) ∧ 1 - 4 * (3 / 4) * (1 - 3 / 4) ≤ u ∧
    4 * (ptn_sigma (3 / 4)) ^ 2
      ≤ (1 / 2 : ℝ) ^ (u / (2 - u) - (2 / (1 + (1 - u) / (4 * (3 / 4) * (1 - 3 / 4))) - 1)) :=
  hcq_residue_proper (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : ∃ u : ℝ, (0 < u ∧ u < 1) ∧
    ¬ (u < 1 - 4 * (3 / 4) * (1 - 3 / 4) ∨
        (1 / 2 : ℝ) ^ (u / (2 - u) - (2 / (1 + (1 - u) / (4 * (3 / 4) * (1 - 3 / 4))) - 1))
          < 4 * (ptn_sigma (3 / 4)) ^ 2) :=
  hcq_antecedent_not_tautology (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `hcq_star_capped_threshold` at `AND`, `p = 3/4`, for the `u` given by `hcq_residue_proper`. -/
example : ∃ u : ℝ, (0 < u ∧ u < 1) ∧
    8 * (3 / 4 : ℝ) ^ 3 * (1 - 3 / 4) + 8 * (1 - u) * (3 / 4) ^ 2 * (1 - 3 / 4) ^ 2
      ≤ (3 / 4) ^ (u / (2 - u)) * (2 * (3 / 4)) := by
  obtain ⟨u, ⟨hu0, hu1⟩, hlo, hthr⟩ :=
    hcq_residue_proper (p := 3 / 4) (δ := 3 / 4) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  refine ⟨u, ⟨hu0, hu1⟩, ?_⟩
  have h := hcq_star_capped_threshold (p := 3 / 4) (by norm_num) (by norm_num) andFun hlo hu1
    (by rw [maxInfl_andInd_p]; norm_num) (q' := 1 + (1 - u) / (4 * (3 / 4) * (1 - 3 / 4)))
    (by have : 0 ≤ (1 - u) / (4 * (3 / 4 : ℝ) * (1 - 3 / 4)) :=
          div_nonneg (by linarith) (by norm_num)
        linarith)
    (by norm_num at hlo ⊢; linarith)
    (by field_simp; ring)
    (by rw [maxInfl_andInd_p]; exact hthr)
  rwa [cappedSum_andInd (by norm_num) (by norm_num), maxInfl_andInd_p, totalInfl_andInd_p] at h

/-- `hcq_smallDelta_p_half` at `AND`, `u = 1/2`. -/
example : (3 / 4 : ℝ) ≤ (1 / 2) ^ ((1 / 2 : ℝ) / (2 - 1 / 2)) * 1 := by
  have h := hcq_smallDelta_p_half andFun (u := 1 / 2) (by norm_num) (by norm_num)
  rw [cappedSum_andInd (by norm_num) (by norm_num), maxInfl_andInd_p, totalInfl_andInd_p] at h
  norm_num at h ⊢
  linarith

/-- `hcq_lowRangeResidue q` for `q ≤ 1/2` holds vacuously. -/
lemma hcq_lowRangeResidue_of_le_half {q : ℝ} (hq : q ≤ 1 / 2) : hcq_lowRangeResidue q :=
  fun _ hp => absurd (hp.1.trans hp.2) (not_lt.mpr hq)

example : cvg_smallDeltaResidue (1 / 2) :=
  hcq_smallDelta_of_lowRange (hcq_lowRangeResidue_of_le_half le_rfl)

example : mxd_martingaleHC_statement (1 / 2) :=
  hcq_martingaleHC_of_lowRange (hcq_lowRangeResidue_of_le_half le_rfl)

example : (0 : ℝ) ≤ (maxInfl (bernoulliWeight (3 / 4)) andInd) ^ ((1 / 2 : ℝ) / (2 - 1 / 2))
    * totalInfl (bernoulliWeight (3 / 4)) andInd :=
  hcq_lowRange_nonvacuous (by norm_num) (by norm_num) andFun (by norm_num) (by norm_num)

end StatMechTest.BooleanFunctions
