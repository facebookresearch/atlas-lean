/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.FSMartingale
public import CSLibExtTest.Complexity.BooleanFunctions.KKL.FSPerEdge

/-!
# Tests for the damped per-coordinate weights

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.FSMartingale` at the `AND` function on
`{0, 1}^Bool`:

* `fsm2_dampWeight p 0 AND e = p²` for every `p ∈ (0, 1)`;
* `fsm2_dampWeight_le_hc` at `q = 1`, `ρ = 0` is the equality `p² ≤ p²`;
* `fsm2_logGain_capped` instantiated at `p = 3/4`, `q = 2`, `ρ = √3/2`, with its positivity
  hypotheses discharged from the explicit influences;
* `fsm2_residue_statement q` is proved here for no `q > 1/2`; it holds for `q ≤ 1/2` because
  `(1/2, q)` is empty, and `fsm2_rhoOptimise_of_residue` transfers it to `ptn_RhoOptimise`.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.Probability

lemma fsm2_dampWeight_zero_andFun {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (e : Bool) :
    fsm2_dampWeight p 0 andFun e = p ^ 2 := by
  have : 0 < 1 - p := by linarith
  cases e <;>
  · rw [fsm2_dampWeight, Finset.sum_filter, sum_finset_bool]
    simp only [div_pow, ptn_sigma_sq hp0 hp1]
    rw [ptn_coeff_andInd_true_sq hp0 hp1, ptn_coeff_andInd_false_sq hp0 hp1,
      ptn_coeff_andInd_univ_sq hp0 hp1]
    simp
    field_simp

/-- `fsm2_dampWeight_le_hc` at `q = 1`, `ρ = 0` holds with equality. -/
example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : p ^ 2 ≤ p ^ (2 / (1 : ℝ)) := by
  have h := fsm2_dampWeight_le_hc hp0 hp1 le_rfl zero_le_one le_rfl one_le_two
    (by ring) andFun true
  rwa [fsm2_dampWeight_zero_andFun hp0 hp1, infl_andInd] at h

example {p : ℝ} : p ^ (2 / (1 : ℝ)) = p ^ 2 := by norm_num

example :
    totalInfl (bernoulliWeight (3 / 4)) andInd * (2 / 2 - 1)
        * Real.log (1 / maxInfl (bernoulliWeight (3 / 4)) andInd)
      ≤ ∑ e ∈ Finset.univ.filter (fun e : Bool => 0 < infl (bernoulliWeight (3 / 4)) andInd e),
        infl (bernoulliWeight (3 / 4)) andInd e
          * Real.log (infl (bernoulliWeight (3 / 4)) andInd e
              / fsm2_dampWeight (3 / 4) (Real.sqrt 3 / 2) andFun e) :=
  fsm2_logGain_capped (by norm_num) (by norm_num) (by positivity) rho_le_one (by norm_num) le_rfl
    rho_sq andFun (by rw [totalInfl_andInd_p]; norm_num) (by rw [maxInfl_andInd_p]; norm_num)
    (by rw [maxInfl_andInd_p]; norm_num)

/-- `fsm2_residue_statement q` for `q ≤ 1/2` holds vacuously. -/
lemma fsm2_residue_of_le_half {q : ℝ} (hq : q ≤ 1 / 2) : fsm2_residue_statement q :=
  fun _ hp => absurd (hp.1.trans hp.2) (not_lt.mpr hq)

example : ptn_RhoOptimise (1 / 2) := fsm2_rhoOptimise_of_residue (fsm2_residue_of_le_half le_rfl)

end StatMechTest.BooleanFunctions
