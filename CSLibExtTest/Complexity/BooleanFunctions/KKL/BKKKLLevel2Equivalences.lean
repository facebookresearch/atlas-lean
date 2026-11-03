/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.BKKKLLevel2Equivalences
public import CSLibExtTest.Complexity.BooleanFunctions.KKL.BKKKLLevel2

/-!
# Tests for the level-two equivalences

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.BKKKLLevel2Equivalences`:

* `ctc_remainingGoal_false_of_half_lt`: `bkt2_RemainingGoal q` fails for every `q > 1/2`;
* `bkt2c_weightGap_eq_target_sub_damped` on the one-variable dictator (both sides are empty
  sums) and on a general two-variable function, `bkt2c_gap_vanishes_at_p_half`,
  `bkt2_weightGap_nonneg` and `bkt2c_truncDamped_capped` at concrete parameters.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions.BKKKLLevel2Equivalences

open Finset StatMech StatMech.OSSS StatMech.Probability
open StatMechTest.BooleanFunctions.BKKKLLevel2 (maxInfl_constFalse)

/-- `bkt2_RemainingGoal q` fails for every `q > 1/2`. -/
example {q : ℝ} (hq : 1 / 2 < q) : ¬ bkt2_RemainingGoal q :=
  ctc_remainingGoal_false_of_half_lt hq

/-- `bkt2c_weightGap_eq_target_sub_damped` with cutoff `k = 1`: all three sums are empty. -/
example {p u : ℝ} (φ : ConfigSpace (Fin 2) → Bool) :
    4 * ∑ S ∈ univ.filter (fun S : Finset (Fin 2) => 2 ≤ S.card ∧ S.card ≤ 1),
        (S.card : ℝ) * ((1 - u) ^ (S.card - 1)
          - ((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1))
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 = 0 := by
  rw [bkt2c_weightGap_eq_target_sub_damped φ 1]
  have hempty : univ.filter (fun S : Finset (Fin 2) => 2 ≤ S.card ∧ S.card ≤ 1) = ∅ := by
    ext S; simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]; omega
  simp [hempty]

example {p u : ℝ} (φ : ConfigSpace (Fin 2) → Bool) :
    4 * ∑ S ∈ univ.filter (fun S : Finset (Fin 2) => 2 ≤ S.card ∧ S.card ≤ 2),
        (S.card : ℝ) * ((1 - u) ^ (S.card - 1)
          - ((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1))
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      = (4 * ∑ S ∈ univ.filter (fun S : Finset (Fin 2) => 2 ≤ S.card ∧ S.card ≤ 2),
            (S.card : ℝ) * (1 - u) ^ (S.card - 1)
              * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
        - 4 * ∑ S ∈ univ.filter (fun S : Finset (Fin 2) => 2 ≤ S.card ∧ S.card ≤ 2),
            (S.card : ℝ) * (((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1)
              * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) :=
  bkt2c_weightGap_eq_target_sub_damped φ 2

example : (1 - (1 / 3 : ℝ)) ^ (5 - 1) - ((1 - 1 / 3) * (4 * (1 / 2 : ℝ) * (1 - 1 / 2))) ^ (5 - 1)
    = 0 :=
  bkt2c_gap_vanishes_at_p_half 5

/-- `bkt2_weightGap_nonneg` at `p = 9/10`, `u = 0`, `d = 2`: `0 ≤ 1 - 9/25`. -/
example : (0 : ℝ) ≤ 1 - 9 / 25 := by
  have h := bkt2_weightGap_nonneg (p := 9 / 10) (u := 0) (by norm_num) (by norm_num)
    (by norm_num) 2
  norm_num at h ⊢

example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace (Fin 2) → Bool) :
    4 * ∑ S ∈ univ.filter (fun S : Finset (Fin 2) => 2 ≤ S.card ∧ S.card ≤ 2),
        (S.card : ℝ) * (((1 - 1 / 2) * (4 * p * (1 - p))) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ 4 * p * (1 - p)
        * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
            ^ ((1 / 2 : ℝ) / (2 - 1 / 2))
          * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) :=
  bkt2c_truncDamped_capped hp0 hp1 φ (by norm_num) (by norm_num) 2

end StatMechTest.BooleanFunctions.BKKKLLevel2Equivalences
