/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.BKKKLLevel2
public import CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.CoupledTensorizeRefutations
public import CSLibExt.Complexity.BooleanFunctions.KKL.VarGapDictator

/-!
# Tests for the level-at-least-two master estimates

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.BKKKLLevel2`:

* `bkt2_damped_le_target` and `bkt2_weightGap_nonneg` at `p = 3/4`, `u = 1/2`, `d = 3`,
  `bkt2_target_eq_damped_of_p_half`, and `bkt2_capped_levelGe2_damped` /
  `bkt2_truncDamped_le` on the one-variable dictator, where the level-`≥ 2` sum is empty;
* the conditional chain `bkt2_levelGe2_of_remaining`, `bkt2_master_of_levelGe2`,
  `bkt2_master_of_remaining`, `bkt2_rhoOptimise_of_remaining` on the only instance available,
  the empty window `q = 1/2`.

Window predicates: the library refutes `bkt2_levelGe2MasterResidue q` and
`bkt2_RemainingGoal q` for `q > 3/4` (`ctc_levelGe2_false`, `ctc_remainingGoal_false`),
tested here at `q = 1`, and for every `q > 1/2` (`ctc_levelGe2_false_of_half_lt`,
`ctc_remainingGoal_false_of_half_lt`), tested at `q = 3/4` and `q = 3/5`: for the one-variable
dictator the level-`≥ 2` sum is `0`, while the right-hand side is `-4σ_p²(1-u)^k < 0`. So every
theorem in this module that assumes one of the two predicates on a window with `q > 1/2` is
vacuous.

The maximal influence of the constant-false indicator is `0`, so
`0 < maxInfl ν 0 ^ (u / (2 - u))` never holds; this is checked below.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions.BKKKLLevel2

open Finset StatMech StatMech.OSSS StatMech.Probability

example : ¬ bkt2_levelGe2MasterResidue 1 := ctc_levelGe2_false (by norm_num)
example : ¬ bkt2_RemainingGoal 1 := ctc_remainingGoal_false (by norm_num)
example : ¬ bkt2_levelGe2MasterResidue (3 / 4) := ctc_levelGe2_false_of_half_lt (by norm_num)
example : ¬ bkt2_RemainingGoal (3 / 5) := ctc_remainingGoal_false_of_half_lt (by norm_num)

/-- `bkt2_RemainingGoal q` holds vacuously for `q ≤ 1/2`. -/
lemma remainingGoal_of_le_half {q : ℝ} (hq : q ≤ 1 / 2) : bkt2_RemainingGoal q :=
  fun _ hp => absurd (hp.1.trans hp.2) (not_lt.mpr hq)

example : bkt2_levelGe2MasterResidue (1 / 2) :=
  bkt2_levelGe2_of_remaining (remainingGoal_of_le_half le_rfl)
example : pro_PBiasedMaster (1 / 2) :=
  bkt2_master_of_levelGe2 (bkt2_levelGe2_of_remaining (remainingGoal_of_le_half le_rfl))
example : pro_PBiasedMaster (1 / 2) := bkt2_master_of_remaining (remainingGoal_of_le_half le_rfl)
example : ptn_RhoOptimise (1 / 2) := bkt2_rhoOptimise_of_remaining (remainingGoal_of_le_half le_rfl)

example : ((1 - 1 / 2) * (4 * (3 / 4 : ℝ) * (1 - 3 / 4))) ^ (3 - 1) ≤ (1 - 1 / 2) ^ (3 - 1) :=
  bkt2_damped_le_target (by norm_num) (by norm_num) (by norm_num) 3

example : ((1 - 1 / 2) * (4 * (3 / 4 : ℝ) * (1 - 3 / 4))) ^ (3 - 1) = 9 / 64 := by norm_num

example : (0 : ℝ) ≤ (1 - 1 / 2) ^ (3 - 1) - ((1 - 1 / 2) * (4 * (3 / 4) * (1 - 3 / 4))) ^ (3 - 1) :=
  bkt2_weightGap_nonneg (by norm_num) (by norm_num) (by norm_num) 3

example : ((1 - 1 / 3) * (4 * (1 / 2 : ℝ) * (1 - 1 / 2))) ^ (4 - 1) = (1 - 1 / 3) ^ (4 - 1) :=
  bkt2_target_eq_damped_of_p_half 4

/-- `bkt2_capped_levelGe2_damped` on the dictator: the left side is the empty sum. -/
example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    4 * ∑ S ∈ univ.filter (fun S : Finset (Fin 1) => 2 ≤ S.card),
        (S.card : ℝ) * (((1 - 1 / 2) * (4 * p * (1 - p))) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if (fun ω : ConfigSpace (Fin 1) => ω 0) ω then (1 : ℝ) else 0)
            S) ^ 2)
      ≤ 4 * p * (1 - p) := by
  have h := bkt2_capped_levelGe2_damped hp0 hp1 (fun ω : ConfigSpace (Fin 1) => ω 0)
    (u := 1 / 2) (by norm_num) (by norm_num)
  rw [vgp_dictator_maxInfl hp0 hp1, Real.one_rpow, vgp_dictator_totalInfl hp0 hp1] at h
  simpa using h

example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace (Fin 2) → Bool) :
    4 * ∑ S ∈ univ.filter (fun S : Finset (Fin 2) => 2 ≤ S.card ∧ S.card ≤ 2),
        (S.card : ℝ) * (((1 - 1 / 2) * (4 * p * (1 - p))) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ 4 * p * (1 - p)
        * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
            ^ ((1 / 2 : ℝ) / (2 - 1 / 2))
          * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) :=
  bkt2_truncDamped_le hp0 hp1 φ (by norm_num) (by norm_num) 2

/-- The constant-false indicator has maximal influence `0`. -/
lemma maxInfl_constFalse {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (p : ℝ) :
    maxInfl (OSSS.bernoulliWeight p)
      (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0) = 0 := by
  unfold maxInfl OSSS.infl OSSS.expect
  simp

/-- `0 < maxInfl ν 0 ^ (u / (2 - u))` never holds for the constant-false indicator. -/
example {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] {p u : ℝ} (hu0 : 0 < u)
    (hu1 : u < 1) :
    ¬ 0 < (maxInfl (OSSS.bernoulliWeight p)
      (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0))
        ^ (u / (2 - u)) := by
  rw [maxInfl_constFalse, Real.zero_rpow (div_pos hu0 (by linarith)).ne']
  exact lt_irrefl 0

end StatMechTest.BooleanFunctions.BKKKLLevel2
