/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.BKKKLLevel2

@[expose] public section

/-!
# Closing the level-two estimates: truncation, equivalence, endpoint

Capped truncated damping, the equivalence between the remaining goal and the level-≥2
residue (`bkt2c_remaining_iff_levelGe2`), the gap vanishing at `p = 1/2`, and the
conditional implications from either residue to the master estimate and rho-optimisation.

## Main results

* `bkt2c_remaining_iff_levelGe2`: the remaining goal iff the level-≥2 residue.
* `bkt2c_remaining_of_levelGe2`, `bkt2c_levelGe2_of_remaining`,
  `bkt2c_master_of_remaining`, `bkt2c_rhoOptimise_of_remaining`: the conditional chains.
* `bkt2c_gap_vanishes_at_p_half`: the weight gap vanishes at `p = 1/2`.
-/

open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false

namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem bkt2c_truncDamped_capped [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (k : ℕ) :
    4 * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
        (S.card : ℝ) * (((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ 4 * p * (1 - p)
        * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
          * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) :=
  bkt2_truncDamped_le hp0 hp1 φ hu0 hu1 k

theorem bkt2c_weightGap_eq_target_sub_damped {p u : ℝ} (φ : ConfigSpace ι → Bool) (k : ℕ) :
    4 * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
        (S.card : ℝ) * ((1 - u) ^ (S.card - 1)
          - ((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1))
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      = (4 * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
            (S.card : ℝ) * (1 - u) ^ (S.card - 1)
              * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
        - 4 * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
            (S.card : ℝ) * (((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1)
              * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) := by
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro S _
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem bkt2c_remaining_of_levelGe2 {q : ℝ} (H : bkt2_levelGe2MasterResidue q) :
    bkt2_RemainingGoal q := by
  intro p hp hp1 E _ _ _ φ u hu0 hu1
  obtain ⟨k, hk1, hk⟩ := H p hp hp1 φ u hu0 hu1
  refine ⟨k, hk1, ?_⟩
  have hgap := bkt2c_weightGap_eq_target_sub_damped (p := p) (u := u) φ k
  rw [hgap]
  linarith [hk]

omit [Fintype ι] [DecidableEq ι] in
/-- The remaining goal holds iff the level-≥2 residue holds. -/
theorem bkt2c_remaining_iff_levelGe2 {q : ℝ} :
    bkt2_RemainingGoal q ↔ bkt2_levelGe2MasterResidue q :=
  ⟨bkt2_levelGe2_of_remaining, bkt2c_remaining_of_levelGe2⟩

theorem bkt2c_levelGe2_of_remaining {q : ℝ} (H : bkt2_RemainingGoal q) :
    bkt2_levelGe2MasterResidue q :=
  bkt2_levelGe2_of_remaining H

theorem bkt2c_master_of_remaining {q : ℝ} (H : bkt2_RemainingGoal q) :
    pro_PBiasedMaster q :=
  bkt2_master_of_remaining H

theorem bkt2c_rhoOptimise_of_remaining {q : ℝ} (H : bkt2_RemainingGoal q) :
    ptn_RhoOptimise q :=
  bkt2_rhoOptimise_of_remaining H

theorem bkt2c_gap_vanishes_at_p_half {u : ℝ} (d : ℕ) :
    (1 - u) ^ (d - 1) - (((1 - u) * (4 * (1/2 : ℝ) * (1 - 1/2))) ^ (d - 1)) = 0 := by
  rw [bkt2_target_eq_damped_of_p_half d]; ring

end StatMech.Probability
