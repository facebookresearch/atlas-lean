/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































import Code.Probability.BKKKLLevel2

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








theorem bkt2c_remaining_c0 {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hδ0 : 0 < (maxInfl (OSSS.bernoulliWeight p)
        (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0))
        ^ (u / (2 - u))) :
    ∃ k : ℕ, 1 ≤ k ∧
      4 * ∑ S ∈ univ.filter (fun S : Finset E => 2 ≤ S.card ∧ S.card ≤ k),
          (S.card : ℝ) * ((1 - u) ^ (S.card - 1)
            - ((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1)) * (0 : ℝ) ^ 2
        ≤ (4 * (ptn_sigma p) ^ 2)
            * ((maxInfl (OSSS.bernoulliWeight p)
                (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0))
                ^ (u / (2 - u))
              - (1 - u) ^ k)
            * totalInfl (OSSS.bernoulliWeight p)
                (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0)
          - 4 * ∑ _S ∈ univ.filter (fun S : Finset E => S.card = 1), (0 : ℝ) ^ 2
          - 4 * ∑ S ∈ univ.filter (fun S : Finset E => 2 ≤ S.card ∧ S.card ≤ k),
              (S.card : ℝ) * (((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1) * (0 : ℝ) ^ 2) :=
  bkt2_remaining_c0 hp0 hp1 hu0 hu1 hδ0







theorem bkt2c_gap_vanishes_at_p_half {u : ℝ} (d : ℕ) :
    (1 - u) ^ (d - 1) - (((1 - u) * (4 * (1/2 : ℝ) * (1 - 1/2))) ^ (d - 1)) = 0 := by
  rw [bkt2_target_eq_damped_of_p_half d]; ring






theorem bkt2c_weightGap_nonneg {p u : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hu1 : u < 1) (d : ℕ) :
    0 ≤ (1 - u) ^ (d - 1) - ((1 - u) * (4 * p * (1 - p))) ^ (d - 1) :=
  bkt2_weightGap_nonneg hp0 hp1 hu1 d

end StatMech.Probability
