/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































import Code.Probability.BKKKLTruncation

open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false

namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
















theorem bkt2_capped_levelGe2_damped [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    4 * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card),
        (S.card : ℝ) * (((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ 4 * p * (1 - p)
        * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
          * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
  
  have hfull := lib_capped_optimal_weight hp0 hp1 φ hu0 hu1
  
  have h1u0 : (0 : ℝ) ≤ 1 - u := by linarith
  have hsub : (4 : ℝ) * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card),
        (S.card : ℝ) * (((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ 4 * ∑ S : Finset ι, (S.card : ℝ)
          * (((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1)
            * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro S _ _
    have : (0 : ℝ) ≤ ((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1) := by positivity
    positivity
  exact le_trans hsub hfull











theorem bkt2_damped_le_target {p u : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hu1 : u < 1)
    (d : ℕ) :
    ((1 - u) * (4 * p * (1 - p))) ^ (d - 1) ≤ (1 - u) ^ (d - 1) := by
  have h1u0 : (0 : ℝ) ≤ 1 - u := by linarith
  have hs0 : (0 : ℝ) ≤ 4 * p * (1 - p) := by nlinarith
  have hs1 : 4 * p * (1 - p) ≤ 1 := by nlinarith [sq_nonneg (1 - 2 * p)]
  apply pow_le_pow_left₀ (by positivity)
  nlinarith [hs1, h1u0]




theorem bkt2_target_eq_damped_of_p_half {u : ℝ} (d : ℕ) :
    (((1 - u) * (4 * (1/2 : ℝ) * (1 - 1/2))) ^ (d - 1)) = (1 - u) ^ (d - 1) := by
  norm_num

























def bkt2_levelGe2MasterResidue (q : ℝ) : Prop :=
  ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, p < 1 → ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (φ : ConfigSpace E → Bool),
      ∀ u : ℝ, 0 < u → u < 1 →
        ∃ k : ℕ, 1 ≤ k ∧
          4 * ∑ S ∈ univ.filter (fun S : Finset E => 2 ≤ S.card ∧ S.card ≤ k),
              (S.card : ℝ) * (1 - u) ^ (S.card - 1)
                * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
            ≤ (4 * (ptn_sigma p) ^ 2)
                * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
                    ^ (u / (2 - u))
                  - (1 - u) ^ k)
                * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
              - 4 * ∑ S ∈ univ.filter (fun S : Finset E => S.card = 1),
                  (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2









theorem bkt2_lowDegreeMaster_of_levelGe2 {q : ℝ} (H : bkt2_levelGe2MasterResidue q) :
    bkt_lowDegreeMasterResidue q := by
  intro p hp hp1 E _ _ _ φ u hu0 hu1
  obtain ⟨k, hk1, hk⟩ := H p hp hp1 φ u hu0 hu1
  refine ⟨k, ?_⟩
  
  set B : ℝ := (4 * (ptn_sigma p) ^ 2)
      * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
        - (1 - u) ^ k)
      * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) with hB
  
  exact (lib_residue_iff_levelGe2 φ hk1 (B := B)).mpr hk






theorem bkt2_master_of_levelGe2 {q : ℝ} (H : bkt2_levelGe2MasterResidue q) :
    pro_PBiasedMaster q :=
  bkt_master_of_residue (bkt2_lowDegreeMaster_of_levelGe2 H)

































def bkt2_RemainingGoal (q : ℝ) : Prop :=
  ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, p < 1 → ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (φ : ConfigSpace E → Bool),
      ∀ u : ℝ, 0 < u → u < 1 →
        ∃ k : ℕ, 1 ≤ k ∧
          
          4 * ∑ S ∈ univ.filter (fun S : Finset E => 2 ≤ S.card ∧ S.card ≤ k),
              (S.card : ℝ) * ((1 - u) ^ (S.card - 1)
                - ((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1))
                * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
            ≤ (4 * (ptn_sigma p) ^ 2)
                * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
                    ^ (u / (2 - u))
                  - (1 - u) ^ k)
                * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
              - 4 * ∑ S ∈ univ.filter (fun S : Finset E => S.card = 1),
                  (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
              - 4 * ∑ S ∈ univ.filter (fun S : Finset E => 2 ≤ S.card ∧ S.card ≤ k),
                  (S.card : ℝ) * (((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1)
                    * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)

omit [Fintype ι] [DecidableEq ι] in









theorem bkt2_levelGe2_of_remaining {q : ℝ} (H : bkt2_RemainingGoal q) :
    bkt2_levelGe2MasterResidue q := by
  intro p hp hp1 E _ _ _ φ u hu0 hu1
  obtain ⟨k, hk1, hgap⟩ := H p hp hp1 φ u hu0 hu1
  refine ⟨k, hk1, ?_⟩
  set c := fun S : Finset E => (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 with hc
  
  have hdecomp : 4 * ∑ S ∈ univ.filter (fun S : Finset E => 2 ≤ S.card ∧ S.card ≤ k),
        (S.card : ℝ) * (1 - u) ^ (S.card - 1) * c S
      = 4 * ∑ S ∈ univ.filter (fun S : Finset E => 2 ≤ S.card ∧ S.card ≤ k),
            (S.card : ℝ) * ((1 - u) ^ (S.card - 1)
              - ((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1)) * c S
        + 4 * ∑ S ∈ univ.filter (fun S : Finset E => 2 ≤ S.card ∧ S.card ≤ k),
            (S.card : ℝ) * (((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1) * c S) := by
    rw [← mul_add]; congr 1
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro S _; ring
  rw [show (4 : ℝ) * ∑ S ∈ univ.filter (fun S : Finset E => 2 ≤ S.card ∧ S.card ≤ k),
        (S.card : ℝ) * (1 - u) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      = 4 * ∑ S ∈ univ.filter (fun S : Finset E => 2 ≤ S.card ∧ S.card ≤ k),
          (S.card : ℝ) * (1 - u) ^ (S.card - 1) * c S from by rw [hc]]
  rw [hdecomp]
  
  rw [hc] at hgap ⊢
  linarith [hgap]





theorem bkt2_master_of_remaining {q : ℝ} (H : bkt2_RemainingGoal q) :
    pro_PBiasedMaster q :=
  bkt2_master_of_levelGe2 (bkt2_levelGe2_of_remaining H)






theorem bkt2_rhoOptimise_of_remaining {q : ℝ} (H : bkt2_RemainingGoal q) :
    ptn_RhoOptimise q :=
  pro_rhoOptimise_of_master (bkt2_master_of_remaining H)












theorem bkt2_truncDamped_le [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (k : ℕ) :
    4 * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
        (S.card : ℝ) * (((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ 4 * p * (1 - p)
        * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
          * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
  have h1u0 : (0 : ℝ) ≤ 1 - u := by linarith
  refine le_trans ?_ (bkt2_capped_levelGe2_damped hp0 hp1 φ hu0 hu1)
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro S hS; rw [Finset.mem_filter] at hS ⊢; exact ⟨hS.1, hS.2.1⟩
  · intro S _ _
    have h1 : (0 : ℝ) ≤ ((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1) := by positivity
    positivity





theorem bkt2_weightGap_nonneg {p u : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hu1 : u < 1) (d : ℕ) :
    0 ≤ (1 - u) ^ (d - 1) - ((1 - u) * (4 * p * (1 - p))) ^ (d - 1) := by
  have := bkt2_damped_le_target hp0 hp1 hu1 d
  linarith







theorem bkt2_remaining_c0 {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
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
              (S.card : ℝ) * (((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1) * (0 : ℝ) ^ 2) := by
  
  have h1u : (1 : ℝ) - u < 1 := by linarith
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (x := (maxInfl (OSSS.bernoulliWeight p)
      (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0))
      ^ (u / (2 - u))) hδ0 h1u
  refine ⟨k + 1, by omega, ?_⟩
  
  have hz1 : (4 : ℝ) * ∑ S ∈ univ.filter (fun S : Finset E => 2 ≤ S.card ∧ S.card ≤ k + 1),
      (S.card : ℝ) * ((1 - u) ^ (S.card - 1)
        - ((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1)) * (0 : ℝ) ^ 2 = 0 := by
    rw [Finset.sum_eq_zero (fun S _ => by ring), mul_zero]
  have hz2 : (4 : ℝ) * ∑ S ∈ univ.filter (fun S : Finset E => S.card = 1), (0 : ℝ) ^ 2 = 0 := by
    rw [Finset.sum_eq_zero (fun S _ => by ring), mul_zero]
  have hz3 : (4 : ℝ) * ∑ S ∈ univ.filter (fun S : Finset E => 2 ≤ S.card ∧ S.card ≤ k + 1),
      (S.card : ℝ) * (((1 - u) * (4 * p * (1 - p))) ^ (S.card - 1) * (0 : ℝ) ^ 2) = 0 := by
    rw [Finset.sum_eq_zero (fun S _ => by ring), mul_zero]
  rw [hz1, hz2, hz3, sub_zero, sub_zero]
  
  have hmono : (1 - u) ^ (k + 1) ≤ (1 - u) ^ k :=
    pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
  apply mul_nonneg
  · apply mul_nonneg (by positivity)
    linarith [hk, hmono]
  · exact kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) _

end StatMech.Probability
