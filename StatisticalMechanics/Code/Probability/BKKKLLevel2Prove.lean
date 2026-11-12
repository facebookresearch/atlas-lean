/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




























































































import Code.Probability.BKKKLMeanInfl

open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false

namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]














theorem bkt2p_undegree_le_var {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace ι → Bool)
    {u' : ℝ} (hu'0 : 0 ≤ u') (hu'1 : u' < 1) (k : ℕ) :
    ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
        (1 - u') ^ S.card * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
  set f := fun ω : ConfigSpace ι => if φ ω then (1 : ℝ) else 0 with hf
  set μ := OSSS.expect (OSSS.bernoulliWeight p) f with hμ
  have h1u'0 : (0 : ℝ) ≤ 1 - u' := by linarith
  have h1u'1 : (1 : ℝ) - u' ≤ 1 := by linarith
  
  have hvarF : μ * (1 - μ) = ∑ S ∈ (univ.erase (∅ : Finset ι)), (ptn_coeff p f S) ^ 2 := by
    rw [← ptn_var_eq_fourierWeight hp0 hp1 f, mil_var_eq φ, ← hμ]; ring
  rw [hvarF]
  calc ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
          (1 - u') ^ S.card * (ptn_coeff p f S) ^ 2
      ≤ ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
          (ptn_coeff p f S) ^ 2 := by
        apply Finset.sum_le_sum
        intro S _
        have hpow : (1 - u') ^ S.card ≤ 1 := pow_le_one₀ h1u'0 h1u'1
        nlinarith [hpow, sq_nonneg (ptn_coeff p f S), pow_nonneg h1u'0 S.card]
    _ ≤ ∑ S ∈ (univ.erase (∅ : Finset ι)), (ptn_coeff p f S) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro S hS
          rw [Finset.mem_filter] at hS
          rw [Finset.mem_erase]
          refine ⟨?_, Finset.mem_univ S⟩
          intro he; rw [he, Finset.card_empty] at hS; omega
        · intro S _ _; positivity














theorem bkt2p_levelGe2_le_var {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace ι → Bool)
    {u u' : ℝ} (hu1 : u < 1) (hu'0 : 0 ≤ u') (hlt : u' < u) (k : ℕ) :
    4 * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
        (S.card : ℝ) * (1 - u) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ (4 / (u - u'))
        * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
            * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))) := by
  have hu'1 : u' < 1 := by linarith
  have hdpos : 0 < u - u' := by linarith
  
  have hlever := bkt2f_degreeWeight_le_undegree (p := p) hu1 hlt φ k
  
  have hvar := bkt2p_undegree_le_var hp0 hp1 φ hu'0 hu'1 k
  
  calc 4 * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
          (S.card : ℝ) * (1 - u) ^ (S.card - 1)
            * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ 4 * ((1 / (u - u')) * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
          (1 - u') ^ S.card * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) :=
        mul_le_mul_of_nonneg_left hlever (by norm_num)
    _ ≤ 4 * ((1 / (u - u'))
          * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
              * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply mul_le_mul_of_nonneg_left hvar
        positivity
    _ = (4 / (u - u'))
          * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
              * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))) := by
        ring
























def bkt2p_VarGapCore (q : ℝ) : Prop :=
  ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, p < 1 → ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (φ : ConfigSpace E → Bool),
      ∀ u : ℝ, 0 < u → u < 1 →
        ∃ u' : ℝ, 0 < u' ∧ u' < u ∧ ∃ k : ℕ, 1 ≤ k ∧
          (4 / (u - u'))
            * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
                * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)))
            ≤ (4 * (ptn_sigma p) ^ 2)
                * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
                    ^ (u / (2 - u))
                  - (1 - u) ^ k)
                * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
              - 4 * ∑ S ∈ univ.filter (fun S : Finset E => S.card = 1),
                  (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2











theorem bkt2p_levelGe2_of_varGap {q : ℝ} (H : bkt2p_VarGapCore q) :
    bkt2_levelGe2MasterResidue q := by
  intro p hp hp1 E _ _ _ φ u hu0 hu1
  have hp0 : 0 < p := by have := hp.1; linarith
  obtain ⟨u', hu'0, hlt, k, hk1, hbudget⟩ := H p hp hp1 φ u hu0 hu1
  refine ⟨k, hk1, ?_⟩
  
  have hsharp := bkt2p_levelGe2_le_var hp0 hp1 φ hu1 hu'0.le hlt k
  
  exact le_trans hsharp hbudget






theorem bkt2p_remaining_of_varGap {q : ℝ} (H : bkt2p_VarGapCore q) :
    bkt2_RemainingGoal q :=
  bkt2c_remaining_of_levelGe2 (bkt2p_levelGe2_of_varGap H)







theorem bkt2p_master_of_varGap {q : ℝ} (H : bkt2p_VarGapCore q) :
    pro_PBiasedMaster q :=
  bkt2_master_of_levelGe2 (bkt2p_levelGe2_of_varGap H)







theorem bkt2p_rhoOptimise_of_varGap {q : ℝ} (H : bkt2p_VarGapCore q) :
    ptn_RhoOptimise q :=
  bkt2_rhoOptimise_of_remaining (bkt2p_remaining_of_varGap H)












theorem bkt2p_varGapCore_c0 {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hδ0 : 0 < (maxInfl (OSSS.bernoulliWeight p)
        (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0))
        ^ (u / (2 - u))) :
    ∃ u' : ℝ, 0 < u' ∧ u' < u ∧ ∃ k : ℕ, 1 ≤ k ∧
      (4 / (u - u'))
        * (OSSS.expect (OSSS.bernoulliWeight p)
              (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0)
            * (1 - OSSS.expect (OSSS.bernoulliWeight p)
                (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0)))
        ≤ (4 * (ptn_sigma p) ^ 2)
            * ((maxInfl (OSSS.bernoulliWeight p)
                (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0))
                ^ (u / (2 - u))
              - (1 - u) ^ k)
            * totalInfl (OSSS.bernoulliWeight p)
                (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0)
          - 4 * ∑ S ∈ univ.filter (fun S : Finset E => S.card = 1),
              (ptn_coeff p (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0) S) ^ 2 := by
  set f0 : ConfigSpace E → Bool := fun _ => false with hf0
  
  refine ⟨u / 2, by linarith, by linarith, ?_⟩
  
  have h1u : (1 : ℝ) - u < 1 := by linarith
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (x := (maxInfl (OSSS.bernoulliWeight p)
      (fun ω => if f0 ω then (1 : ℝ) else 0)) ^ (u / (2 - u))) hδ0 h1u
  refine ⟨k + 1, by omega, ?_⟩
  
  have hf0zero : (fun ω => if f0 ω then (1 : ℝ) else 0) = (fun _ : ConfigSpace E => (0 : ℝ)) := by
    funext ω; rw [hf0]; simp
  have hμ0 : OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if f0 ω then (1 : ℝ) else 0) = 0 := by
    rw [hf0zero]; unfold OSSS.expect; simp
  rw [hμ0]
  simp only [zero_mul, mul_zero, sub_zero]
  
  have hcoeff0 : ∀ S : Finset E, ptn_coeff p (fun ω => if f0 ω then (1 : ℝ) else 0) S = 0 := by
    intro S; rw [hf0zero]; unfold ptn_coeff OSSS.expect; simp
  have hz1 : (4 : ℝ) * ∑ S ∈ univ.filter (fun S : Finset E => S.card = 1),
      (ptn_coeff p (fun ω => if f0 ω then (1 : ℝ) else 0) S) ^ 2 = 0 := by
    rw [Finset.sum_eq_zero (fun S _ => by rw [hcoeff0]; ring), mul_zero]
  rw [hz1, sub_zero]
  
  have hmono : (1 - u) ^ (k + 1) ≤ (1 - u) ^ k :=
    pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
  apply mul_nonneg
  · apply mul_nonneg (by positivity)
    linarith [hk, hmono]
  · exact kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) _







theorem bkt2p_levelGe2_le_var_and_mil {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace ι → Bool)
    {u u' : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hu'0 : 0 ≤ u') (hlt : u' < u) (k : ℕ) :
    (4 * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
        (S.card : ℝ) * (1 - u) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ (4 / (u - u'))
        * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
            * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))))
    ∧ (4 * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
        (S.card : ℝ) * (1 - u) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ 4 * (k : ℝ)
        * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
            * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)))) :=
  ⟨bkt2p_levelGe2_le_var hp0 hp1 φ hu1 hu'0 hlt k,
    mil_levelGe2_le_var hp0 hp1 φ hu0 hu1 k⟩









theorem bkt2p_poincare_half {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace ι → Bool) :
    OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
      * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ (ptn_sigma p) ^ 2
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  mil_poincare hp0 hp1 φ






theorem bkt2p_gap_vanishes_at_p_half {u : ℝ} (d : ℕ) :
    (1 - u) ^ (d - 1) - (((1 - u) * (4 * (1/2 : ℝ) * (1 - 1/2))) ^ (d - 1)) = 0 := by
  rw [bkt2_target_eq_damped_of_p_half d]; ring

end StatMech.Probability
