/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































import Code.Probability.BKKKLLevel2Final

open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false

namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]





theorem mil_mean_le_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (φ : ConfigSpace ι → Bool) :
    OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) ≤ 1 := by
  have hprob := OSSS.bernoulliWeight_isProbWeight (E := ι) hp0 hp1
  calc OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
      ≤ OSSS.expect (OSSS.bernoulliWeight p) (fun _ => (1 : ℝ)) := by
        apply OSSS.expect_mono hprob
        intro ω; by_cases h : φ ω <;> simp [h]
    _ = 1 := OSSS.expect_one hprob


theorem mil_mean_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (φ : ConfigSpace ι → Bool) :
    0 ≤ OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  unfold OSSS.expect
  exact Finset.sum_nonneg fun ω _ => mul_nonneg
    (Finset.prod_nonneg fun e _ => (OSSS.bernoulliWeight_isProbWeight hp0 hp1).nonneg e (ω e))
    (by positivity)

omit [Fintype ι] [DecidableEq ι] in

theorem mil_indicator_sq (φ : ConfigSpace ι → Bool) (ω : ConfigSpace ι) :
    ((fun ω => if φ ω then (1 : ℝ) else 0) ω) ^ 2 = (fun ω => if φ ω then (1 : ℝ) else 0) ω := by
  by_cases h : φ ω <;> simp [h]


theorem mil_meanSq_eq_mean {p : ℝ} (φ : ConfigSpace ι → Bool) :
    OSSS.expect (OSSS.bernoulliWeight p) (fun ω => ((fun ω => if φ ω then (1 : ℝ) else 0) ω) ^ 2)
      = OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  unfold OSSS.expect
  apply Finset.sum_congr rfl
  intro ω _
  simp only [mil_indicator_sq φ ω]






theorem mil_var_eq {p : ℝ} (φ : ConfigSpace ι → Bool) :
    OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
      = (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
        - (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ 2 := by
  set f := fun ω : ConfigSpace ι => if φ ω then (1 : ℝ) else 0 with hf
  unfold OSSS.var OSSS.cov
  rw [show (fun ω : ConfigSpace ι => f ω * f ω) = (fun ω => (f ω) ^ 2) from by funext ω; ring]
  rw [mil_meanSq_eq_mean φ, sq]




theorem mil_fourierMass_le_degreeWeight (φ : ConfigSpace ι → Bool) {p : ℝ} :
    ∑ S ∈ (univ.erase (∅ : Finset ι)),
        (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ ∑ S : Finset ι, (S.card : ℝ)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
  set c := fun S : Finset ι => (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 with hc
  calc ∑ S ∈ (univ.erase (∅ : Finset ι)), c S
      ≤ ∑ S ∈ (univ.erase (∅ : Finset ι)), (S.card : ℝ) * c S := by
        apply Finset.sum_le_sum
        intro S hS
        rw [Finset.mem_erase] at hS
        have hScard : 1 ≤ S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS.1)
        have h1le : (1 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hScard
        nlinarith [h1le, sq_nonneg (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S)]
    _ ≤ ∑ S : Finset ι, (S.card : ℝ) * c S := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        intro S _ _; rw [hc]; positivity










theorem mil_poincare {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace ι → Bool) :
    (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
      * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ (ptn_sigma p) ^ 2
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  set f := fun ω : ConfigSpace ι => if φ ω then (1 : ℝ) else 0 with hf
  set μ := OSSS.expect (OSSS.bernoulliWeight p) f with hμ
  have hσ2 : (ptn_sigma p) ^ 2 = p * (1 - p) := ptn_sigma_sq hp0 hp1
  have hσ2pos : 0 < (ptn_sigma p) ^ 2 := by rw [hσ2]; nlinarith
  have hvar : OSSS.var (OSSS.bernoulliWeight p) f = μ * (1 - μ) := by
    rw [mil_var_eq φ, ← hμ]; ring
  have hvarF := ptn_var_eq_fourierWeight hp0 hp1 f
  have hTF := ptn_totalInfl_eq_fourierWeight hp0 hp1 φ
  rw [← hvar, hvarF]
  have hdom := mil_fourierMass_le_degreeWeight (p := p) φ
  have hσT : (ptn_sigma p) ^ 2 * totalInfl (OSSS.bernoulliWeight p) f
      = ∑ S : Finset ι, (S.card : ℝ) * (ptn_coeff p f S) ^ 2 := by
    rw [hTF, ← mul_assoc, mul_one_div, div_self (ne_of_gt hσ2pos), one_mul]
  rw [hσT]
  exact hdom













theorem mil_level1_le_var {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace ι → Bool) :
    ∑ S ∈ univ.filter (fun S : Finset ι => S.card = 1),
        (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
  set f := fun ω : ConfigSpace ι => if φ ω then (1 : ℝ) else 0 with hf
  have hvar : OSSS.var (OSSS.bernoulliWeight p) f
      = OSSS.expect (OSSS.bernoulliWeight p) f * (1 - OSSS.expect (OSSS.bernoulliWeight p) f) := by
    rw [mil_var_eq φ]; ring
  rw [← hvar, ptn_var_eq_fourierWeight hp0 hp1 f]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro S hS
    rw [Finset.mem_filter] at hS
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ S⟩
    intro hempty; rw [hempty, Finset.card_empty] at hS; exact absurd hS.2 (by norm_num)
  · intro S _ _; positivity









theorem mil_levelGe2_le_var {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace ι → Bool)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (k : ℕ) :
    4 * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
        (S.card : ℝ) * (1 - u) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ 4 * (k : ℝ)
        * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
            * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))) := by
  set f := fun ω : ConfigSpace ι => if φ ω then (1 : ℝ) else 0 with hf
  set μ := OSSS.expect (OSSS.bernoulliWeight p) f with hμ
  have h1u0 : (0:ℝ) ≤ 1 - u := by linarith
  have h1u1 : (1:ℝ) - u ≤ 1 := by linarith
  have hvarF : μ * (1 - μ) = ∑ S ∈ (univ.erase (∅ : Finset ι)), (ptn_coeff p f S) ^ 2 := by
    rw [← ptn_var_eq_fourierWeight hp0 hp1 f, mil_var_eq φ, ← hμ]; ring
  have hstep1 : ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
        (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p f S) ^ 2
      ≤ (k : ℝ) * (μ * (1 - μ)) := by
    rw [hvarF, Finset.mul_sum]
    calc ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
          (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p f S) ^ 2
        ≤ ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
            (k : ℝ) * (ptn_coeff p f S) ^ 2 := by
          apply Finset.sum_le_sum
          intro S hS
          rw [Finset.mem_filter] at hS
          have hSk : (S.card : ℝ) ≤ (k : ℝ) := by exact_mod_cast hS.2.2
          have hpow : (1 - u) ^ (S.card - 1) ≤ 1 := pow_le_one₀ h1u0 h1u1
          have hsq : (0:ℝ) ≤ (ptn_coeff p f S) ^ 2 := sq_nonneg _
          have hcardnn : (0:ℝ) ≤ (S.card : ℝ) := by positivity
          nlinarith [hSk, hpow, hsq, hcardnn, mul_nonneg hcardnn hsq]
      _ ≤ ∑ S ∈ (univ.erase (∅ : Finset ι)), (k : ℝ) * (ptn_coeff p f S) ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro S hS
            rw [Finset.mem_filter] at hS
            rw [Finset.mem_erase]
            refine ⟨?_, Finset.mem_univ S⟩
            intro he; rw [he, Finset.card_empty] at hS; omega
          · intro S _ _; positivity
  calc 4 * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
          (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p f S) ^ 2
      ≤ 4 * ((k : ℝ) * (μ * (1 - μ))) := mul_le_mul_of_nonneg_left hstep1 (by norm_num)
    _ = 4 * (k:ℝ) * (μ * (1 - μ)) := by ring







omit [Fintype ι] [DecidableEq ι] in

theorem mil_constTrue_eq :
    (fun ω => if (fun _ => true : ConfigSpace ι → Bool) ω then (1 : ℝ) else 0)
      = (fun _ : ConfigSpace ι => (1 : ℝ)) := by funext ω; simp



theorem mil_constTrue_totalInfl {p : ℝ} :
    totalInfl (OSSS.bernoulliWeight p)
      (fun ω => if (fun _ => true : ConfigSpace ι → Bool) ω then (1 : ℝ) else 0) = 0 := by
  unfold totalInfl
  apply Finset.sum_eq_zero
  intro e _
  unfold OSSS.infl
  rw [mil_constTrue_eq]; simp only [sub_self, abs_zero]; unfold OSSS.expect; simp



theorem mil_constTrue_coeff {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (S : Finset ι) :
    ptn_coeff p (fun ω => if (fun _ => true : ConfigSpace ι → Bool) ω then (1 : ℝ) else 0) S
      = if S = ∅ then 1 else 0 := by
  rw [mil_constTrue_eq]
  unfold ptn_coeff
  have heq : (fun ω : ConfigSpace ι => (1 : ℝ) * ptn_pchar p S ω)
      = (fun ω => ptn_pchar p (∅ : Finset ι) ω * ptn_pchar p S ω) := by
    funext ω; simp [ptn_pchar_empty]
  rw [heq, ptn_orthonormal hp0 hp1]
  by_cases h : (∅ : Finset ι) = S
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hh => h hh.symm)]


theorem mil_constTrue_qnorm {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {q : ℝ} (hq : 0 < q) :
    (ptn_qnorm p q
        (fun ω => if (fun _ => true : ConfigSpace ι → Bool) ω then (1 : ℝ) else 0)) ^ 2 = 1 := by
  rw [bkt2f_qnorm_indicator_sq hp0 hp1 hq, mil_constTrue_eq,
    OSSS.expect_one (OSSS.bernoulliWeight_isProbWeight hp0 hp1), Real.one_rpow]









theorem bkt2f_meanInflResidue_refutable {q : ℝ} (hq : 1 / 2 < q) :
    ¬ bkt2f_meanInflResidue q := by
  intro H
  set p := (1 / 2 + min q 1) / 2 with hpdef
  have hqgt : (1 / 2 : ℝ) < min q 1 := lt_min hq (by norm_num)
  have hp_lo : 1 / 2 < p := by rw [hpdef]; linarith [hqgt]
  have hp_hi : p < min q 1 := by rw [hpdef]; linarith [hqgt]
  have hp_q : p < q := lt_of_lt_of_le hp_hi (min_le_left _ _)
  have hp_1 : p < 1 := lt_of_lt_of_le hp_hi (min_le_right _ _)
  have hp0 : 0 < p := by linarith
  have hmem : p ∈ Set.Ioo (1 / 2 : ℝ) q := ⟨hp_lo, hp_q⟩
  obtain ⟨u', hu'0, hu'lt, hcap, k, hk1, hbound⟩ :=
    @H p hmem hp_1 Bool _ _ _ (fun _ => true) (1 / 2) (by norm_num) (by norm_num)
  rw [mil_constTrue_totalInfl] at hbound
  have hqpos : (0 : ℝ) < 1 + (1 - u') / (4 * p * (1 - p)) := by
    have hs0 : 0 < 4 * p * (1 - p) := by nlinarith
    have : 0 ≤ (1 - u') / (4 * p * (1 - p)) := div_nonneg (by linarith) hs0.le
    linarith
  rw [mil_constTrue_qnorm hp0.le hp_1.le hqpos] at hbound
  have hlevel1 : (4 : ℝ) * ∑ S ∈ univ.filter (fun S : Finset Bool => S.card = 1),
      (ptn_coeff p (fun ω => if (fun _ => true : ConfigSpace Bool → Bool) ω then (1 : ℝ) else 0) S) ^ 2
        = 0 := by
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro S hS
    rw [Finset.mem_filter] at hS
    rw [mil_constTrue_coeff hp0 hp_1]
    have hSne : S ≠ ∅ := by intro he; rw [he, Finset.card_empty] at hS; exact absurd hS.2 (by norm_num)
    rw [if_neg hSne]; ring
  rw [hlevel1] at hbound
  simp only [mul_zero, sub_zero, mul_one] at hbound
  have hpos : (0 : ℝ) < 4 / (1 / 2 - u') := by
    apply div_pos (by norm_num); linarith [hu'lt]
  linarith [hpos, hbound]






















def mil_VarScalarCore (q : ℝ) : Prop :=
  ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, p < 1 → ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (φ : ConfigSpace E → Bool),
      ∀ u : ℝ, 0 < u → u < 1 →
        ∃ k : ℕ, 1 ≤ k ∧
          4 * ((k : ℝ) + 1)
            * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
                * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)))
            ≤ (4 * (ptn_sigma p) ^ 2)
                * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
                    ^ (u / (2 - u))
                  - (1 - u) ^ k)
                * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)














theorem mil_levelGe2_of_var {q : ℝ} (H : mil_VarScalarCore q) :
    bkt2_levelGe2MasterResidue q := by
  intro p hp hp1 E _ _ _ φ u hu0 hu1
  have hp0 : 0 < p := by have := hp.1; linarith
  obtain ⟨k, hk1, hvar⟩ := H p hp hp1 φ u hu0 hu1
  refine ⟨k, hk1, ?_⟩
  set μ := OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) with hμ
  have hge2 := mil_levelGe2_le_var hp0 hp1 φ hu0 hu1 k
  rw [← hμ] at hge2
  have hlvl1var := mil_level1_le_var hp0 hp1 φ
  rw [← hμ] at hlvl1var
  
  have h4lvl1 : 4 * ∑ S ∈ univ.filter (fun S : Finset E => S.card = 1),
      (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 ≤ 4 * (μ * (1 - μ)) :=
    mul_le_mul_of_nonneg_left hlvl1var (by norm_num)
  linarith [hge2, hvar, h4lvl1]





theorem mil_master_of_varScalar {q : ℝ} (H : mil_VarScalarCore q) :
    pro_PBiasedMaster q :=
  bkt2_master_of_levelGe2 (mil_levelGe2_of_var H)






theorem mil_rhoOptimise_of_varScalar {q : ℝ} (H : mil_VarScalarCore q) :
    ptn_RhoOptimise q :=
  pro_rhoOptimise_of_master (mil_master_of_varScalar H)









theorem mil_varScalarCore_c0 {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hδ0 : 0 < (maxInfl (OSSS.bernoulliWeight p)
        (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0))
        ^ (u / (2 - u))) :
    ∃ k : ℕ, 1 ≤ k ∧
      4 * ((k : ℝ) + 1)
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
                (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0) := by
  set f0 : ConfigSpace E → Bool := fun _ => false with hf0
  
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
  
  have hmono : (1 - u) ^ (k + 1) ≤ (1 - u) ^ k :=
    pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
  have hσ2nn : (0 : ℝ) ≤ 4 * (ptn_sigma p) ^ 2 := by positivity
  apply mul_nonneg
  · apply mul_nonneg hσ2nn
    linarith [hk, hmono]
  · exact kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) _

end StatMech.Probability
