/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































import Code.Probability.MasterFamilyProve

open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false

namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]



















theorem mfp2_singleBit_q_gt_2_false : ¬ mfp_SingleBitQGt2 (9 / 10) := by
  intro H
  have h := H (1 / 2) (by norm_num) (by norm_num) 1 0
  rw [show |(1:ℝ)| = 1 by norm_num, show |(0:ℝ)| = 0 by norm_num] at h
  rw [show (2:ℝ) - 1 / 2 = 3 / 2 by norm_num] at h
  rw [Real.one_rpow] at h
  rw [Real.zero_rpow (by norm_num : (3:ℝ) / 2 ≠ 0)] at h
  rw [show (2:ℝ) / (3 / 2) = 4 / 3 by norm_num] at h
  rw [show ((1 - 9 / 10) * 1 + 9 / 10 * 0 : ℝ) = 1 / 10 by norm_num] at h
  have hLHS : ((1:ℝ) / 10) ^ 2 + (1 - 1 / 2) * (9 / 10 * (1 - 9 / 10)) * (1 - 0) ^ 2 = 11 / 200 := by
    norm_num
  rw [hLHS] at h
  
  have hcontra : ((1:ℝ) / 10) ^ ((4:ℝ) / 3) < 11 / 200 := by
    have hy : (0:ℝ) ≤ (11:ℝ) / 200 := by norm_num
    have hcube_x : (((1:ℝ) / 10) ^ ((4:ℝ) / 3)) ^ (3:ℕ) = ((1:ℝ) / 10) ^ (4:ℝ) := by
      rw [← Real.rpow_natCast (((1:ℝ) / 10) ^ ((4:ℝ) / 3)) 3, ← Real.rpow_mul (by norm_num)]
      norm_num
    have h10_4 : ((1:ℝ) / 10) ^ (4:ℝ) = 1 / 10000 := by
      rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num
    have hlt : (((1:ℝ) / 10) ^ ((4:ℝ) / 3)) ^ (3:ℕ) < ((11:ℝ) / 200) ^ (3:ℕ) := by
      rw [hcube_x, h10_4]; norm_num
    by_contra hc
    rw [not_lt] at hc
    exact absurd (pow_le_pow_left₀ hy hc 3) (not_le.mpr hlt)
  linarith





















def mfp2_PerCoordHighNoise (q : ℝ) : Prop :=
  ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, p < 1 → ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (φ : ConfigSpace E → Bool), ∀ u : ℝ, 0 < u → u < 1 → ∀ e : E,
      (∑ S ∈ univ.filter (fun S : Finset E => e ∈ S),
          (1 - u) ^ (S.erase e).card * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S
            / ptn_sigma p) ^ 2)
        ≤ (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / (2 - u))










theorem mfp2_noiseGap_pos {p u : ℝ} (hp : 1 / 2 < p) (_hp1 : p < 1) (_hu0 : 0 < u) (hu1 : u < 1) :
    0 < (1 - u) - (1 - u) * (4 * p * (1 - p)) := by
  have h1u : 0 < 1 - u := by linarith
  have heq : (1 - u) - (1 - u) * (4 * p * (1 - p)) = (1 - u) * (1 - 2 * p) ^ 2 := by ring
  rw [heq]
  have hne : (1 - 2 * p) ≠ 0 := by intro h; nlinarith [h]
  positivity











theorem mfp2_summed_highNoise [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) {u : ℝ}
    (Hper : ∀ e : ι,
      (∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
          (1 - u) ^ (S.erase e).card * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S
            / ptn_sigma p) ^ 2)
        ≤ (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / (2 - u))) :
    (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset ι, (S.card : ℝ) * ((1 - u) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ ∑ e : ι, (OSSS.infl (OSSS.bernoulliWeight p)
          (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / (2 - u)) := by
  set σ2 := (ptn_sigma p) ^ 2 with hσ2
  set cc := fun S : Finset ι => (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 with hcc
  have hσ2pos : 0 < σ2 := by rw [hσ2]; exact pow_pos (ptn_sigma_pos hp0 hp1) 2
  have hper : ∀ e : ι,
      (1 / σ2) * ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
          (1 - u) ^ (S.erase e).card * cc S
        ≤ (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / (2 - u)) := by
    intro e
    refine le_trans (le_of_eq ?_) (Hper e)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    rw [hcc, div_pow, one_div, hσ2]; ring
  refine le_trans ?_ (Finset.sum_le_sum (fun e _ => hper e))
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply le_of_eq
  symm
  have hinner : ∀ e : ι, (∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
        (1 - u) ^ (S.erase e).card * cc S)
      = ∑ S : Finset ι, (if e ∈ S then (1 - u) ^ (S.card - 1) * cc S else 0) := by
    intro e
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro S _
    by_cases he : e ∈ S
    · rw [if_pos he, if_pos he, Finset.card_erase_of_mem he]
    · rw [if_neg he, if_neg he]
  simp_rw [hinner]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]











theorem mfp2_master_of_perCoordHighNoise [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (Hper : ∀ e : ι,
      (∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
          (1 - u) ^ (S.erase e).card * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S
            / ptn_sigma p) ^ 2)
        ≤ (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / (2 - u))) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  set δ := maxInfl (OSSS.bernoulliWeight p) f with hδ
  set T := totalInfl (OSSS.bernoulliWeight p) f with hT
  set cc := fun S : Finset ι => (ptn_coeff p f S) ^ 2 with hcc
  
  have hsummed := mfp2_summed_highNoise hp0 hp1 φ Hper
  
  have hq1 : (1:ℝ) ≤ 2 - u := by linarith
  have hq2 : (2:ℝ) - u ≤ 2 := by linarith
  have hcap := ptn_cap_sum (ι := ι) hp0 hp1 hq1 hq2 φ
  
  have hchain := le_trans hsummed hcap
  
  have h2une : (2:ℝ) - u ≠ 0 := by linarith
  have hexp : (2:ℝ) / (2 - u) - 1 = u / (2 - u) := by
    rw [div_sub_one h2une]; congr 1; ring
  rw [hexp] at hchain
  
  have hσ2ne : (ptn_sigma p) ^ 2 ≠ 0 := (pow_pos (ptn_sigma_pos hp0 hp1) 2).ne'
  have h4σ : 4 * (ptn_sigma p) ^ 2 ≤ 1 := by
    rw [ptn_sigma_sq hp0 hp1]; nlinarith [sq_nonneg (1 - 2 * p)]
  have hRHSnn : 0 ≤ δ ^ (u / (2 - u)) * T :=
    mul_nonneg (Real.rpow_nonneg (kkl_maxInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) f) _)
      (kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) f)
  
  have hLHS : (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * cc S)
      = 4 * (ptn_sigma p) ^ 2 * ((1 / (ptn_sigma p) ^ 2)
          * ∑ S : Finset ι, (S.card : ℝ) * ((1 - u) ^ (S.card - 1) * cc S)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    rw [show 4 * (ptn_sigma p) ^ 2 * (1 / (ptn_sigma p) ^ 2 * ((S.card : ℝ) * ((1 - u) ^ (S.card - 1) * cc S)))
        = (4 * ((S.card : ℝ) * ((1 - u) ^ (S.card - 1) * cc S))) * ((ptn_sigma p) ^ 2 / (ptn_sigma p) ^ 2) from by ring]
    rw [div_self hσ2ne, mul_one]; ring
  rw [hLHS]
  calc 4 * (ptn_sigma p) ^ 2 * ((1 / (ptn_sigma p) ^ 2)
          * ∑ S : Finset ι, (S.card : ℝ) * ((1 - u) ^ (S.card - 1) * cc S))
      ≤ 4 * (ptn_sigma p) ^ 2 * (δ ^ (u / (2 - u)) * T) :=
        mul_le_mul_of_nonneg_left hchain (by positivity)
    _ ≤ 1 * (δ ^ (u / (2 - u)) * T) := mul_le_mul_of_nonneg_right h4σ hRHSnn
    _ = δ ^ (u / (2 - u)) * T := by rw [one_mul]







theorem mfp2_openResidue_of_perCoordHighNoise {q : ℝ} (H : mfp2_PerCoordHighNoise q) :
    frh_openResidue q := by
  intro p hp hp1 E _ _ _ φ u hu0 hu1
  have hp0 : 0 < p := by have := hp.1; linarith
  exact mfp2_master_of_perCoordHighNoise hp0 hp1 φ hu0 hu1 (fun e => H p hp hp1 φ u hu0 hu1 e)










theorem mfp2_perCoordHighNoise_half [Nonempty ι] (φ : ConfigSpace ι → Bool)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (e : ι) :
    (∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
        (1 - u) ^ (S.erase e).card * (ptn_coeff (1 / 2 : ℝ) (fun ω => if φ ω then (1 : ℝ) else 0) S
          / ptn_sigma (1 / 2 : ℝ)) ^ 2)
      ≤ (OSSS.infl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) e)
          ^ (2 / (2 - u)) := by
  have hp0 : (0:ℝ) < 1 / 2 := by norm_num
  have hp1 : (1 / 2 : ℝ) < 1 := by norm_num
  set ρ := Real.sqrt (1 - u) with hρ
  have hu1' : (0:ℝ) ≤ 1 - u := by linarith
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ1 : ρ ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  set q := 2 - u with hq
  have hq1 : (1:ℝ) ≤ q := by rw [hq]; linarith
  have hq2 : q ≤ 2 := by rw [hq]; linarith
  have hρsq : ρ ^ 2 = (q - 1) * 4 * (1 / 2 : ℝ) * (1 - 1 / 2) := by
    rw [hρ, Real.sq_sqrt hu1', hq]; ring
  have hper := ptn_perCoord_hc (ι := ι) hp0 hp1 hρ0 hρ1 hq1 hq2 hρsq φ e
  refine le_trans (le_of_eq ?_) hper
  apply Finset.sum_congr rfl
  intro S _
  congr 1
  rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hu1']








theorem mfp2_master_half_via_perCoord [Nonempty ι] (φ : ConfigSpace ι → Bool)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff (1 / 2 : ℝ) (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0))
          ^ (u / (2 - u))
        * totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  mfp2_master_of_perCoordHighNoise (by norm_num) (by norm_num) φ hu0 hu1
    (fun e => mfp2_perCoordHighNoise_half φ hu0 hu1 e)






theorem mfp2_perCoordHighNoise_nonvacuous {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool)
    (u : ℝ) (e : E) :
    (∑ _S ∈ univ.filter (fun S : Finset E => e ∈ S), (0 : ℝ))
      ≤ (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / (2 - u)) := by
  rw [Finset.sum_const, smul_zero]
  exact Real.rpow_nonneg
    (kkl_infl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) _ e) _






theorem mfp2_perCoordHighNoise_noncirc {q : ℝ} (H : mfp2_PerCoordHighNoise q)
    {p : ℝ} (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (e : E) :
    (∑ S ∈ univ.filter (fun S : Finset E => e ∈ S),
        (1 - u) ^ (S.erase e).card * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S
          / ptn_sigma p) ^ 2)
      ≤ (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / (2 - u)) :=
  H p hp hp1 φ u hu0 hu1 e









theorem mfp2_kesten_of_perCoordHighNoise {q : ℝ} (H : mfp2_PerCoordHighNoise q)
    {p : ℝ} (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q) (hp1 : p < 1) :
    KKLHypercontractive p 2 :=
  mfp_kesten_of_masterFamily (mfp2_openResidue_of_perCoordHighNoise H) hp hp1









theorem mfp2_kkl_logGain_of_perCoordHighNoise {q : ℝ} (H : mfp2_PerCoordHighNoise q)
    {p : ℝ} (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool) :
    2 * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
          * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)))
        * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  mfp_kkl_logGain_of_masterFamily (mfp2_openResidue_of_perCoordHighNoise H) hp hp1 φ

end StatMech.Probability
