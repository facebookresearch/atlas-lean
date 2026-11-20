/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































































import Code.Probability.CoupledTensorizeProve
import Code.Probability.BKKKLTruncation

open scoped BigOperators
open Finset Real Set
open intervalIntegral MeasureTheory

set_option linter.style.longLine false

namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]





theorem sbk_coeff0_sq : (ptn_coeff (9/10 : ℝ) ctp_f {0}) ^ 2 = 9 / 10000 := by
  have hp0 : (0:ℝ) < 9/10 := by norm_num
  have hσ2 : ptn_sigma (9/10 : ℝ) ^ 2 = (9/10) * (1 - 9/10) := ptn_sigma_sq hp0 (by norm_num)
  have hσne : ptn_sigma (9/10 : ℝ) ≠ 0 := (ptn_sigma_pos hp0 (by norm_num)).ne'
  have h := ctp_coeff_zero_sq_div
  rw [div_pow] at h
  have heq : (ptn_coeff (9/10:ℝ) ctp_f {0})^2 = (1/100) * ptn_sigma (9/10)^2 := by
    field_simp at h ⊢; linarith [h]
  rw [heq, hσ2]; norm_num


theorem sbk_coeff1_sq : (ptn_coeff (9/10 : ℝ) ctp_f {1}) ^ 2 = 9 / 10000 := by
  have hp0 : (0:ℝ) < 9/10 := by norm_num
  have hσ2 : ptn_sigma (9/10 : ℝ) ^ 2 = (9/10) * (1 - 9/10) := ptn_sigma_sq hp0 (by norm_num)
  have hσne : ptn_sigma (9/10 : ℝ) ≠ 0 := (ptn_sigma_pos hp0 (by norm_num)).ne'
  have hc : ptn_coeff (9/10 : ℝ) ctp_f {1} = (9/1000 : ℝ) / ptn_sigma (9/10) := by
    unfold ptn_coeff; rw [ctp_expect_fin2]
    have hch : ∀ ω : ConfigSpace (Fin 2), ptn_pchar (9/10:ℝ) {1} ω = ptn_psi (9/10) (ω 1) := by
      intro ω; unfold ptn_pchar; rw [Finset.prod_singleton]
    simp only [hch, ctp_cfg_one, ctp_f_ff, ctp_f_ft, ctp_f_tf, ctp_f_tt]
    rw [ctp_psi_eval, ctp_psi_eval]; simp only [Bool.false_eq_true, if_false, if_true]
    field_simp; ring
  rw [hc, div_pow, hσ2]; norm_num



theorem sbk_coeff01_sq :
    (ptn_coeff (9/10 : ℝ) ctp_f ({0,1}:Finset (Fin 2))) ^ 2 = 81 / 10000 := by
  have hp0 : (0:ℝ) < 9/10 := by norm_num
  have hσ2 : ptn_sigma (9/10 : ℝ) ^ 2 = (9/10) * (1 - 9/10) := ptn_sigma_sq hp0 (by norm_num)
  have hσne : ptn_sigma (9/10 : ℝ) ≠ 0 := (ptn_sigma_pos hp0 (by norm_num)).ne'
  have h := ctp_coeff_zeroone_sq_div
  rw [div_pow] at h
  have heq : (ptn_coeff (9/10:ℝ) ctp_f ({0,1}:Finset (Fin 2)))^2 = (9/100) * ptn_sigma (9/10)^2 := by
    field_simp at h ⊢; linarith [h]
  rw [heq, hσ2]; norm_num


theorem sbk_OR_infl1 : OSSS.infl (OSSS.bernoulliWeight (9/10 : ℝ)) ctp_f 1 = 1 / 10 := by
  unfold OSSS.infl
  rw [ctp_expect_fin2]
  have hopen : ∀ a b : Bool, (StatMech.setOpen 1 (ctp_cfg a b)) = ctp_cfg a true := by
    intro a b; funext i; fin_cases i <;> simp [StatMech.setOpen, ctp_cfg, Function.update]
  have hclosed : ∀ a b : Bool, (StatMech.setClosed 1 (ctp_cfg a b)) = ctp_cfg a false := by
    intro a b; funext i; fin_cases i <;> simp [StatMech.setClosed, ctp_cfg, Function.update]
  simp only [hopen, hclosed, ctp_f_ff, ctp_f_ft, ctp_f_tf, ctp_f_tt]
  norm_num


theorem sbk_OR_totalInfl : totalInfl (OSSS.bernoulliWeight (9/10 : ℝ)) ctp_f = 1/5 := by
  unfold totalInfl
  rw [Fin.sum_univ_two, ctp_OR_infl0, sbk_OR_infl1]; norm_num


theorem sbk_OR_maxInfl : maxInfl (OSSS.bernoulliWeight (9/10 : ℝ)) ctp_f = 1/10 := by
  unfold maxInfl
  have hfun : (OSSS.infl (OSSS.bernoulliWeight (9/10:ℝ)) ctp_f) = fun _ => (1/10 : ℝ) := by
    funext e; fin_cases e
    · exact ctp_OR_infl0
    · exact sbk_OR_infl1
  rw [hfun]
  simp [Finset.sup'_const]


theorem sbk_univ_fin2 :
    (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0,1}} := by decide






theorem sbk_OR_summed_lhs :
    (∑ S : Finset (Fin 2), 4 * (S.card : ℝ) * (1 - (1/2:ℝ)) ^ (S.card - 1)
        * (ptn_coeff (9/10:ℝ) ctp_f S) ^ 2) = 99/2500 := by
  rw [sbk_univ_fin2]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  rw [show (∅ : Finset (Fin 2)).card = 0 by decide, show ({0}:Finset (Fin 2)).card = 1 by decide,
      show ({1}:Finset (Fin 2)).card = 1 by decide, show ({0,1}:Finset (Fin 2)).card = 2 by decide]
  rw [sbk_coeff0_sq, sbk_coeff1_sq, sbk_coeff01_sq]
  norm_num




theorem sbk_numeric : (99:ℝ)/500 ≤ ((1:ℝ)/10) ^ ((1:ℝ)/3) := by
  have hr : (0:ℝ) ≤ ((1:ℝ)/10) ^ ((1:ℝ)/3) := Real.rpow_nonneg (by norm_num) _
  have hcube : ((99:ℝ)/500)^(3:ℕ) ≤ (((1:ℝ)/10)^((1:ℝ)/3))^(3:ℕ) := by
    rw [← Real.rpow_natCast (((1:ℝ)/10)^((1:ℝ)/3)) 3, ← Real.rpow_mul (by norm_num)]
    norm_num
  by_contra hc
  rw [not_le] at hc
  have := pow_lt_pow_left₀ hc hr (by norm_num : (3:ℕ) ≠ 0)
  linarith [hcube, this]














theorem sbk_summed_holds_at_OR :
    (∑ S : Finset (Fin 2), 4 * (S.card : ℝ) * (1 - (1/2:ℝ)) ^ (S.card - 1)
        * (ptn_coeff (9/10:ℝ) ctp_f S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight (9/10:ℝ)) ctp_f) ^ ((1/2:ℝ) / (2 - 1/2))
        * totalInfl (OSSS.bernoulliWeight (9/10:ℝ)) ctp_f := by
  rw [sbk_OR_summed_lhs, sbk_OR_maxInfl, sbk_OR_totalInfl]
  rw [show (1/2:ℝ) / (2 - 1/2) = 1/3 by norm_num]
  
  have hr : (0:ℝ) ≤ ((1:ℝ)/10) ^ ((1:ℝ)/3) := Real.rpow_nonneg (by norm_num) _
  nlinarith [sbk_numeric, hr]




theorem sbk_numeric_master_false :
    ((1 : ℝ) / 10) ^ ((1 : ℝ) / 3) * (9 / 125) < 99 / 2500 := by
  set r : ℝ := ((1 : ℝ) / 10) ^ ((1 : ℝ) / 3) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr3 : r ^ (3 : ℕ) = (1 : ℝ) / 10 := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hrlt : r < 1 / 2 := by
    by_contra h
    rw [not_lt] at h
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) h 3
    rw [hr3] at hpow
    norm_num at hpow
  nlinarith





theorem sbk_pBiasedMaster_false {q : ℝ} (hq : (9 : ℝ) / 10 < q) :
    ¬ pro_PBiasedMaster q := by
  intro H
  have hp : (9 / 10 : ℝ) ∈ Set.Ioo (1 / 2 : ℝ) q := ⟨by norm_num, hq⟩
  have h := H (9 / 10) hp (by norm_num) ctp_OR (1 / 2) (by norm_num) (by norm_num)
  change (∑ S : Finset (Fin 2), 4 * (S.card : ℝ) * (1 - (1 / 2 : ℝ)) ^ (S.card - 1)
      * (ptn_coeff (9 / 10 : ℝ) ctp_f S) ^ 2) ≤ _ at h
  rw [sbk_OR_summed_lhs,
    show (fun ω => if ctp_OR ω then (1 : ℝ) else 0) = ctp_f from rfl,
    sbk_OR_maxInfl, sbk_OR_totalInfl,
    ptn_sigma_sq (by norm_num : (0 : ℝ) < 9 / 10)
      (by norm_num : (9 : ℝ) / 10 < 1)] at h
  rw [show (1 / 2 : ℝ) / (2 - 1 / 2) = 1 / 3 by norm_num] at h
  have hfalse := sbk_numeric_master_false
  norm_num at h
  nlinarith




theorem sbk_lowDegreeMasterResidue_false {q : ℝ} (hq : (9 : ℝ) / 10 < q) :
    ¬ bkt_lowDegreeMasterResidue q := by
  intro H
  exact sbk_pBiasedMaster_false hq (bkt_master_of_residue H)





















theorem sbk_engine_integral_eq (n : ℕ) {s : ℝ} :
    (∫ v in (1 - s)..(1:ℝ), ((n : ℝ) + 1) * (1 - v) ^ n) = s ^ (n + 1) := by
  rw [intervalIntegral.integral_const_mul]
  have h := intervalIntegral.integral_comp_sub_left (a := (1 - s)) (b := (1:ℝ))
    (fun x => x ^ n) 1
  simp only at h
  rw [h, integral_pow]
  rw [show (1:ℝ) - (1 - s) = s by ring, show (1:ℝ) - 1 = 0 by ring]
  rw [zero_pow (by omega : n + 1 ≠ 0)]
  field_simp
  ring









theorem sbk_engine_integral_damped {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {d : ℕ} (hd : 1 ≤ d) :
    (∫ v in (1 - s)..(1:ℝ), (d : ℝ) * (1 - v) ^ (d - 1)) < 1 := by
  have hdd : (d - 1) + 1 = d := by omega
  have hcast : ((d - 1 : ℕ) : ℝ) + 1 = (d : ℝ) := by
    have := congrArg (Nat.cast (R := ℝ)) hdd; push_cast at this; linarith
  have hval : (∫ v in (1 - s)..(1:ℝ), (d : ℝ) * (1 - v) ^ (d - 1)) = s ^ ((d - 1) + 1) := by
    rw [← hcast]; exact sbk_engine_integral_eq (d - 1)
  rw [hval, hdd]
  calc s ^ d ≤ s ^ 1 := pow_le_pow_of_le_one hs0.le hs1.le hd
    _ = s := pow_one s
    _ < 1 := hs1






























theorem sbk_openResidue_of_lowDegree {q : ℝ} (H : bkt_lowDegreeMasterResidue q) :
    frh_openResidue q := by
  
  
  have hmaster := bkt_master_of_residue H
  intro p hp hp1 E _ _ _ φ u hu0 hu1
  have hp0 : 0 < p := by have := hp.1; linarith
  
  have hM := hmaster p hp hp1 φ u hu0.le hu1.le
  
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  set δ := maxInfl (OSSS.bernoulliWeight p) f with hδ
  set T := totalInfl (OSSS.bernoulliWeight p) f with hT
  have hδnn : 0 ≤ δ := kkl_maxInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) f
  have hTnn : 0 ≤ T := kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) f
  have hσ2val : (ptn_sigma p) ^ 2 = p * (1 - p) := ptn_sigma_sq hp0 hp1
  have h4σ : 4 * (ptn_sigma p) ^ 2 ≤ 1 := by rw [hσ2val]; nlinarith [sq_nonneg (1 - 2 * p)]
  have hσ2nn : (0:ℝ) ≤ 4 * (ptn_sigma p) ^ 2 := by positivity
  have hδexpnn : 0 ≤ δ ^ (u / (2 - u)) := Real.rpow_nonneg hδnn _
  refine le_trans hM ?_
  calc δ ^ (u / (2 - u)) * (4 * (ptn_sigma p) ^ 2 * T)
      = (4 * (ptn_sigma p) ^ 2) * (δ ^ (u / (2 - u)) * T) := by ring
    _ ≤ 1 * (δ ^ (u / (2 - u)) * T) := by
        apply mul_le_mul_of_nonneg_right h4σ; positivity
    _ = δ ^ (u / (2 - u)) * T := one_mul _



theorem sbk_kesten_of_lowDegree {q : ℝ} (H : bkt_lowDegreeMasterResidue q)
    {p : ℝ} (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q) (hp1 : p < 1) :
    KKLHypercontractive p 2 :=
  mfp_kesten_of_masterFamily (sbk_openResidue_of_lowDegree H) hp hp1









theorem sbk_summed_half [Nonempty ι] (φ : ConfigSpace ι → Bool)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff (1 / 2 : ℝ) (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0))
          ^ (u / (2 - u))
        * totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  mfp2_master_half_via_perCoord φ hu0 hu1





theorem sbk_weightGap_vanishes_half (u : ℝ) (d : ℕ) :
    (1 - u) ^ (d - 1) - ((1 - u) * (4 * (1/2:ℝ) * (1 - 1/2))) ^ (d - 1) = 0 := by
  rw [show (4 * (1/2:ℝ) * (1 - 1/2)) = 1 by norm_num, mul_one, sub_self]






theorem sbk_summed_survives_percoord_fails {q : ℝ} (hq : (9 : ℝ) / 10 < q) :
    (¬ mfp2_PerCoordHighNoise q)
      ∧ (∑ S : Finset (Fin 2), 4 * (S.card : ℝ) * (1 - (1/2:ℝ)) ^ (S.card - 1)
            * (ptn_coeff (9/10:ℝ) ctp_f S) ^ 2)
          ≤ (maxInfl (OSSS.bernoulliWeight (9/10:ℝ)) ctp_f) ^ ((1/2:ℝ) / (2 - 1/2))
            * totalInfl (OSSS.bernoulliWeight (9/10:ℝ)) ctp_f
      ∧ (bkt_lowDegreeMasterResidue q → frh_openResidue q) :=
  ⟨ctp_perCoordHighNoise_false hq, sbk_summed_holds_at_OR, sbk_openResidue_of_lowDegree⟩

end StatMech.Probability
