/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































import Code.Probability.PBiasedTensorize
import Code.Probability.FullRangeHC
import Code.Probability.PBiasedRhoOptimise
import Code.Probability.VarGapProve2

open scoped BigOperators
open Finset
open Real Set
open StatMech StatMech.OSSS

set_option linter.style.longLine false

namespace StatMech.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]






















def PBiasedHCLib (p : ℝ) : Prop :=
  ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 → ∀ u v : ℝ,
    ((1 - p) * u + p * v) ^ 2 + ρ ^ 2 * (p * (1 - p)) * (u - v) ^ 2
      ≤ ((1 - p) * |u| ^ (1 + ρ ^ 2) + p * |v| ^ (1 + ρ ^ 2)) ^ (2 / (1 + ρ ^ 2))





theorem htl_cons_quadform_eq {p ρ u v : ℝ} :
    (1 - p) * (ptn_kbit p ρ false false * u + ptn_kbit p ρ false true * v) ^ 2
        + p * (ptn_kbit p ρ true false * u + ptn_kbit p ρ true true * v) ^ 2
      = ((1 - p) * u + p * v) ^ 2 + ρ ^ 2 * (p * (1 - p)) * (u - v) ^ 2 := by
  rw [ptn_kbit_ff, ptn_kbit_ft, ptn_kbit_tf, ptn_kbit_tt]; ring







theorem htl_pbiasedHCLib_half {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (u v : ℝ) :
    ((1 - (1 / 2 : ℝ)) * u + (1 / 2) * v) ^ 2
        + ρ ^ 2 * ((1 / 2 : ℝ) * (1 - 1 / 2)) * (u - v) ^ 2
      ≤ ((1 - (1 / 2 : ℝ)) * |u| ^ (1 + ρ ^ 2) + (1 / 2) * |v| ^ (1 + ρ ^ 2)) ^ (2 / (1 + ρ ^ 2)) := by
  have hbts := bts_twoPointScalar h0 h1 ((u + v) / 2) ((u - v) / 2)
  
  have ha : (u + v) / 2 + (u - v) / 2 = u := by ring
  have hb : (u + v) / 2 - (u - v) / 2 = v := by ring
  rw [ha, hb] at hbts
  
  have hLHS : ((1 - (1 / 2 : ℝ)) * u + (1 / 2) * v) ^ 2
        + ρ ^ 2 * ((1 / 2 : ℝ) * (1 - 1 / 2)) * (u - v) ^ 2
      = ((u + v) / 2) ^ 2 + ρ ^ 2 * ((u - v) / 2) ^ 2 := by ring
  
  have hRHS : ((|u| ^ (1 + ρ ^ 2) + |v| ^ (1 + ρ ^ 2)) / 2) ^ (2 / (1 + ρ ^ 2))
      = ((1 - (1 / 2 : ℝ)) * |u| ^ (1 + ρ ^ 2) + (1 / 2) * |v| ^ (1 + ρ ^ 2)) ^ (2 / (1 + ρ ^ 2)) := by
    congr 1; ring
  rw [hLHS]
  rw [hRHS] at hbts
  exact hbts




theorem htl_lib_half : PBiasedHCLib (1 / 2) :=
  fun _ρ h0 h1 u v => htl_pbiasedHCLib_half h0 h1 u v












theorem htl_tensorStep {p ρ q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (hqeq : q = 1 + ρ ^ 2) (H : PBiasedHCLib p) (n : ℕ)
    (ih : ∀ g : (Fin n → Bool) → ℝ, ptn_qnorm p 2 (ptn_kop p ρ g) ≤ ptn_qnorm p q g)
    (f : (Fin (n + 1) → Bool) → ℝ) :
    ptn_qnorm p 2 (ptn_kop p ρ f) ≤ ptn_qnorm p q f := by
  have hq1 : 1 ≤ q := by rw [hqeq]; nlinarith [sq_nonneg ρ]
  have hq0 : (0 : ℝ) < q := by linarith
  set g₀ : (Fin n → Bool) → ℝ := fun ω' => f (Fin.cons false ω') with hg0
  set g₁ : (Fin n → Bool) → ℝ := fun ω' => f (Fin.cons true ω') with hg1
  set F₀ := ptn_kop p ρ g₀ with hF0
  set F₁ := ptn_kop p ρ g₁ with hF1
  set Eu := OSSS.expect (OSSS.bernoulliWeight p) (fun ω : Fin n → Bool => (F₀ ω) ^ 2) with hEu
  set Ev := OSSS.expect (OSSS.bernoulliWeight p) (fun ω : Fin n → Bool => (F₁ ω) ^ 2) with hEv
  set Euv := OSSS.expect (OSSS.bernoulliWeight p) (fun ω : Fin n → Bool => F₀ ω * F₁ ω) with hEuv
  set u := Real.sqrt Eu with hu
  set v := Real.sqrt Ev with hv
  have hEunn : 0 ≤ Eu := by
    rw [hEu]; unfold OSSS.expect
    exact Finset.sum_nonneg (fun ω _ => mul_nonneg
      (Finset.prod_nonneg (fun e _ => (bernoulliWeight_isProbWeight hp0.le hp1.le).nonneg e (ω e)))
      (sq_nonneg _))
  have hEvnn : 0 ≤ Ev := by
    rw [hEv]; unfold OSSS.expect
    exact Finset.sum_nonneg (fun ω _ => mul_nonneg
      (Finset.prod_nonneg (fun e _ => (bernoulliWeight_isProbWeight hp0.le hp1.le).nonneg e (ω e)))
      (sq_nonneg _))
  have hunn : 0 ≤ u := Real.sqrt_nonneg _
  have hvnn : 0 ≤ v := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = Eu := Real.sq_sqrt hEunn
  have hv2 : v ^ 2 = Ev := Real.sq_sqrt hEvnn
  have hCS : Euv ≤ u * v := by rw [hu, hv]; exact ptn_expect_inner_le hp0.le hp1.le F₀ F₁
  have hLHS : ptn_qnormPow p 2 (ptn_kop p ρ f)
      = (1 - p) * (ptn_kbit p ρ false false ^ 2 * Eu
            + 2 * ptn_kbit p ρ false false * ptn_kbit p ρ false true * Euv
            + ptn_kbit p ρ false true ^ 2 * Ev)
        + p * (ptn_kbit p ρ true false ^ 2 * Eu
            + 2 * ptn_kbit p ρ true false * ptn_kbit p ρ true true * Euv
            + ptn_kbit p ρ true true ^ 2 * Ev) := by
    rw [ptn_kop_l2sq_cons]
    rw [ptn_expect_sq_lincomb p (ptn_kbit p ρ false false) (ptn_kbit p ρ false true) F₀ F₁,
        ptn_expect_sq_lincomb p (ptn_kbit p ρ true false) (ptn_kbit p ρ true true) F₀ F₁]
  have hcoef0 : 0 ≤ (1 - p) * (2 * ptn_kbit p ρ false false * ptn_kbit p ρ false true) := by
    have := ptn_kbit_nonneg h0 h1 hp0.le hp1.le false false
    have := ptn_kbit_nonneg h0 h1 hp0.le hp1.le false true
    positivity
  have hcoef1 : 0 ≤ p * (2 * ptn_kbit p ρ true false * ptn_kbit p ρ true true) := by
    have := ptn_kbit_nonneg h0 h1 hp0.le hp1.le true false
    have := ptn_kbit_nonneg h0 h1 hp0.le hp1.le true true
    positivity
  set a00 := ptn_kbit p ρ false false with ha00
  set a01 := ptn_kbit p ρ false true with ha01
  set a10 := ptn_kbit p ρ true false with ha10
  set a11 := ptn_kbit p ρ true true with ha11
  have hbound : ptn_qnormPow p 2 (ptn_kop p ρ f)
      ≤ (1 - p) * (a00 * u + a01 * v) ^ 2 + p * (a10 * u + a11 * v) ^ 2 := by
    rw [hLHS]
    have hgoal : (1 - p) * (a00 * u + a01 * v) ^ 2 + p * (a10 * u + a11 * v) ^ 2
        - ((1 - p) * (a00 ^ 2 * Eu + 2 * a00 * a01 * Euv + a01 ^ 2 * Ev)
          + p * (a10 ^ 2 * Eu + 2 * a10 * a11 * Euv + a11 ^ 2 * Ev))
        = (1 - p) * (2 * a00 * a01) * (u * v - Euv) + p * (2 * a10 * a11) * (u * v - Euv) := by
      rw [← hu2, ← hv2]; ring
    have hc0 : 0 ≤ (1 - p) * (2 * a00 * a01) * (u * v - Euv) :=
      mul_nonneg hcoef0 (by linarith [hCS])
    have hc1 : 0 ≤ p * (2 * a10 * a11) * (u * v - Euv) :=
      mul_nonneg hcoef1 (by linarith [hCS])
    linarith [hgoal, hc0, hc1]
  
  have hquad := htl_cons_quadform_eq (p := p) (ρ := ρ) (u := u) (v := v)
  have hpcx := H ρ h0 h1 u v
  rw [← hqeq] at hpcx
  rw [abs_of_nonneg hunn, abs_of_nonneg hvnn] at hpcx
  have hstep1 : ptn_qnormPow p 2 (ptn_kop p ρ f)
      ≤ ((1 - p) * u ^ q + p * v ^ q) ^ (2 / q) := by
    refine le_trans hbound ?_
    rw [hquad]; exact hpcx
  have hub : u ≤ ptn_qnorm p q g₀ := by
    have hsq : Eu = (ptn_qnorm p 2 F₀) ^ 2 := by
      rw [hEu, ← ptn_qnormPow2_eq_expect_sq, ptn_qnorm2_sq hp0.le hp1.le F₀]
    rw [hu, hsq, Real.sqrt_sq (ptn_qnorm_nonneg hp0.le hp1.le 2 F₀)]
    exact ih g₀
  have hvb : v ≤ ptn_qnorm p q g₁ := by
    have hsq : Ev = (ptn_qnorm p 2 F₁) ^ 2 := by
      rw [hEv, ← ptn_qnormPow2_eq_expect_sq, ptn_qnorm2_sq hp0.le hp1.le F₁]
    rw [hv, hsq, Real.sqrt_sq (ptn_qnorm_nonneg hp0.le hp1.le 2 F₁)]
    exact ih g₁
  have huq : u ^ q ≤ ptn_qnormPow p q g₀ := by
    rw [← ptn_qnorm_rpow_self hp0.le hp1.le (ne_of_gt hq0) g₀]
    exact Real.rpow_le_rpow hunn hub hq0.le
  have hvq : v ^ q ≤ ptn_qnormPow p q g₁ := by
    rw [← ptn_qnorm_rpow_self hp0.le hp1.le (ne_of_gt hq0) g₁]
    exact Real.rpow_le_rpow hvnn hvb hq0.le
  have hbasebound : (1 - p) * u ^ q + p * v ^ q ≤ ptn_qnormPow p q f := by
    rw [ptn_qnormPow_cons_split p q f, ← hg0, ← hg1]
    have h1p : 0 ≤ 1 - p := by linarith
    have hA := mul_le_mul_of_nonneg_left huq h1p
    have hB := mul_le_mul_of_nonneg_left hvq hp0.le
    linarith
  have hBnn : (0 : ℝ) ≤ (1 - p) * u ^ q + p * v ^ q := by
    have : (0:ℝ) ≤ u ^ q := Real.rpow_nonneg hunn q
    have : (0:ℝ) ≤ v ^ q := Real.rpow_nonneg hvnn q
    have h1p : 0 ≤ 1 - p := by linarith
    positivity
  have hstep2 : ptn_qnormPow p 2 (ptn_kop p ρ f) ≤ (ptn_qnormPow p q f) ^ (2 / q) := by
    refine le_trans hstep1 ?_
    exact Real.rpow_le_rpow hBnn hbasebound (by positivity)
  unfold ptn_qnorm
  calc (ptn_qnormPow p 2 (ptn_kop p ρ f)) ^ (1 / (2:ℝ))
      ≤ ((ptn_qnormPow p q f) ^ (2 / q)) ^ (1 / (2:ℝ)) :=
        Real.rpow_le_rpow (ptn_qnormPow_nonneg hp0.le hp1.le 2 _) hstep2 (by norm_num)
    _ = (ptn_qnormPow p q f) ^ (1 / q) := by
        rw [← Real.rpow_mul (ptn_qnormPow_nonneg hp0.le hp1.le q f)]
        congr 1; field_simp






theorem htl_hypercontractivity_fin {p ρ q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 ≤ ρ)
    (h1 : ρ ≤ 1) (hqeq : q = 1 + ρ ^ 2) (H : PBiasedHCLib p)
    (n : ℕ) (f : (Fin n → Bool) → ℝ) :
    ptn_qnorm p 2 (ptn_kop p ρ f) ≤ ptn_qnorm p q f := by
  have hq0 : (0:ℝ) < q := by rw [hqeq]; nlinarith [sq_nonneg ρ]
  induction n with
  | zero =>
    rw [ptn_kop_fin_zero, ptn_qnorm_fin_zero (by norm_num : (0:ℝ) < 2),
        ptn_qnorm_fin_zero hq0]
  | succ m ih => exact htl_tensorStep hp0 hp1 h0 h1 hqeq H m (fun g => ih g) f




theorem htl_lowDegreeWeight_fin {p ρ q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 ≤ ρ)
    (h1 : ρ ≤ 1) (hqeq : q = 1 + ρ ^ 2) (H : PBiasedHCLib p)
    (n : ℕ) (f : (Fin n → Bool) → ℝ) :
    (∑ S : Finset (Fin n), (ρ ^ S.card) ^ 2 * (ptn_coeff p f S) ^ 2)
      ≤ (ptn_qnorm p q f) ^ 2 := by
  have hhc := htl_hypercontractivity_fin hp0 hp1 h0 h1 hqeq H n f
  have hlhsnn : 0 ≤ ptn_qnorm p 2 (ptn_kop p ρ f) := ptn_qnorm_nonneg hp0.le hp1.le 2 _
  have hrhsnn : 0 ≤ ptn_qnorm p q f := ptn_qnorm_nonneg hp0.le hp1.le q f
  have hsq : (ptn_qnorm p 2 (ptn_kop p ρ f)) ^ 2 ≤ (ptn_qnorm p q f) ^ 2 := by
    nlinarith [hhc, hlhsnn, hrhsnn]
  rw [ptn_qnorm2_sq hp0.le hp1.le, ptn_qnormPow2_eq_expect_sq, ptn_kop_eq_noiseOp hp0 hp1,
      ptn_noiseOp_l2sq hp0 hp1] at hsq
  exact hsq




theorem htl_lowDegreeWeight {p ρ q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 ≤ ρ)
    (h1 : ρ ≤ 1) (hqeq : q = 1 + ρ ^ 2) (H : PBiasedHCLib p)
    (f : ConfigSpace ι → ℝ) :
    (∑ S : Finset ι, (ρ ^ S.card) ^ 2 * (ptn_coeff p f S) ^ 2)
      ≤ (ptn_qnorm p q f) ^ 2 := by
  set σ : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm with hσ
  have hfin := htl_lowDegreeWeight_fin hp0 hp1 h0 h1 hqeq H (Fintype.card ι)
    (ptn_reindex σ f)
  have hL : (∑ S : Finset (Fin (Fintype.card ι)), (ρ ^ S.card) ^ 2 * (ptn_coeff p (ptn_reindex σ f) S) ^ 2)
      = ∑ S : Finset ι, (ρ ^ S.card) ^ 2 * (ptn_coeff p f S) ^ 2 := by
    rw [← ptn_noiseOp_l2sq hp0 hp1, ← ptn_noiseOp_l2sq hp0 hp1,
        ← ptn_kop_eq_noiseOp hp0 hp1, ← ptn_kop_eq_noiseOp hp0 hp1,
        ptn_kop_reindex σ p ρ f]
    rw [show (fun ω => (ptn_reindex σ (ptn_kop p ρ f) ω) ^ 2)
        = ptn_reindex σ (fun x => (ptn_kop p ρ f x) ^ 2) from rfl, ptn_expect_reindex]
  rw [hL, ptn_qnorm_reindex σ p q f] at hfin
  exact hfin
















theorem htl_perCoord_hc {p ρ q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (hqeq : q = 1 + ρ ^ 2) (H : PBiasedHCLib p)
    (φ : ConfigSpace ι → Bool) (e : ι) :
    (∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
        (ρ ^ (S.erase e).card) ^ 2 * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S
          / ptn_sigma p) ^ 2)
      ≤ (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / q) := by
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  have hq0 : (0:ℝ) < q := by rw [hqeq]; nlinarith [sq_nonneg ρ]
  have hldw := htl_lowDegreeWeight hp0 hp1 h0 h1 hqeq H (ptn_deriv f e)
  rw [show (∑ S : Finset ι, (ρ ^ S.card) ^ 2 * (ptn_coeff p (ptn_deriv f e) S) ^ 2)
      = OSSS.expect (OSSS.bernoulliWeight p) (fun x => (ptn_kop p ρ (ptn_deriv f e) x) ^ 2) from by
        rw [ptn_kop_eq_noiseOp hp0 hp1, ptn_noiseOp_l2sq hp0 hp1]] at hldw
  rw [ptn_kop_deriv_l2sq hp0 hp1] at hldw
  rw [ptn_qnorm_deriv_sq hp0 hp1 (by linarith : (0:ℝ) < q)] at hldw
  exact hldw





theorem htl_summed_hc {p ρ q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (hqeq : q = 1 + ρ ^ 2) (H : PBiasedHCLib p)
    (φ : ConfigSpace ι → Bool) :
    (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset ι, (S.card : ℝ) * ((ρ ^ (S.card - 1)) ^ 2
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ ∑ e : ι, (OSSS.infl (OSSS.bernoulliWeight p)
          (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / q) := by
  set σ2 := (ptn_sigma p) ^ 2 with hσ2
  set cc := fun S : Finset ι => (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 with hcc
  have hσ2pos : 0 < σ2 := by rw [hσ2]; exact pow_pos (ptn_sigma_pos hp0 hp1) 2
  have hper : ∀ e : ι,
      (1 / σ2) * ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
          (ρ ^ (S.erase e).card) ^ 2 * cc S
        ≤ (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / q) := by
    intro e
    have h := htl_perCoord_hc hp0 hp1 h0 h1 hqeq H φ e
    refine le_trans (le_of_eq ?_) h
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
        (ρ ^ (S.erase e).card) ^ 2 * cc S)
      = ∑ S : Finset ι, (if e ∈ S then (ρ ^ (S.card - 1)) ^ 2 * cc S else 0) := by
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










theorem htl_capped_hc [Nonempty ι] {p ρ q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 ≤ ρ)
    (h1 : ρ ≤ 1) (hqeq : q = 1 + ρ ^ 2) (hq2 : q ≤ 2)
    (H : PBiasedHCLib p) (φ : ConfigSpace ι → Bool) :
    (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset ι, (S.card : ℝ) * ((ρ ^ (S.card - 1)) ^ 2
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / q - 1)
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  have hq1 : 1 ≤ q := by rw [hqeq]; nlinarith [sq_nonneg ρ]
  exact le_trans (htl_summed_hc hp0 hp1 h0 h1 hqeq H φ) (ptn_cap_sum hp0 hp1 hq1 hq2 φ)





















theorem htl_master_open [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (H : PBiasedHCLib p)
    (φ : ConfigSpace ι → Bool) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  set δ := maxInfl (OSSS.bernoulliWeight p) f with hδ
  set T := totalInfl (OSSS.bernoulliWeight p) f with hT
  set cc := fun S : Finset ι => (ptn_coeff p f S) ^ 2 with hcc
  have hu1' : (0:ℝ) ≤ 1 - u := by linarith
  set ρ := Real.sqrt (1 - u) with hρ
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ1 : ρ ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hρsq : ρ ^ 2 = 1 - u := Real.sq_sqrt hu1'
  set q := 2 - u with hq
  have hq1 : 1 ≤ q := by rw [hq]; linarith
  have hq2 : q ≤ 2 := by rw [hq]; linarith
  have hqpos : 0 < q := by rw [hq]; linarith
  
  have hqeq : q = 1 + ρ ^ 2 := by rw [hρsq, hq]; ring
  
  have hcap := htl_capped_hc hp0 hp1 hρ0 hρ1 hqeq hq2 H φ
  
  have hσ2sq : (0:ℝ) < (ptn_sigma p)^2 := pow_pos (ptn_sigma_pos hp0 hp1) 2
  have hσne : ptn_sigma p ≠ 0 := (ptn_sigma_pos hp0 hp1).ne'
  have hσ2val : (ptn_sigma p)^2 = p*(1-p) := ptn_sigma_sq hp0 hp1
  
  have h2u : (2 : ℝ) - u ≠ 0 := by intro h; rw [hq] at hqpos; linarith
  have hexp : 2 / q - 1 = u / (2 - u) := by
    rw [hq, div_sub_one h2u]; ring_nf
  
  have hpow : ∀ S : Finset ι, (ρ ^ (S.card - 1)) ^ 2 = (1 - u) ^ (S.card - 1) := by
    intro S; rw [← pow_mul, mul_comm, pow_mul, hρsq]
  have hLHS : (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * cc S)
      = 4 * (ptn_sigma p)^2 * ((1 / (ptn_sigma p) ^ 2)
          * ∑ S : Finset ι, (S.card : ℝ) * ((ρ ^ (S.card - 1)) ^ 2 * cc S)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    rw [hpow S]
    field_simp
  
  have h4σ : 4 * (ptn_sigma p)^2 ≤ 1 := by rw [hσ2val]; nlinarith [sq_nonneg (1 - 2*p)]
  have h4σnn : (0:ℝ) ≤ 4 * (ptn_sigma p)^2 := by positivity
  have hRHSnn : 0 ≤ δ ^ (2 / q - 1) * T := by
    apply mul_nonneg (Real.rpow_nonneg ?_ _)
    · exact kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) f
    · exact kkl_maxInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) f
  
  calc (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * cc S)
      = 4 * (ptn_sigma p)^2 * ((1 / (ptn_sigma p) ^ 2)
          * ∑ S : Finset ι, (S.card : ℝ) * ((ρ ^ (S.card - 1)) ^ 2 * cc S)) := hLHS
    _ ≤ 4 * (ptn_sigma p)^2 * (δ ^ (2 / q - 1) * T) :=
        mul_le_mul_of_nonneg_left hcap h4σnn
    _ ≤ 1 * (δ ^ (2 / q - 1) * T) := mul_le_mul_of_nonneg_right h4σ hRHSnn
    _ = δ ^ (u / (2 - u)) * T := by rw [one_mul, hexp]






theorem htl_openResidue_of_lib {q : ℝ}
    (H : ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, PBiasedHCLib p) :
    frh_openResidue q := by
  intro p hp hp1 E _ _ _ φ u hu0 hu1
  have hp0 : 0 < p := by have := hp.1; linarith
  exact htl_master_open hp0 hp1 (H p hp) φ hu0 hu1














theorem htl_kkl_logGain {q : ℝ} (H : ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, PBiasedHCLib p)
    {p : ℝ} (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool) :
    2 * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
          * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)))
        * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  vgp2_kkl_logGain_of_master (htl_openResidue_of_lib H) hp hp1 φ






theorem htl_rhoOptimise_of_lib {q : ℝ} (H : ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, PBiasedHCLib p) :
    ptn_RhoOptimise q :=
  mxd_rhoOptimise_of_martingaleHC (frh_martingaleHC_of_openResidue (htl_openResidue_of_lib H))



theorem htl_kklHC_of_lib {q : ℝ} (H : ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, PBiasedHCLib p)
    {p : ℝ} (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q) (hp1 : p < 1) :
    KKLHypercontractive p 2 :=
  ptn_kklHC_of_rhoOptimise (htl_rhoOptimise_of_lib H) hp hp1



theorem htl_PBiasedHC_of_lib {q : ℝ} (hq : q ≤ 1)
    (H : ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, PBiasedHCLib p) :
    kpb_PBiasedHC q :=
  ptn_PBiasedHC_of_rhoOptimise hq (htl_rhoOptimise_of_lib H)







theorem htl_sharpThreshold {q : ℝ} (hq1 : q ≤ 1)
    (H : ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, PBiasedHCLib p)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (A : Set (ConfigSpace E)) [DecidablePred (· ∈ A)] (hA : IsIncreasing A)
    {v₀ L : ℝ} (hq : (1 : ℝ) / 2 ≤ q) (hv0 : 0 ≤ v₀) (hL : 0 ≤ L)
    (hhalf : StatMech.prob (1 / 2) A = 1 / 2)
    (hvar : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      v₀ ≤ StatMech.prob p A * (1 - StatMech.prob p A))
    (hLL' : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      L ≤ StatMech.TwoDim.kklw_logMaxInfl p A) :
    1 / 2 + (2 * v₀ * L) * (q - 1 / 2) ≤ StatMech.prob q A :=
  ptn_sharpThreshold_of_rhoOptimise hq1 (htl_rhoOptimise_of_lib H) A hA hq hv0 hL hhalf hvar hLL'








theorem htl_kkl_logGain_half {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (φ : ConfigSpace ι → Bool) :
    2 * (OSSS.expect (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)
          * (1 - OSSS.expect (OSSS.bernoulliWeight (1 / 2 : ℝ))
              (fun ω => if φ ω then (1 : ℝ) else 0)))
        * Real.log (1 / maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ))
            (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  vgp2_kkl_logGain_half φ






theorem htl_lib_rho_zero {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (u v : ℝ) :
    ((1 - p) * u + p * v) ^ 2 + (0 : ℝ) ^ 2 * (p * (1 - p)) * (u - v) ^ 2
      ≤ ((1 - p) * |u| ^ (1 + (0:ℝ) ^ 2) + p * |v| ^ (1 + (0:ℝ) ^ 2)) ^ (2 / (1 + (0:ℝ) ^ 2)) := by
  have h1p : 0 ≤ 1 - p := by linarith
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero]
  rw [Real.rpow_one, Real.rpow_one, show (2 : ℝ) / 1 = 2 by norm_num,
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  
  have hbase : |(1 - p) * u + p * v| ≤ (1 - p) * |u| + p * |v| := by
    calc |(1 - p) * u + p * v| ≤ |(1 - p) * u| + |p * v| := abs_add_le _ _
      _ = (1 - p) * |u| + p * |v| := by
          rw [abs_mul, abs_mul, abs_of_nonneg h1p, abs_of_nonneg hp0]
  calc ((1 - p) * u + p * v) ^ 2 = |(1 - p) * u + p * v| ^ 2 := (sq_abs _).symm
    _ ≤ ((1 - p) * |u| + p * |v|) ^ 2 := by
        apply pow_le_pow_left₀ (abs_nonneg _) hbase








theorem htl_lib_noncirc {p : ℝ} (H : PBiasedHCLib p) {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (u v : ℝ) :
    ((1 - p) * u + p * v) ^ 2 + ρ ^ 2 * (p * (1 - p)) * (u - v) ^ 2
      ≤ ((1 - p) * |u| ^ (1 + ρ ^ 2) + p * |v| ^ (1 + ρ ^ 2)) ^ (2 / (1 + ρ ^ 2)) :=
  H ρ h0 h1 u v

end StatMech.Probability
