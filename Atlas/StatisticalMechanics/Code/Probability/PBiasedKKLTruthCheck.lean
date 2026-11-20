/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




























import Code.Probability.SummedBKKKLClose

open scoped BigOperators
open Finset Real Set

set_option linter.style.longLine false

namespace StatMech.Probability

open StatMech StatMech.OSSS




theorem pbkt_OR_expect (p : ℝ) :
    OSSS.expect (OSSS.bernoulliWeight p) ctp_f = 1 - (1 - p) ^ 2 := by
  rw [ctp_expect_fin2]
  simp only [ctp_f_ff, ctp_f_ft, ctp_f_tf, ctp_f_tt]
  ring



theorem pbkt_OR_var (p : ℝ) :
    OSSS.var (OSSS.bernoulliWeight p) ctp_f =
      (1 - (1 - p) ^ 2) * (1 - p) ^ 2 := by
  have h := mil_var_eq (p := p) ctp_OR
  change OSSS.var (OSSS.bernoulliWeight p) ctp_f = _ at h
  have hf : (fun ω => if ctp_OR ω then (1 : ℝ) else 0) = ctp_f := rfl
  rw [hf] at h
  rw [pbkt_OR_expect] at h
  nlinarith


theorem pbkt_OR_infl0 (p : ℝ) :
    OSSS.infl (OSSS.bernoulliWeight p) ctp_f 0 = 1 - p := by
  unfold OSSS.infl
  rw [ctp_expect_fin2]
  have hopen : ∀ a b : Bool, StatMech.setOpen 0 (ctp_cfg a b) = ctp_cfg true b := by
    intro a b
    funext i
    fin_cases i <;> simp [StatMech.setOpen, ctp_cfg, Function.update]
  have hclosed : ∀ a b : Bool, StatMech.setClosed 0 (ctp_cfg a b) = ctp_cfg false b := by
    intro a b
    funext i
    fin_cases i <;> simp [StatMech.setClosed, ctp_cfg, Function.update]
  simp only [hopen, hclosed, ctp_f_ff, ctp_f_ft, ctp_f_tf, ctp_f_tt]
  ring


theorem pbkt_OR_infl1 (p : ℝ) :
    OSSS.infl (OSSS.bernoulliWeight p) ctp_f 1 = 1 - p := by
  unfold OSSS.infl
  rw [ctp_expect_fin2]
  have hopen : ∀ a b : Bool, StatMech.setOpen 1 (ctp_cfg a b) = ctp_cfg a true := by
    intro a b
    funext i
    fin_cases i <;> simp [StatMech.setOpen, ctp_cfg, Function.update]
  have hclosed : ∀ a b : Bool, StatMech.setClosed 1 (ctp_cfg a b) = ctp_cfg a false := by
    intro a b
    funext i
    fin_cases i <;> simp [StatMech.setClosed, ctp_cfg, Function.update]
  simp only [hopen, hclosed, ctp_f_ff, ctp_f_ft, ctp_f_tf, ctp_f_tt]
  ring


theorem pbkt_OR_totalInfl (p : ℝ) :
    totalInfl (OSSS.bernoulliWeight p) ctp_f = 2 * (1 - p) := by
  unfold totalInfl
  rw [Fin.sum_univ_two, pbkt_OR_infl0, pbkt_OR_infl1]
  ring


theorem pbkt_OR_maxInfl (p : ℝ) :
    maxInfl (OSSS.bernoulliWeight p) ctp_f = 1 - p := by
  unfold maxInfl
  have hfun : OSSS.infl (OSSS.bernoulliWeight p) ctp_f = fun _ => 1 - p := by
    funext e
    fin_cases e
    · exact pbkt_OR_infl0 p
    · exact pbkt_OR_infl1 p
  rw [hfun]
  simp [Finset.sup'_const]







theorem pbkt_twoBit_atom_numeric {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    2 * ((1 - x ^ 2) * x ^ 2) * Real.log (1 / x) ≤ 2 * x := by
  have hinv : 0 < 1 / x := by positivity
  have hlog := Real.log_le_sub_one_of_pos hinv
  have hxlog : x * Real.log (1 / x) ≤ 1 - x := by
    calc
      x * Real.log (1 / x) ≤ x * (1 / x - 1) :=
        mul_le_mul_of_nonneg_left hlog hx0.le
      _ = 1 - x := by field_simp [hx0.ne']
  have hlog0 : 0 ≤ Real.log (1 / x) := by
    apply Real.log_nonneg
    exact (one_le_div hx0).2 hx1.le
  have hxlog0 : 0 ≤ x * Real.log (1 / x) := mul_nonneg hx0.le hlog0
  have hxlog1 : x * Real.log (1 / x) ≤ 1 := by linarith [hxlog]
  have hcoef1 : 1 - x ^ 2 ≤ 1 := by nlinarith
  have hproduct : (1 - x ^ 2) * (x * Real.log (1 / x)) ≤ 1 := by
    calc
      (1 - x ^ 2) * (x * Real.log (1 / x))
          ≤ 1 * (x * Real.log (1 / x)) :=
        mul_le_mul_of_nonneg_right hcoef1 hxlog0
      _ ≤ 1 := by simpa using hxlog1
  have hscale := mul_le_mul_of_nonneg_left hproduct (show 0 ≤ 2 * x by positivity)
  calc
    2 * ((1 - x ^ 2) * x ^ 2) * Real.log (1 / x) =
        2 * x * ((1 - x ^ 2) * (x * Real.log (1 / x))) := by ring
    _ ≤ 2 * x * 1 := hscale
    _ = 2 * x := by ring







theorem pbkt_OR_kkl_two {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    2 * OSSS.var (OSSS.bernoulliWeight p) ctp_f
        * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) ctp_f)
      ≤ totalInfl (OSSS.bernoulliWeight p) ctp_f := by
  rw [pbkt_OR_var, pbkt_OR_maxInfl, pbkt_OR_totalInfl]
  exact pbkt_twoBit_atom_numeric (by linarith) (by linarith)




def pbkt_AND : ConfigSpace (Fin 2) → Bool := fun ω => ω 0 && ω 1


noncomputable def pbkt_andF : ConfigSpace (Fin 2) → ℝ :=
  fun ω => if pbkt_AND ω then 1 else 0

@[simp] theorem pbkt_andF_ff : pbkt_andF (ctp_cfg false false) = 0 := by
  simp [pbkt_andF, pbkt_AND, ctp_cfg]

@[simp] theorem pbkt_andF_ft : pbkt_andF (ctp_cfg false true) = 0 := by
  simp [pbkt_andF, pbkt_AND, ctp_cfg]

@[simp] theorem pbkt_andF_tf : pbkt_andF (ctp_cfg true false) = 0 := by
  simp [pbkt_andF, pbkt_AND, ctp_cfg]

@[simp] theorem pbkt_andF_tt : pbkt_andF (ctp_cfg true true) = 1 := by
  simp [pbkt_andF, pbkt_AND, ctp_cfg]


theorem pbkt_AND_expect (p : ℝ) :
    OSSS.expect (OSSS.bernoulliWeight p) pbkt_andF = p ^ 2 := by
  rw [ctp_expect_fin2]
  simp only [pbkt_andF_ff, pbkt_andF_ft, pbkt_andF_tf, pbkt_andF_tt]
  ring


theorem pbkt_AND_var (p : ℝ) :
    OSSS.var (OSSS.bernoulliWeight p) pbkt_andF = (1 - p ^ 2) * p ^ 2 := by
  have h := mil_var_eq (p := p) pbkt_AND
  change OSSS.var (OSSS.bernoulliWeight p) pbkt_andF = _ at h
  have hf : (fun ω => if pbkt_AND ω then (1 : ℝ) else 0) = pbkt_andF := rfl
  rw [hf, pbkt_AND_expect] at h
  nlinarith


theorem pbkt_AND_infl0 (p : ℝ) :
    OSSS.infl (OSSS.bernoulliWeight p) pbkt_andF 0 = p := by
  unfold OSSS.infl
  rw [ctp_expect_fin2]
  have hopen : ∀ a b : Bool, StatMech.setOpen 0 (ctp_cfg a b) = ctp_cfg true b := by
    intro a b
    funext i
    fin_cases i <;> simp [StatMech.setOpen, ctp_cfg, Function.update]
  have hclosed : ∀ a b : Bool, StatMech.setClosed 0 (ctp_cfg a b) = ctp_cfg false b := by
    intro a b
    funext i
    fin_cases i <;> simp [StatMech.setClosed, ctp_cfg, Function.update]
  simp only [hopen, hclosed, pbkt_andF_ff, pbkt_andF_ft, pbkt_andF_tf, pbkt_andF_tt]
  ring


theorem pbkt_AND_infl1 (p : ℝ) :
    OSSS.infl (OSSS.bernoulliWeight p) pbkt_andF 1 = p := by
  unfold OSSS.infl
  rw [ctp_expect_fin2]
  have hopen : ∀ a b : Bool, StatMech.setOpen 1 (ctp_cfg a b) = ctp_cfg a true := by
    intro a b
    funext i
    fin_cases i <;> simp [StatMech.setOpen, ctp_cfg, Function.update]
  have hclosed : ∀ a b : Bool, StatMech.setClosed 1 (ctp_cfg a b) = ctp_cfg a false := by
    intro a b
    funext i
    fin_cases i <;> simp [StatMech.setClosed, ctp_cfg, Function.update]
  simp only [hopen, hclosed, pbkt_andF_ff, pbkt_andF_ft, pbkt_andF_tf, pbkt_andF_tt]
  ring


theorem pbkt_AND_totalInfl (p : ℝ) :
    totalInfl (OSSS.bernoulliWeight p) pbkt_andF = 2 * p := by
  unfold totalInfl
  rw [Fin.sum_univ_two, pbkt_AND_infl0, pbkt_AND_infl1]
  ring


theorem pbkt_AND_maxInfl (p : ℝ) :
    maxInfl (OSSS.bernoulliWeight p) pbkt_andF = p := by
  unfold maxInfl
  have hfun : OSSS.infl (OSSS.bernoulliWeight p) pbkt_andF = fun _ => p := by
    funext e
    fin_cases e
    · exact pbkt_AND_infl0 p
    · exact pbkt_AND_infl1 p
  rw [hfun]
  simp [Finset.sup'_const]



theorem pbkt_AND_kkl_two {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    2 * OSSS.var (OSSS.bernoulliWeight p) pbkt_andF
        * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) pbkt_andF)
      ≤ totalInfl (OSSS.bernoulliWeight p) pbkt_andF := by
  rw [pbkt_AND_var, pbkt_AND_maxInfl, pbkt_AND_totalInfl]
  exact pbkt_twoBit_atom_numeric hp0 hp1



theorem pbkt_dictator_kkl_two {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    2 * OSSS.var (OSSS.bernoulliWeight p)
          (fun ω : ConfigSpace (Fin 1) => if ω 0 then (1 : ℝ) else 0)
        * Real.log (1 / maxInfl (OSSS.bernoulliWeight p)
          (fun ω : ConfigSpace (Fin 1) => if ω 0 then (1 : ℝ) else 0))
      ≤ totalInfl (OSSS.bernoulliWeight p)
          (fun ω : ConfigSpace (Fin 1) => if ω 0 then (1 : ℝ) else 0) := by
  rw [vgp_dictator_var hp0 hp1, vgp_dictator_maxInfl hp0 hp1,
    vgp_dictator_totalInfl hp0 hp1]
  norm_num

end StatMech.Probability
