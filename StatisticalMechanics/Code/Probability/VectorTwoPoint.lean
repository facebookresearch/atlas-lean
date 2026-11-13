/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































import Code.Probability.BonamiTensorize
import Code.Probability.BonamiTwoPoint

open scoped BigOperators
open Finset

set_option linter.style.longLine false

namespace StatMech.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]





theorem vtp_uexp_add (g h : (ι → Bool) → ℝ) :
    bnt_uexp (fun ω => g ω + h ω) = bnt_uexp g + bnt_uexp h := by
  unfold bnt_uexp; rw [← add_div, Finset.sum_add_distrib]


theorem vtp_uexp_smul (c : ℝ) (g : (ι → Bool) → ℝ) :
    bnt_uexp (fun ω => c * g ω) = c * bnt_uexp g := by
  unfold bnt_uexp; rw [← Finset.mul_sum, mul_div_assoc]



theorem vtp_qnormPow2_eq_uexp_sq (f : (ι → Bool) → ℝ) :
    bnt_qnormPow 2 f = bnt_uexp (fun ω => (f ω) ^ 2) := by
  unfold bnt_qnormPow; congr 1; funext ω
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]



theorem vtp_qnorm2_eq_sqrt (u : (ι → Bool) → ℝ) :
    bnt_qnorm 2 u = Real.sqrt (bnt_qnormPow 2 u) := by
  unfold bnt_qnorm; rw [Real.sqrt_eq_rpow]



theorem vtp_qnorm2_sq (u : (ι → Bool) → ℝ) :
    (bnt_qnorm 2 u) ^ 2 = bnt_qnormPow 2 u := by
  rw [vtp_qnorm2_eq_sqrt, Real.sq_sqrt (bnt_qnormPow_nonneg 2 u)]








theorem vtp_qnormPow2_expand (a b : ℝ) (u v : (ι → Bool) → ℝ) :
    bnt_qnormPow 2 (fun ω => a * u ω + b * v ω)
      = a ^ 2 * bnt_uexp (fun ω => (u ω) ^ 2)
        + 2 * a * b * bnt_uexp (fun ω => u ω * v ω)
        + b ^ 2 * bnt_uexp (fun ω => (v ω) ^ 2) := by
  rw [vtp_qnormPow2_eq_uexp_sq]
  have heq : (fun ω => (a * u ω + b * v ω) ^ 2)
      = (fun ω => a ^ 2 * (u ω) ^ 2 + (2 * a * b) * (u ω * v ω) + b ^ 2 * (v ω) ^ 2) := by
    funext ω; ring
  rw [heq, vtp_uexp_add, vtp_uexp_add, vtp_uexp_smul, vtp_uexp_smul, vtp_uexp_smul]




theorem vtp_uexp_inner_le (u v : (ι → Bool) → ℝ) :
    bnt_uexp (fun ω => u ω * v ω) ≤ bnt_qnorm 2 u * bnt_qnorm 2 v := by
  rw [vtp_qnorm2_eq_sqrt, vtp_qnorm2_eq_sqrt, vtp_qnormPow2_eq_uexp_sq,
    vtp_qnormPow2_eq_uexp_sq]
  unfold bnt_uexp
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (univ : Finset (ι → Bool)) u v
  have hN : (0 : ℝ) < 2 ^ (Fintype.card ι) := by positivity
  have hsq1 : (0 : ℝ) ≤ ∑ ω : ι → Bool, (u ω) ^ 2 :=
    Finset.sum_nonneg (fun ω _ => sq_nonneg _)
  have hsq2 : (0 : ℝ) ≤ ∑ ω : ι → Bool, (v ω) ^ 2 :=
    Finset.sum_nonneg (fun ω _ => sq_nonneg _)
  simp only []
  rw [Real.sqrt_div hsq1, Real.sqrt_div hsq2, div_mul_div_comm, Real.mul_self_sqrt hN.le]
  exact (div_le_div_iff_of_pos_right hN).mpr hcs













theorem vtp_vectorTwoPoint_aux {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (n : ℕ) (u v : (Fin n → Bool) → ℝ) :
    (bnt_qnormPow 2 (fun ω => (1 + ρ) / 2 * u ω + (1 - ρ) / 2 * v ω)
        + bnt_qnormPow 2 (fun ω => (1 - ρ) / 2 * u ω + (1 + ρ) / 2 * v ω)) / 2
      ≤ ((bnt_qnorm 2 u ^ (1 + ρ ^ 2) + bnt_qnorm 2 v ^ (1 + ρ ^ 2)) / 2) ^ (2 / (1 + ρ ^ 2)) := by
  
  set p := bnt_qnorm 2 u with hp
  set s := bnt_qnorm 2 v with hs
  have hpnn : 0 ≤ p := bnt_qnorm_nonneg 2 u
  have hsnn : 0 ≤ s := bnt_qnorm_nonneg 2 v
  set Eu := bnt_uexp (fun ω : Fin n → Bool => (u ω) ^ 2) with hEu
  set Ev := bnt_uexp (fun ω : Fin n → Bool => (v ω) ^ 2) with hEv
  set Euv := bnt_uexp (fun ω : Fin n → Bool => u ω * v ω) with hEuv
  have hp2 : p ^ 2 = Eu := by rw [hp, vtp_qnorm2_sq, vtp_qnormPow2_eq_uexp_sq]
  have hs2 : s ^ 2 = Ev := by rw [hs, vtp_qnorm2_sq, vtp_qnormPow2_eq_uexp_sq]
  
  have hexp1 := vtp_qnormPow2_expand ((1 + ρ) / 2) ((1 - ρ) / 2) u v
  have hexp2 := vtp_qnormPow2_expand ((1 - ρ) / 2) ((1 + ρ) / 2) u v
  rw [← hEu, ← hEv, ← hEuv] at hexp1 hexp2
  
  have hLHS : (bnt_qnormPow 2 (fun ω => (1 + ρ) / 2 * u ω + (1 - ρ) / 2 * v ω)
        + bnt_qnormPow 2 (fun ω => (1 - ρ) / 2 * u ω + (1 + ρ) / 2 * v ω)) / 2
      = (1 / 2) * (((1 + ρ) / 2) ^ 2 + ((1 - ρ) / 2) ^ 2) * (Eu + Ev)
        + 2 * ((1 + ρ) / 2) * ((1 - ρ) / 2) * Euv := by
    rw [hexp1, hexp2]; ring
  rw [hLHS]
  
  have hCS : Euv ≤ p * s := vtp_uexp_inner_le u v
  have hcoef : 0 ≤ 2 * ((1 + ρ) / 2) * ((1 - ρ) / 2) := by nlinarith
  have hbound : (1 / 2) * (((1 + ρ) / 2) ^ 2 + ((1 - ρ) / 2) ^ 2) * (Eu + Ev)
        + 2 * ((1 + ρ) / 2) * ((1 - ρ) / 2) * Euv
      ≤ (1 / 2) * (((1 + ρ) / 2) ^ 2 + ((1 - ρ) / 2) ^ 2) * (p ^ 2 + s ^ 2)
        + 2 * ((1 + ρ) / 2) * ((1 - ρ) / 2) * (p * s) := by
    rw [hp2, hs2]
    have := mul_le_mul_of_nonneg_left hCS hcoef
    linarith
  
  have halg : (1 / 2) * (((1 + ρ) / 2) ^ 2 + ((1 - ρ) / 2) ^ 2) * (p ^ 2 + s ^ 2)
        + 2 * ((1 + ρ) / 2) * ((1 - ρ) / 2) * (p * s)
      = ((p + s) / 2) ^ 2 + ρ ^ 2 * ((p - s) / 2) ^ 2 := by ring
  
  have key := bts_twoPointScalar h0 h1 ((p + s) / 2) ((p - s) / 2)
  have e1 : (p + s) / 2 + (p - s) / 2 = p := by ring
  have e2 : (p + s) / 2 - (p - s) / 2 = s := by ring
  rw [e1, e2, abs_of_nonneg hpnn, abs_of_nonneg hsnn] at key
  
  calc (1 / 2) * (((1 + ρ) / 2) ^ 2 + ((1 - ρ) / 2) ^ 2) * (Eu + Ev)
        + 2 * ((1 + ρ) / 2) * ((1 - ρ) / 2) * Euv
      ≤ ((p + s) / 2) ^ 2 + ρ ^ 2 * ((p - s) / 2) ^ 2 := by rw [← halg]; exact hbound
    _ ≤ ((p ^ (1 + ρ ^ 2) + s ^ (1 + ρ ^ 2)) / 2) ^ (2 / (1 + ρ ^ 2)) := key












theorem vtp_vectorTwoPoint {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    bnt_VectorTwoPoint ρ :=
  fun n u v => vtp_vectorTwoPoint_aux h0 h1 n u v












theorem vtp_hypercontractivity {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (n : ℕ) (f : (Fin n → Bool) → ℝ) :
    bnt_qnorm 2 (bnt_noiseOp ρ f) ≤ bnt_qnorm (1 + ρ ^ 2) f :=
  bnt_hypercontractivity (vtp_vectorTwoPoint h0 h1) n f

end StatMech.Probability
