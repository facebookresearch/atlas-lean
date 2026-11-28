/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.FiniteEntropy
public import Mathlib.Data.EReal.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Jensen–Shannon divergence against a point mass

For a finite probability mass function `p`, the Jensen–Shannon divergence in bits from `p`
to a point mass at `j` depends only on `p j`. The divergence decreases strictly from one to
zero as this mass increases; its negative base-ten logarithm orders profiles by their mass
at `j`, with infinite score at unit mass.

Reddy et al., *Science Advances* 7 (2021), eabf6123, Methods ("The CaCTS algorithm"), use
the negative logarithm of this divergence as a specificity score. The formulas here concern
the exact point mass, without the pseudocounts used in that application.
-/

@[expose] public section

namespace InformationTheory

open Finset MeasureTheory Real
open scoped ENNReal

variable {α : Type*} [Fintype α]

/-- The equally weighted mixture of two probability mass functions on a finite type. -/
noncomputable def midpointPMF (p q : PMF α) : PMF α :=
  PMF.ofFintype (fun a => (p a + q a) * (2 : ℝ≥0∞)⁻¹) (by
    have hp : ∑ a, p a = 1 := by simpa only [tsum_fintype] using p.tsum_coe
    have hq : ∑ a, q a = 1 := by simpa only [tsum_fintype] using q.tsum_coe
    rw [← sum_mul, sum_add_distrib, hp, hq]
    simpa only [one_add_one_eq_two] using
      (ENNReal.mul_inv_cancel (a := 2) (by norm_num) (by simp)))

private theorem midpointPMF_real (p q : PMF α) (a : α) :
    (midpointPMF p q a).toReal = ((p a).toReal + (q a).toReal) / 2 := by
  simp [midpointPMF, ENNReal.toReal_add (p.apply_ne_top a) (q.apply_ne_top a), div_eq_mul_inv]

private theorem left_midpointPMF_support (p q : PMF α) (a : α)
    (h : midpointPMF p q a = 0) : p a = 0 := by
  have hz : (p a + q a) * (2 : ℝ≥0∞)⁻¹ = 0 := h
  rcases mul_eq_zero.mp hz with hsum | hinv
  · exact (add_eq_zero.mp hsum).1
  · exact False.elim (by norm_num at hinv)

private theorem right_midpointPMF_support (p q : PMF α) (a : α)
    (h : midpointPMF p q a = 0) : q a = 0 := by
  have h' : midpointPMF q p a = 0 := by
    simpa only [midpointPMF, PMF.ofFintype_apply, add_comm (q a) (p a)] using h
  exact left_midpointPMF_support q p a h'

/-- Jensen–Shannon divergence in bits on a finite type with measurable singletons: the average
of the two Kullback–Leibler divergences to the equally weighted mixture, converted from nats
by dividing by `Real.log 2`. Both divergences are finite since the mixture dominates each
law. -/
noncomputable def jensenShannonBits [MeasurableSpace α] [MeasurableSingletonClass α]
    (p q : PMF α) : ℝ :=
  let m := (midpointPMF p q).toMeasure
  ((klDiv p.toMeasure m).toReal + (klDiv q.toMeasure m).toReal) / (2 * log 2)

/-- The one-hot Jensen–Shannon divergence in bits as a function of the mass `x` at the selected
outcome. This is `1 + (x * log x - (1 + x) * log (1 + x)) / (2 * log 2)`, with the zero term
interpreted as zero. -/
noncomputable def oneHotJensenShannon (x : ℝ) : ℝ :=
  1 + (negMulLog (1 + x) - negMulLog x) / (2 * log 2)

private theorem pmf_sum_real (p : PMF α) : ∑ a, (p a).toReal = 1 := by
  have hs : ∑ a, p a = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  rw [← ENNReal.toReal_sum (fun a _ => p.apply_ne_top a), hs]
  simp

/-- For a finite probability mass function `p` on a type with measurable singletons and a
selected outcome `j`, the Jensen–Shannon divergence in bits from `p` to the point mass at `j`
is `oneHotJensenShannon (p j).toReal`. Only the selected mass matters. -/
theorem jensenShannonBits_pure [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : PMF α) (j : α) : jensenShannonBits p (PMF.pure j) = oneHotJensenShannon (p j).toReal := by
  classical
  let q : PMF α := PMF.pure j
  let m : PMF α := midpointPMF p q
  change ((klDiv p.toMeasure m.toMeasure).toReal + (klDiv q.toMeasure m.toMeasure).toReal) /
    (2 * log 2) = _
  rw [toReal_klDiv_toMeasure (left_midpointPMF_support p q),
    toReal_klDiv_toMeasure (right_midpointPMF_support p q)]
  let x := (p j).toReal
  have h0 : 0 ≤ x := ENNReal.toReal_nonneg
  have hpos : 0 < 1 + x := by linarith
  have hmj : (m j).toReal = (1 + x) / 2 := by
    simp [m, q, x, midpointPMF_real, add_comm]
  have hqj : (q j).toReal = 1 := by simp [q]
  have hqother (a : α) (ha : a ≠ j) : (q a).toReal = 0 := by
    simp [q, ha]
  have hpother (a : α) (ha : a ≠ j) :
      (p a).toReal * log ((p a).toReal / (m a).toReal) = (p a).toReal * log 2 := by
    have hm : (m a).toReal = (p a).toReal / 2 := by
      simp [m, midpointPMF_real, hqother a ha]
    rw [hm]
    by_cases hp : (p a).toReal = 0
    · simp [hp]
    · have hr : (p a).toReal / ((p a).toReal / 2) = 2 := by field_simp
      rw [hr]
  have hrest : ∑ a ∈ univ.erase j, (p a).toReal = 1 - x := by
    have h := sum_erase_add (s := univ) (fun a => (p a).toReal) (mem_univ j)
    rw [pmf_sum_real] at h
    linarith
  have hp_sum : ∑ a, (p a).toReal * log ((p a).toReal / (m a).toReal) =
      (1 - x) * log 2 + x * log (x / ((1 + x) / 2)) := by
    rw [← sum_erase_add _ _ (mem_univ j)]
    congr 1
    · rw [← hrest, sum_mul]
      exact sum_congr rfl fun a ha => hpother a (mem_erase.mp ha).1
    · rw [hmj]
  have hq_sum : ∑ a, (q a).toReal * log ((q a).toReal / (m a).toReal) =
      log (1 / ((1 + x) / 2)) := by
    rw [sum_eq_single j, hqj, hmj, one_mul]
    · intro a _ ha
      simp [hqother a ha]
    · simp
  have hq_log : log (1 / ((1 + x) / 2)) = log 2 - log (1 + x) := by
    rw [one_div_div, log_div (by norm_num : (2 : ℝ) ≠ 0) hpos.ne']
  have hp_log : x * log (x / ((1 + x) / 2)) =
      x * log 2 + x * log x - x * log (1 + x) := by
    by_cases hx : x = 0
    · simp [hx]
    · rw [div_div_eq_mul_div, log_div (mul_ne_zero hx (by norm_num)) hpos.ne',
        log_mul hx (by norm_num)]
      ring
  rw [hp_sum, hq_sum, hp_log, hq_log]
  change _ = oneHotJensenShannon x
  simp only [oneHotJensenShannon, negMulLog_eq_neg]
  have hlog : log (2 : ℝ) ≠ 0 := (log_pos (by norm_num)).ne'
  field_simp
  ring

/-- On the full interval of possible masses `[0, 1]`, the one-hot Jensen–Shannon divergence
in bits decreases strictly. The proof differentiates in the interior and uses continuity at
zero, where the derivative formula is not valid. -/
theorem strictAntiOn_oneHotJensenShannon : StrictAntiOn oneHotJensenShannon (Set.Icc 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 1)
  · unfold oneHotJensenShannon
    fun_prop
  · intro x hx
    rw [interior_Icc] at hx
    have hpos : 0 < x := hx.1
    have hpos' : 0 < 1 + x := by linarith
    have hlog : 0 < log (2 : ℝ) := log_pos (by norm_num)
    have hderiv : HasDerivAt oneHotJensenShannon
        ((log x - log (1 + x)) / (2 * log 2)) x := by
      have hshift : HasDerivAt (fun t : ℝ => 1 + t) 1 x :=
        (hasDerivAt_id x).const_add 1
      have hd := ((hasDerivAt_const x (1 : ℝ)).add
        ((((hasDerivAt_negMulLog hpos'.ne').comp x hshift).sub
          (hasDerivAt_negMulLog hpos.ne')).div_const (2 * log 2)))
      convert hd using 1
      · rfl
      · ring
    rw [hderiv.deriv]
    exact div_neg_of_neg_of_pos (sub_neg.mpr (log_lt_log hpos (by linarith)))
      (mul_pos (by norm_num : (0 : ℝ) < 2) hlog)

/-- Zero mass at the selected outcome gives one bit of Jensen–Shannon divergence. -/
@[simp] theorem oneHotJensenShannon_zero : oneHotJensenShannon 0 = 1 := by
  simp [oneHotJensenShannon]

/-- Unit mass at the selected outcome gives zero Jensen–Shannon divergence. -/
@[simp] theorem oneHotJensenShannon_one : oneHotJensenShannon 1 = 0 := by
  unfold oneHotJensenShannon
  norm_num [negMulLog, show (1 : ℝ) + 1 = 2 by norm_num]

/-- One-hot specificity for a mass `x` is the negative base-ten logarithm of the divergence.
It takes the value `⊤` at zero divergence, rather than the totalized real logarithm's value. -/
noncomputable def oneHotSpecificity (x : ℝ) : EReal :=
  if oneHotJensenShannon x = 0 then ⊤ else ((-logb 10 (oneHotJensenShannon x) : ℝ) : EReal)

/-- Among masses in `[0, 1]`, only unit mass has infinite one-hot specificity. -/
theorem oneHotSpecificity_eq_top_iff {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    oneHotSpecificity x = ⊤ ↔ x = 1 := by
  have hzero : oneHotJensenShannon x = 0 ↔ x = 1 := by
    constructor
    · intro h
      exact strictAntiOn_oneHotJensenShannon.injOn hx (by simp)
        (h.trans oneHotJensenShannon_one.symm)
    · rintro rfl
      exact oneHotJensenShannon_one
  simp [oneHotSpecificity, hzero]

/-- On the interval `[0, 1]`, the one-hot specificity score ranks profiles by their mass at
the selected outcome, with the infinite endpoint above every finite score. -/
theorem strictMonoOn_oneHotSpecificity : StrictMonoOn oneHotSpecificity (Set.Icc 0 1) := by
  intro x hx y hy hxy
  have hpos {z : ℝ} (hz : z ∈ Set.Icc 0 1) (hz' : z < 1) : 0 < oneHotJensenShannon z := by
    simpa only [oneHotJensenShannon_one] using strictAntiOn_oneHotJensenShannon hz (by simp) hz'
  have hxpos := hpos hx (hxy.trans_le hy.2)
  by_cases hey : y = 1
  · rw [hey, (oneHotSpecificity_eq_top_iff (x := 1) (by simp)).2 rfl,
      oneHotSpecificity, ite_eq_right hxpos.ne']
    exact EReal.coe_lt_top _
  · have hypos := hpos hy (lt_of_le_of_ne hy.2 hey)
    rw [oneHotSpecificity, ite_eq_right hxpos.ne', oneHotSpecificity, ite_eq_right hypos.ne',
      EReal.coe_lt_coe_iff]
    exact neg_lt_neg (logb_lt_logb (by norm_num) hypos (strictAntiOn_oneHotJensenShannon hx hy hxy))

end InformationTheory
