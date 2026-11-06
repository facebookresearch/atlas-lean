/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.MeasureTheory.Function.LpSeminorm.Count
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

@[expose] public section

section
open MeasureTheory

namespace MathlibExt.Analysis.FunctionalAnalysis.RieszThorinWanted

private lemma holder_conj {q : ENNReal} (hq : 1 ≤ q) :
    ∃ q' : ENNReal, q⁻¹ + q'⁻¹ = 1 := by
  refine ⟨(1 - q⁻¹)⁻¹, ?_⟩
  rw [inv_inv]
  have hle : q⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr hq
  exact add_tsub_cancel_of_le hle

private lemma eLpNorm_count_eq_zero_iff {α : Type*} [Finite α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {r : ENNReal} (hr : r ≠ 0) (y : α → Complex) :
    eLpNorm y r Measure.count = 0 ↔ y = 0 := by
  have := Fintype.ofFinite α
  rw [eLpNorm_eq_zero_iff hr]
  constructor
  · intro h; funext i; exact Measure.ae_count_iff.mp h i
  · intro h; exact Measure.ae_count_iff.mpr (fun i => by simp [h])

private lemma enorm_complex_eq_ofReal (z : Complex) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  rw [enorm_eq_nnnorm, ← coe_nnnorm z, ENNReal.ofReal_coe_nnreal]

private lemma aemeas_count {α : Type*} [MeasurableSpace α] (y : α → Complex)
    [Finite α] [MeasurableSingletonClass α] :
    AEStronglyMeasurable y Measure.count :=
  (measurable_of_finite y).aestronglyMeasurable

private lemma eLpNorm_count_ne_top {α : Type*} [Finite α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (y : α → Complex) {r : ENNReal} (hr : r ≠ 0) :
    eLpNorm y r Measure.count ≠ ⊤ := by
  have := Fintype.ofFinite α
  have hlt : eLpNorm y r Measure.count < ⊤ := by
    rw [eLpNorm_count_lt_top hr]
    intro i
    exact lt_top_iff_ne_top.mpr enorm_ne_top
  exact ne_of_lt hlt

private lemma eLpNorm_count_eq_sum {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (y : α → Complex) {r : ENNReal}
    (hr0 : r ≠ 0) (hrt : r ≠ ⊤) :
    eLpNorm y r Measure.count = (∑ i, ‖y i‖ₑ ^ r.toReal) ^ (1 / r.toReal) := by
  have hmeas : AEStronglyMeasurable y Measure.count := aemeas_count y
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 hrt hmeas, lintegral_count,
    tsum_fintype]

private lemma eLpNorm_count_one_eq {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (y : α → Complex) :
    eLpNorm y 1 Measure.count = ∑ i, ‖y i‖ₑ := by
  have hmeas : AEStronglyMeasurable y Measure.count := aemeas_count y
  rw [eLpNorm_one_eq_lintegral_enorm hmeas, lintegral_count, tsum_fintype]

private lemma eLpNorm_count_top_eq {α : Type*} [Finite α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (y : α → Complex) :
    eLpNorm y ⊤ Measure.count = ⨆ i, ‖y i‖ₑ := by
  have := Fintype.ofFinite α
  have hmeas : AEStronglyMeasurable y Measure.count := aemeas_count y
  rw [eLpNorm_exponent_top hmeas, eLpNormEssSup_count]

private lemma q_ge_one_of_conj {q q' : ENNReal} (hq : q⁻¹ + q'⁻¹ = 1) :
    1 ≤ q := by
  have h : q⁻¹ ≤ q⁻¹ + q'⁻¹ := le_add_right le_rfl
  rw [hq] at h
  exact ENNReal.inv_le_one.mp h

private lemma q'_ne_zero_of_conj {q q' : ENNReal} (hq : q⁻¹ + q'⁻¹ = 1) :
    q' ≠ 0 := by
  rintro rfl
  rw [ENNReal.inv_zero, add_top] at hq
  exact (by simp : (⊤ : ENNReal) ≠ 1) hq

private lemma pairing_le {κ : Type*} [Fintype κ] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] (y g : κ → Complex) {q q' : ENNReal}
    (hq : q⁻¹ + q'⁻¹ = 1) :
    ‖∑ k, y k * g k‖ₑ ≤
      eLpNorm y q Measure.count * eLpNorm g q' Measure.count := by
  have hq1 : 1 ≤ q := q_ge_one_of_conj hq
  have hq'0 : q' ≠ 0 := q'_ne_zero_of_conj hq
  have hq0 : q ≠ 0 := ne_of_gt (one_pos.trans_le hq1)
  calc ‖∑ k, y k * g k‖ₑ ≤ ∑ k, ‖y k‖ₑ * ‖g k‖ₑ := by
        calc ‖∑ k, y k * g k‖ₑ ≤ ∑ k, ‖y k * g k‖ₑ :=
              enorm_sum_le Finset.univ _
          _ = ∑ k, ‖y k‖ₑ * ‖g k‖ₑ := by
              apply Finset.sum_congr rfl; intro k _
              exact enorm_mul _ _
    _ ≤ eLpNorm y q Measure.count * eLpNorm g q' Measure.count := by
        rcases eq_or_ne q 1 with rfl | hq1ne
        · rw [eLpNorm_count_one_eq, Finset.sum_mul]
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_right (enorm_le_eLpNorm_count g i hq'0) _
        · rcases eq_or_ne q ⊤ with rfl | hqtop
          · have hq'inv1 : q'⁻¹ = 1 := by simpa using hq
            have hq'1 : q' = 1 := by
              have h2 := congrArg Inv.inv hq'inv1
              rwa [inv_inv, inv_one] at h2
            rw [hq'1, eLpNorm_count_top_eq, eLpNorm_count_one_eq, Finset.mul_sum]
            apply Finset.sum_le_sum
            intro i _
            exact mul_le_mul_left (le_iSup (fun j => ‖y j‖ₑ) i) _
          · have hq1lt : 1 < q := lt_of_le_of_ne hq1 (Ne.symm hq1ne)
            have h1r : 1 < q.toReal := by
              have h := (ENNReal.toReal_lt_toReal (by simp : (1 : ENNReal) ≠ ⊤) hqtop).mpr hq1lt
              rwa [ENNReal.toReal_one] at h
            have hsum : (q.toReal)⁻¹ + (q'.toReal)⁻¹ = 1 := by
              have h := congrArg ENNReal.toReal hq
              rw [ENNReal.toReal_add (ENNReal.inv_ne_top.mpr hq0)
                (ENNReal.inv_ne_top.mpr hq'0), ENNReal.toReal_inv,
                ENNReal.toReal_inv, ENNReal.toReal_one] at h
              exact h
            have hq'top : q' ≠ ⊤ := by
              rintro rfl
              rw [ENNReal.toReal_top, inv_zero, add_zero] at hsum
              have h1 : q.toReal = 1 := by
                have h2 := congrArg Inv.inv hsum
                rwa [inv_inv, inv_one] at h2
              linarith
            have hconj : q.toReal.HolderConjugate q'.toReal := by
              rw [Real.holderConjugate_iff]
              exact ⟨h1r, hsum⟩
            have hH := ENNReal.inner_le_Lp_mul_Lq Finset.univ
              (fun i => ‖y i‖ₑ) (fun i => ‖g i‖ₑ) hconj
            rw [eLpNorm_count_eq_sum y hq0 hqtop,
              eLpNorm_count_eq_sum g hq'0 hq'top]
            simpa using hH

private noncomputable def sgn {κ : Type*} (y : κ → Complex) (i : κ) : Complex :=
  if y i = 0 then 0 else (starRingEnd ℂ) (y i) / (‖y i‖ : ℂ)

private lemma sgn_mul {κ : Type*} (y : κ → Complex) (i : κ) :
    y i * sgn y i = (‖y i‖ : ℂ) := by
  unfold sgn
  by_cases h : y i = 0
  · simp [h]
  · rw [ite_eq_right h]
    have hn : ‖y i‖ ≠ 0 := fun e => h (norm_eq_zero.mp e)
    have hC : ((‖y i‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [← mul_div_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.ofReal_pow, pow_two, mul_div_cancel_left₀ _ hC]

private lemma norm_sgn {κ : Type*} (y : κ → Complex) (i : κ) :
    ‖sgn y i‖ = if y i = 0 then 0 else 1 := by
  unfold sgn
  by_cases h : y i = 0
  · simp [h]
  · rw [ite_eq_right h, norm_div, Complex.norm_conj, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Complex.norm_nonneg _), ite_eq_right h]
    exact div_self (fun e => h (norm_eq_zero.mp e))

private lemma dual_attain {κ : Type*} [Fintype κ]
    [MeasurableSpace κ]
    [MeasurableSingletonClass κ] (y : κ → Complex) (hy : y ≠ 0)
    {q q' : ENNReal} (hq1 : 1 ≤ q) (hq : q⁻¹ + q'⁻¹ = 1) :
    ∃ g : κ → Complex, eLpNorm g q' Measure.count = 1 ∧
      ∑ k, y k * g k = ((eLpNorm y q Measure.count).toReal : ℂ) := by
  classical
  have hq0 : q ≠ 0 := ne_of_gt (one_pos.trans_le hq1)
  have hq'0 : q' ≠ 0 := q'_ne_zero_of_conj hq
  have hy0 : eLpNorm y q Measure.count ≠ 0 := by
    rw [Ne, eLpNorm_count_eq_zero_iff hq0]
    exact hy
  have hyTop : eLpNorm y q Measure.count ≠ ⊤ := eLpNorm_count_ne_top y hq0
  set A := (eLpNorm y q Measure.count).toReal with hA
  have hApos : 0 < A := ENNReal.toReal_pos hy0 hyTop
  obtain ⟨k₁, hk₁⟩ : ∃ k, y k ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hy (funext fun k => hall k)
  rcases eq_or_ne q ⊤ with rfl | hqtop
  · have hq'inv1 : q'⁻¹ = 1 := by simpa using hq
    have hq'1 : q' = 1 := by
      have h2 := congrArg Inv.inv hq'inv1
      rwa [inv_inv, inv_one] at h2
    have hne : (Finset.univ : Finset κ).Nonempty := ⟨k₁, Finset.mem_univ k₁⟩
    obtain ⟨k₀, _, hk₀⟩ :=
      Finset.exists_max_image Finset.univ (fun k => ‖y k‖) hne
    have hk₀ne : y k₀ ≠ 0 := by
      intro h0
      apply hk₁
      have hle : ‖y k₁‖ ≤ ‖y k₀‖ := hk₀ k₁ (Finset.mem_univ k₁)
      rw [h0, norm_zero] at hle
      exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
    have hsup : (⨆ i, ‖y i‖ₑ) = ‖y k₀‖ₑ :=
      le_antisymm (iSup_le fun i => by
        rw [enorm_complex_eq_ofReal, enorm_complex_eq_ofReal]
        exact ENNReal.ofReal_le_ofReal (hk₀ i (Finset.mem_univ i)))
        (le_iSup (fun i => ‖y i‖ₑ) k₀)
    have hAeq : A = ‖y k₀‖ := by
      rw [hA, eLpNorm_count_top_eq, hsup, enorm_complex_eq_ofReal,
        ENNReal.toReal_ofReal (Complex.norm_nonneg _)]
    refine ⟨fun k => if k = k₀ then sgn y k₀ else 0, ?_, ?_⟩
    · rw [hq'1, eLpNorm_count_one_eq, Finset.sum_eq_single k₀]
      · show ‖(if k₀ = k₀ then sgn y k₀ else 0 : Complex)‖ₑ = _
        rw [ite_eq_left rfl, enorm_complex_eq_ofReal, norm_sgn, ite_eq_right hk₀ne]
        simp
      · intro k _ hk
        rw [ite_eq_right hk]
        simp
      · intro h
        exact absurd (Finset.mem_univ k₀) h
    · rw [Finset.sum_eq_single k₀]
      · change y k₀ * (if k₀ = k₀ then sgn y k₀ else 0 : Complex) = _
        rw [ite_eq_left rfl, sgn_mul, hAeq]
      · intro k _ hk
        change y k * (if k = k₀ then sgn y k₀ else 0 : Complex) = _
        rw [ite_eq_right hk, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ k₀) h
  · have hq1r : 1 ≤ q.toReal := by
      have h := (ENNReal.toReal_le_toReal (by simp : (1 : ENNReal) ≠ ⊤)
        hqtop).mpr hq1
      rwa [ENNReal.toReal_one] at h
    have hqpos : 0 < q.toReal := one_pos.trans_le hq1r
    have hqne0 : q.toReal ≠ 0 := ne_of_gt hqpos
    have hinner : (∑ k, ‖y k‖ₑ ^ q.toReal) =
        ENNReal.ofReal (∑ k, ‖y k‖ ^ q.toReal) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun k _ =>
        Real.rpow_nonneg (Complex.norm_nonneg _) _)]
      apply Finset.sum_congr rfl; intro k _
      rw [enorm_complex_eq_ofReal,
        ENNReal.ofReal_rpow_of_nonneg (Complex.norm_nonneg _)
          ENNReal.toReal_nonneg]
    have h1qnn : 0 ≤ 1 / q.toReal := le_of_lt (one_div_pos.mpr hqpos)
    have hSnn : 0 ≤ ∑ k, ‖y k‖ ^ q.toReal :=
      Finset.sum_nonneg fun k _ =>
        Real.rpow_nonneg (Complex.norm_nonneg _) _
    have hAeq : A = (∑ k, ‖y k‖ ^ q.toReal) ^ (1 / q.toReal) := by
      rw [hA, eLpNorm_count_eq_sum y hq0 hqtop, hinner,
        ENNReal.ofReal_rpow_of_nonneg hSnn h1qnn,
        ENNReal.toReal_ofReal (Real.rpow_nonneg hSnn _)]
    have hS : ∑ k, ‖y k‖ ^ q.toReal = A ^ q.toReal := by
      have h1 : ((∑ k, ‖y k‖ ^ q.toReal) ^ (1 / q.toReal)) ^ q.toReal
          = (∑ k, ‖y k‖ ^ q.toReal) := by
        rw [← Real.rpow_mul hSnn, div_mul_cancel₀ 1 hqne0, Real.rpow_one]
      rw [← h1, hAeq]
    set e := q.toReal - 1 with he
    have he_nn : 0 ≤ e := by rw [he]; linarith [hq1r]
    have hAe : A ^ e ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hApos e)
    set g : κ → Complex := fun k =>
      sgn y k * ((‖y k‖ ^ e / A ^ e : ℝ) : ℂ) with hg
    have hterm : ∀ k : κ, y k * g k =
        ((‖y k‖ * (‖y k‖ ^ e / A ^ e) : ℝ) : ℂ) := by
      intro k
      have : g k = sgn y k * ((‖y k‖ ^ e / A ^ e : ℝ) : ℂ) := rfl
      rw [this, ← mul_assoc, sgn_mul, Complex.ofReal_mul]
    have hpair : ∑ k, y k * g k = ((A : ℝ) : ℂ) := by
      have h1 : ∑ k, y k * g k =
          ((∑ k, ‖y k‖ * (‖y k‖ ^ e / A ^ e) : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum]
        apply Finset.sum_congr rfl; intro k _
        exact hterm k
      rw [h1]
      congr 1
      have hterm2 : ∀ k : κ, ‖y k‖ * (‖y k‖ ^ e / A ^ e) =
          ‖y k‖ ^ q.toReal / A ^ e := by
        intro k
        rw [← mul_div_assoc]
        congr 1
        rcases eq_or_lt_of_le (Complex.norm_nonneg (y k)) with h0 | hpos
        · rw [← h0, zero_mul, Real.zero_rpow hqne0]
        · have hqe1 : q.toReal = 1 + e := by rw [he]; ring
          rw [hqe1, Real.rpow_add hpos, Real.rpow_one]
      rw [Finset.sum_congr rfl (fun k _ => hterm2 k), ← Finset.sum_div, hS,
        ← Real.rpow_sub hApos]
      have hqe : q.toReal - e = 1 := by rw [he]; ring
      rw [hqe, Real.rpow_one]
    refine ⟨g, ?_, ?_⟩
    · rcases eq_or_ne q 1 with rfl | hq1ne
      · have hq'inv0 : q'⁻¹ = 0 := by simpa using hq
        have hq'top : q' = ⊤ := ENNReal.inv_eq_zero.mp hq'inv0
        have he0 : e = 0 := by
          rw [he, ENNReal.toReal_one, sub_self]
        have hg_eq : ∀ k, g k = sgn y k := by
          intro k
          have : g k = sgn y k * ((‖y k‖ ^ e / A ^ e : ℝ) : ℂ) := rfl
          rw [this, he0, Real.rpow_zero, Real.rpow_zero, div_one,
            Complex.ofReal_one, mul_one]
        rw [hq'top, eLpNorm_count_top_eq]
        apply le_antisymm
        · apply iSup_le; intro k
          rw [hg_eq k, enorm_complex_eq_ofReal, norm_sgn]
          by_cases hk : y k = 0 <;> simp [hk]
        · have h1 : ‖g k₁‖ₑ ≤ ⨆ i, ‖g i‖ₑ :=
            le_iSup (fun i => ‖g i‖ₑ) k₁
          rw [hg_eq k₁, enorm_complex_eq_ofReal, norm_sgn,
            ite_eq_right hk₁] at h1
          simpa using h1
      · have hsum : (q.toReal)⁻¹ + (q'.toReal)⁻¹ = 1 := by
          have h := congrArg ENNReal.toReal hq
          rw [ENNReal.toReal_add (ENNReal.inv_ne_top.mpr hq0)
            (ENNReal.inv_ne_top.mpr hq'0), ENNReal.toReal_inv,
            ENNReal.toReal_inv, ENNReal.toReal_one] at h
          exact h
        have hq'1 : 1 ≤ q' := q_ge_one_of_conj (by rw [add_comm]; exact hq)
        have hq'top : q' ≠ ⊤ := by
          rintro rfl
          simp only [ENNReal.inv_top, add_zero, ENNReal.inv_eq_one]at hq
          exact hq1ne hq
        have hq'1r : 1 ≤ q'.toReal := by
          have h := (ENNReal.toReal_le_toReal (by simp : (1 : ENNReal) ≠ ⊤)
            hq'top).mpr hq'1
          rwa [ENNReal.toReal_one] at h
        have hq'pos : 0 < q'.toReal := one_pos.trans_le hq'1r
        have hqq' : e * q'.toReal = q.toReal := by
          have hq'ne0 : q'.toReal ≠ 0 := ne_of_gt hq'pos
          have h2 : q.toReal * q'.toReal = q.toReal + q'.toReal := by
            have h := hsum
            rw [inv_eq_one_div, inv_eq_one_div] at h
            field_simp at h
            linarith
          rw [he]
          linarith [h2]
        have htermN : ∀ k : κ, ‖g k‖ₑ ^ q'.toReal =
            ENNReal.ofReal (‖y k‖ ^ q.toReal / A ^ q.toReal) := by
          intro k
          have hnorm : ‖g k‖ =
              ‖sgn y k‖ * (‖y k‖ ^ e / A ^ e) := by
            have hgg : g k = sgn y k * ((‖y k‖ ^ e / A ^ e : ℝ) : ℂ) := rfl
            rw [hgg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (div_nonneg
                (Real.rpow_nonneg (Complex.norm_nonneg _) _)
                (le_of_lt (Real.rpow_pos_of_pos hApos _)))]
          by_cases hk : y k = 0
          · have hsgn0 : sgn y k = 0 := by unfold sgn; rw [ite_eq_left hk]
            have hg0 : g k = 0 := by
              have hgg : g k =
                sgn y k * ((‖y k‖ ^ e / A ^ e : ℝ) : ℂ) := rfl
              rw [hgg, hsgn0, zero_mul]
            have hyk0 : ‖y k‖ = 0 := norm_eq_zero.mpr hk
            rw [hg0, enorm_zero, ENNReal.zero_rpow_of_pos hq'pos,
              hyk0, Real.zero_rpow hqne0, zero_div, ENNReal.ofReal_zero]
          · have hsgn1 : ‖sgn y k‖ = 1 := by rw [norm_sgn, ite_eq_right hk]
            rw [enorm_complex_eq_ofReal, hnorm, hsgn1, one_mul,
              ENNReal.ofReal_rpow_of_nonneg
                (div_nonneg (Real.rpow_nonneg (Complex.norm_nonneg _) _)
                  (le_of_lt (Real.rpow_pos_of_pos hApos _)))
                ENNReal.toReal_nonneg,
              Real.div_rpow (Real.rpow_nonneg (Complex.norm_nonneg _) _)
                (le_of_lt (Real.rpow_pos_of_pos hApos _)),
              ← Real.rpow_mul (Complex.norm_nonneg (y k)),
              ← Real.rpow_mul (le_of_lt hApos), hqq']
        rw [eLpNorm_count_eq_sum g hq'0 hq'top]
        have hsumN : (∑ k, ‖g k‖ₑ ^ q'.toReal) =
            ENNReal.ofReal (∑ k, ‖y k‖ ^ q.toReal / A ^ q.toReal) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
          apply Finset.sum_congr rfl; intro k _
          exact htermN k
        rw [hsumN, ← Finset.sum_div, hS,
          div_self (ne_of_gt (Real.rpow_pos_of_pos hApos _)),
          ENNReal.ofReal_one, ENNReal.one_rpow]
    · rw [hpair, hA]

private noncomputable def ph {α : Type*} (h : α → Complex) (i : α) : Complex :=
  if h i = 0 then 0 else h i / (‖h i‖ : ℂ)

private lemma ph_mul {α : Type*} (h : α → Complex) (i : α) :
    ph h i * (‖h i‖ : ℂ) = h i := by
  unfold ph
  by_cases hh : h i = 0
  · simp [hh]
  · rw [ite_eq_right hh, div_mul_cancel₀ _ (by exact_mod_cast
      (fun e => hh (norm_eq_zero.mp e)))]

private lemma norm_ph {α : Type*} (h : α → Complex) (i : α) :
    ‖ph h i‖ = if h i = 0 then 0 else 1 := by
  unfold ph
  by_cases hh : h i = 0
  · simp [hh]
  · rw [ite_eq_right hh, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Complex.norm_nonneg _), ite_eq_right hh]
    exact div_self (fun e => hh (norm_eq_zero.mp e))

private lemma fam_bound {α : Type*} [Finite α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (h : α → Complex) {r r₀ r₁ : ENNReal} {θ : ℝ}
    (hr0 : 1 ≤ r₀) (hr1 : 1 ≤ r₁)
    (hr_eq : r⁻¹ = ENNReal.ofReal (1 - θ) * r₀⁻¹ + ENNReal.ofReal θ * r₁⁻¹)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hnorm : eLpNorm h r Measure.count = 1) :
    ∃ H : ℂ → (α → Complex),
      H ((θ : ℝ) : ℂ) = h
      ∧ (∀ z : ℂ, z.re = 0 → eLpNorm (H z) r₀ Measure.count = 1)
      ∧ (∀ z : ℂ, z.re = 1 → eLpNorm (H z) r₁ Measure.count = 1)
      ∧ (∀ i, Differentiable ℂ (fun z => H z i))
      ∧ ∃ B : α → ℝ, ∀ z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1,
        ∀ i, ‖H z i‖ ≤ B i := by
  classical
  have := Fintype.ofFinite α
  have hr00 : r₀ ≠ 0 := ne_of_gt (one_pos.trans_le hr0)
  have hr10 : r₁ ≠ 0 := ne_of_gt (one_pos.trans_le hr1)
  have hrinvT : r⁻¹ ≠ ⊤ := by
    rw [hr_eq, ENNReal.add_ne_top]
    exact ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.inv_ne_top.mpr hr00),
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.inv_ne_top.mpr hr10)⟩
  have hr_ne0 : r ≠ 0 := ENNReal.inv_ne_top.mp hrinvT
  have hhne : h ≠ 0 := by
    intro h0
    rw [h0, eLpNorm_zero] at hnorm
    exact zero_ne_one hnorm
  obtain ⟨i₁, hi₁⟩ : ∃ i, h i ≠ 0 := by
    by_contra hall
    apply hhne
    funext i
    by_contra hi
    exact hall ⟨i, hi⟩
  by_cases hinf : r₀ = ⊤ ∧ r₁ = ⊤
  · obtain ⟨rfl, rfl⟩ := hinf
    have hrT : r = ⊤ := by
      have h : r⁻¹ = 0 := by simpa using hr_eq
      exact ENNReal.inv_eq_zero.mp h
    refine ⟨fun _ => h, rfl, ?_, ?_, ?_, ?_⟩
    · intro z _
      change eLpNorm h _ _ = _
      rw [← hrT]
      exact hnorm
    · intro z _
      change eLpNorm h _ _ = _
      rw [← hrT]
      exact hnorm
    · intro i
      exact differentiable_const _
    · exact ⟨fun i => ‖h i‖, fun z _ i => le_rfl⟩
  · have hrT : r ≠ ⊤ := by
      by_cases h0T : r₀ = ⊤
      · have h1T : r₁ ≠ ⊤ := fun h => hinf ⟨h0T, h⟩
        have h1 : r₁⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr h1T
        have h2 : ENNReal.ofReal θ ≠ 0 := (ENNReal.ofReal_pos.mpr hθ₀).ne'
        have h3 : ENNReal.ofReal θ * r₁⁻¹ ≠ 0 := mul_ne_zero h2 h1
        intro hTT
        have h4 : ENNReal.ofReal θ * r₁⁻¹ ≤ r⁻¹ := by
          rw [hr_eq]; exact le_add_left le_rfl
        rw [hTT, show (⊤ : ENNReal)⁻¹ = 0 from by simp] at h4
        exact h3 (le_antisymm h4 zero_le)
      · have h1 : r₀⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr h0T
        have h2 : ENNReal.ofReal (1 - θ) ≠ 0 :=
          (ENNReal.ofReal_pos.mpr (sub_pos.mpr hθ₁)).ne'
        have h3 : ENNReal.ofReal (1 - θ) * r₀⁻¹ ≠ 0 := mul_ne_zero h2 h1
        intro hTT
        have h4 : ENNReal.ofReal (1 - θ) * r₀⁻¹ ≤ r⁻¹ := by
          rw [hr_eq]; exact le_add_right le_rfl
        rw [hTT, show (⊤ : ENNReal)⁻¹ = 0 from by simp] at h4
        exact h3 (le_antisymm h4 zero_le)
    have hP : 0 < r.toReal := ENNReal.toReal_pos hr_ne0 hrT
    set A : ℂ → ℂ := fun z =>
      (r.toReal : ℂ) * ((1 - z) * ((r₀⁻¹).toReal : ℂ) +
        z * ((r₁⁻¹).toReal : ℂ)) with hA
    set H : ℂ → (α → Complex) := fun z i =>
      if h i = 0 then 0 else ph h i *
        Complex.exp (A z * Real.log ‖h i‖) with hH
    have hmid : (r⁻¹).toReal =
        (1 - θ) * (r₀⁻¹).toReal + θ * (r₁⁻¹).toReal := by
      have h := congrArg ENNReal.toReal hr_eq
      rw [ENNReal.toReal_add
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.inv_ne_top.mpr hr00))
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.inv_ne_top.mpr hr10)),
        ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hθ₁.le),
        ENNReal.toReal_ofReal hθ₀.le] at h
      exact h
    have hAre : ∀ z : ℂ, (A z).re = r.toReal *
        ((1 - z.re) * (r₀⁻¹).toReal + z.re * (r₁⁻¹).toReal) := by
      intro z
      rw [hA]
      change ((r.toReal : ℂ) * ((1 - z) * ((r₀⁻¹).toReal : ℂ) +
        z * ((r₁⁻¹).toReal : ℂ))).re = _
      simp only [Complex.mul_re, Complex.add_re, Complex.sub_re,
        Complex.one_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        sub_zero]
      ring
    have hAθ : A ((θ : ℝ) : ℂ) = 1 := by
      have hmid2 : r.toReal * ((1 - θ) * (r₀⁻¹).toReal +
          θ * (r₁⁻¹).toReal) = 1 := by
        rw [← hmid, ENNReal.toReal_inv, mul_inv_cancel₀ hP.ne']
      rw [hA]
      change ((r.toReal : ℂ) * ((1 - ↑θ) * ((r₀⁻¹).toReal : ℂ) +
        ↑θ * ((r₁⁻¹).toReal : ℂ)) : ℂ) = 1
      exact_mod_cast hmid2
    have hHnorm : ∀ z : ℂ, ∀ i : α, ‖H z i‖ =
        if h i = 0 then 0 else ‖h i‖ ^ (A z).re := by
      intro z i
      by_cases hh : h i = 0
      · have hHz : H z i = 0 := by
          rw [hH]
          change (if h i = 0 then (0 : ℂ) else _) = 0
          rw [ite_eq_left hh]
        rw [hHz, norm_zero, ite_eq_left hh]
      · have hpos : 0 < ‖h i‖ := norm_pos_iff.mpr hh
        rw [hH]
        change ‖(if h i = 0 then (0 : ℂ) else _)‖ = _
        rw [ite_eq_right hh, norm_mul, norm_ph, ite_eq_right hh, one_mul,
          Complex.norm_exp]
        have hre : (A z * ((Real.log ‖h i‖ : ℝ) : ℂ)).re =
            (A z).re * Real.log ‖h i‖ := by
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            mul_zero, sub_zero]
        rw [hre, mul_comm, ← Real.rpow_def_of_pos hpos, ite_eq_right hh]
    have hSnn : 0 ≤ ∑ i, ‖h i‖ ^ r.toReal :=
      Finset.sum_nonneg fun i _ => Real.rpow_nonneg (Complex.norm_nonneg _) _
    have h1Pnn : (0 : ℝ) ≤ 1 / r.toReal := le_of_lt (one_div_pos.mpr hP)
    have hinner_h : (∑ i, ‖h i‖ₑ ^ r.toReal) =
        ENNReal.ofReal (∑ i, ‖h i‖ ^ r.toReal) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ =>
        Real.rpow_nonneg (Complex.norm_nonneg _) _)]
      apply Finset.sum_congr rfl; intro i _
      rw [enorm_complex_eq_ofReal,
        ENNReal.ofReal_rpow_of_nonneg (Complex.norm_nonneg _)
          ENNReal.toReal_nonneg]
    have hAeq_h : (eLpNorm h r Measure.count).toReal =
        (∑ i, ‖h i‖ ^ r.toReal) ^ (1 / r.toReal) := by
      rw [eLpNorm_count_eq_sum h hr_ne0 hrT, hinner_h,
        ENNReal.ofReal_rpow_of_nonneg hSnn h1Pnn,
        ENNReal.toReal_ofReal (Real.rpow_nonneg hSnn _)]
    have hSh : ∑ i, ‖h i‖ ^ r.toReal = 1 := by
      have h4 : ((∑ i, ‖h i‖ ^ r.toReal) ^ (1 / r.toReal)) ^ r.toReal
          = (∑ i, ‖h i‖ ^ r.toReal) := by
        rw [← Real.rpow_mul hSnn, div_mul_cancel₀ 1 hP.ne', Real.rpow_one]
      rw [← h4, ← hAeq_h, hnorm, ENNReal.toReal_one, Real.one_rpow]
    have hHθ : H ((θ : ℝ) : ℂ) = h := by
      funext i
      rw [hH]
      change (if h i = 0 then (0 : ℂ) else _) = _
      by_cases hh : h i = 0
      · rw [ite_eq_left hh, hh]
      · rw [ite_eq_right hh, hAθ, one_mul, ← Complex.ofReal_exp,
          Real.exp_log (norm_pos_iff.mpr hh)]
        exact ph_mul h i
    have bnd_top : ∀ z : ℂ, (A z).re = 0 →
        eLpNorm (H z) ⊤ Measure.count = 1 := by
      intro z hre0
      rw [eLpNorm_count_top_eq]
      apply le_antisymm
      · apply iSup_le; intro i
        rw [enorm_complex_eq_ofReal, hHnorm z i]
        by_cases hh : h i = 0
        · rw [ite_eq_left hh]; simp
        · rw [ite_eq_right hh, hre0, Real.rpow_zero]; simp
      · have h1l : ‖H z i₁‖ₑ = 1 := by
          rw [enorm_complex_eq_ofReal, hHnorm z i₁, ite_eq_right hi₁, hre0,
            Real.rpow_zero, ENNReal.ofReal_one]
        rw [← h1l]
        exact le_iSup (fun i => ‖H z i‖ₑ) i₁
    have bnd_fin : ∀ s : ENNReal, 1 ≤ s → ∀ z : ℂ,
        (A z).re * s.toReal = r.toReal →
        eLpNorm (H z) s Measure.count = 1 := by
      intro s hs z hre
      have hsT : s ≠ ⊤ := by
        rintro rfl
        rw [ENNReal.toReal_top, mul_zero] at hre
        exact hP.ne' hre.symm
      have hs0 : s ≠ 0 := ne_of_gt (one_pos.trans_le hs)
      have hRle : 1 ≤ s.toReal := by
        have h := (ENNReal.toReal_le_toReal (by simp : (1 : ENNReal) ≠ ⊤)
          hsT).mpr hs
        rwa [ENNReal.toReal_one] at h
      have hR : 0 < s.toReal := zero_lt_one.trans_le hRle
      have hpt : ∀ i, ‖H z i‖ ^ s.toReal = ‖h i‖ ^ r.toReal := by
        intro i
        rw [hHnorm z i]
        by_cases hh : h i = 0
        · rw [ite_eq_left hh]
          have hh0 : ‖h i‖ = 0 := norm_eq_zero.mpr hh
          rw [hh0, Real.zero_rpow (ne_of_gt hR), Real.zero_rpow hP.ne']
        · rw [ite_eq_right hh, ← Real.rpow_mul (Complex.norm_nonneg _), hre]
      have htm : ∀ i, ‖H z i‖ₑ ^ s.toReal =
          ENNReal.ofReal (‖h i‖ ^ r.toReal) := by
        intro i
        rw [enorm_complex_eq_ofReal,
          ENNReal.ofReal_rpow_of_nonneg (Complex.norm_nonneg _)
            ENNReal.toReal_nonneg,
          hpt i]
      have hsumH : (∑ i, ‖H z i‖ₑ ^ s.toReal) = 1 := by
        rw [Finset.sum_congr rfl (fun i _ => htm i),
          ← ENNReal.ofReal_sum_of_nonneg (fun i _ =>
            Real.rpow_nonneg (Complex.norm_nonneg _) _),
          hSh, ENNReal.ofReal_one]
      rw [eLpNorm_count_eq_sum _ hs0 hsT, hsumH]
      simp
    have hre_z0 : ∀ z : ℂ, z.re = 0 → (A z).re =
        r.toReal * (r₀⁻¹).toReal := by
      intro z hz
      rw [hAre z, hz, sub_zero, one_mul, zero_mul, add_zero]
    have hre_z1 : ∀ z : ℂ, z.re = 1 → (A z).re =
        r.toReal * (r₁⁻¹).toReal := by
      intro z hz
      rw [hAre z, hz, sub_self, zero_mul, one_mul, zero_add]
    have bnd0 : ∀ z : ℂ, z.re = 0 → eLpNorm (H z) r₀ Measure.count = 1 := by
      intro z hz
      rcases eq_or_ne r₀ ⊤ with rfl | hr0T
      · have hre0 : (A z).re = 0 := by
          rw [hre_z0 z hz]
          simp
        exact bnd_top z hre0
      · have hR₀le : 1 ≤ r₀.toReal := by
          have h := (ENNReal.toReal_le_toReal (by simp : (1 : ENNReal) ≠ ⊤)
            hr0T).mpr hr0
          rwa [ENNReal.toReal_one] at h
        have hPR : (r₀⁻¹).toReal * r₀.toReal = 1 := by
          rw [ENNReal.toReal_inv,
            inv_mul_cancel₀ (ne_of_gt (zero_lt_one.trans_le hR₀le))]
        have hreP : (A z).re * r₀.toReal = r.toReal := by
          rw [hre_z0 z hz, mul_assoc, hPR, mul_one]
        exact bnd_fin r₀ hr0 z hreP
    have bnd1 : ∀ z : ℂ, z.re = 1 → eLpNorm (H z) r₁ Measure.count = 1 := by
      intro z hz
      rcases eq_or_ne r₁ ⊤ with rfl | hr1T
      · have hre1 : (A z).re = 0 := by
          rw [hre_z1 z hz]
          simp
        exact bnd_top z hre1
      · have hR₁le : 1 ≤ r₁.toReal := by
          have h := (ENNReal.toReal_le_toReal (by simp : (1 : ENNReal) ≠ ⊤)
            hr1T).mpr hr1
          rwa [ENNReal.toReal_one] at h
        have hPR : (r₁⁻¹).toReal * r₁.toReal = 1 := by
          rw [ENNReal.toReal_inv,
            inv_mul_cancel₀ (ne_of_gt (zero_lt_one.trans_le hR₁le))]
        have hreP : (A z).re * r₁.toReal = r.toReal := by
          rw [hre_z1 z hz, mul_assoc, hPR, mul_one]
        exact bnd_fin r₁ hr1 z hreP
    have hA_diff : Differentiable ℂ A := by
      rw [hA]
      show Differentiable ℂ (fun z : ℂ =>
        (r.toReal : ℂ) * ((1 - z) * ((r₀⁻¹).toReal : ℂ) +
          z * ((r₁⁻¹).toReal : ℂ)))
      exact (((differentiable_const _).sub differentiable_id).mul_const _).add
        (differentiable_id.mul_const _) |>.const_mul _
    have hHdiff : ∀ i, Differentiable ℂ (fun z => H z i) := by
      intro i
      by_cases hh : h i = 0
      · have e0 : (fun z => H z i) = fun _ => 0 := by
          funext z
          rw [hH]
          change (if h i = 0 then (0 : ℂ) else _) = 0
          rw [ite_eq_left hh]
        rw [e0]
        exact differentiable_const _
      · have e1 : (fun z => H z i) = (fun z =>
          ph h i * Complex.exp (A z * Real.log ‖h i‖)) := by
          funext z
          rw [hH]
          change (if h i = 0 then (0 : ℂ) else _) = _
          rw [ite_eq_right hh]
        rw [e1]
        exact (differentiable_const _).mul
          (Complex.differentiable_exp.comp (hA_diff.mul_const _))
    have hHbdd : ∃ B : α → ℝ, ∀ z ∈
        Complex.HadamardThreeLines.verticalClosedStrip 0 1,
        ∀ i, ‖H z i‖ ≤ B i := by
      refine ⟨fun i => ‖h i‖ ^ (r.toReal * min (r₀⁻¹).toReal (r₁⁻¹).toReal)
        + ‖h i‖ ^ (r.toReal * max (r₀⁻¹).toReal (r₁⁻¹).toReal),
        fun z hz i => ?_⟩
      have hx : z.re ∈ Set.Icc (0 : ℝ) 1 := hz
      obtain ⟨hx0, hx1⟩ := Set.mem_Icc.mp hx
      have hmem0 : (1 - z.re) * (r₀⁻¹).toReal + z.re * (r₁⁻¹).toReal ≤
          max (r₀⁻¹).toReal (r₁⁻¹).toReal := by
        calc (1 - z.re) * (r₀⁻¹).toReal + z.re * (r₁⁻¹).toReal
            ≤ (1 - z.re) * max (r₀⁻¹).toReal (r₁⁻¹).toReal +
              z.re * max (r₀⁻¹).toReal (r₁⁻¹).toReal := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left (le_max_left _ _)
                  (sub_nonneg.mpr hx1)
              · exact mul_le_mul_of_nonneg_left (le_max_right _ _) hx0
          _ = _ := by rw [← add_mul, sub_add_cancel, one_mul]
      have hmem1 : min (r₀⁻¹).toReal (r₁⁻¹).toReal ≤
          (1 - z.re) * (r₀⁻¹).toReal + z.re * (r₁⁻¹).toReal := by
        calc min (r₀⁻¹).toReal (r₁⁻¹).toReal
            = (1 - z.re) * min (r₀⁻¹).toReal (r₁⁻¹).toReal +
              z.re * min (r₀⁻¹).toReal (r₁⁻¹).toReal := by
                rw [← add_mul, sub_add_cancel, one_mul]
          _ ≤ _ := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left (min_le_left _ _)
                  (sub_nonneg.mpr hx1)
              · exact mul_le_mul_of_nonneg_left (min_le_right _ _) hx0
      have hlo : r.toReal * min (r₀⁻¹).toReal (r₁⁻¹).toReal ≤ (A z).re := by
        rw [hAre z]
        exact mul_le_mul_of_nonneg_left hmem1 hP.le
      have hhi : (A z).re ≤ r.toReal *
          max (r₀⁻¹).toReal (r₁⁻¹).toReal := by
        rw [hAre z]
        exact mul_le_mul_of_nonneg_left hmem0 hP.le
      rw [hHnorm z i]
      by_cases hh : h i = 0
      · rw [ite_eq_left hh]
        exact add_nonneg (Real.rpow_nonneg (Complex.norm_nonneg _) _)
          (Real.rpow_nonneg (Complex.norm_nonneg _) _)
      · rw [ite_eq_right hh]
        have hpos : 0 < ‖h i‖ := norm_pos_iff.mpr hh
        rcases le_total ‖h i‖ 1 with hle | hle
        · calc ‖h i‖ ^ (A z).re
              ≤ ‖h i‖ ^ (r.toReal * min (r₀⁻¹).toReal (r₁⁻¹).toReal) :=
                Real.rpow_le_rpow_of_exponent_ge hpos hle hlo
            _ ≤ _ + _ := le_add_of_nonneg_right
                (Real.rpow_nonneg (Complex.norm_nonneg _) _)
        · calc ‖h i‖ ^ (A z).re
              ≤ ‖h i‖ ^ (r.toReal * max (r₀⁻¹).toReal (r₁⁻¹).toReal) :=
                Real.rpow_le_rpow_of_exponent_le hle hhi
            _ ≤ _ + _ := le_add_of_nonneg_left
                (Real.rpow_nonneg (Complex.norm_nonneg _) _)
    exact ⟨H, hHθ, bnd0, bnd1, hHdiff, hHbdd⟩

private lemma unit_bound {ι κ : Type*} [Finite ι] [Fintype κ]
    [MeasurableSpace ι] [MeasurableSpace κ]
    [MeasurableSingletonClass ι] [MeasurableSingletonClass κ]
    {p₀ p₁ q₀ q₁ p q : ENNReal} {θ : ℝ}
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁)
    (hp_eq : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hq_eq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    {M₀ M₁ : ENNReal} (hM₀ : M₀ ≠ ⊤) (hM₁ : M₁ ≠ ⊤)
    (T : (ι → Complex) →ₗ[Complex] (κ → Complex))
    (h₀ : ∀ f : ι → Complex,
      eLpNorm (T f) q₀ (Measure.count : Measure κ) ≤
        M₀ * eLpNorm f p₀ (Measure.count : Measure ι))
    (h₁ : ∀ f : ι → Complex,
      eLpNorm (T f) q₁ (Measure.count : Measure κ) ≤
        M₁ * eLpNorm f p₁ (Measure.count : Measure ι))
    {q₀' q₁' q' : ENNReal}
    (hq₀c : q₀⁻¹ + q₀'⁻¹ = 1) (hq₁c : q₁⁻¹ + q₁'⁻¹ = 1)
    (hqc : q⁻¹ + q'⁻¹ = 1)
    {f : ι → Complex}
    (hf : eLpNorm f p (Measure.count : Measure ι) = 1)
    {g : κ → Complex}
    (hg : eLpNorm g q' (Measure.count : Measure κ) = 1) :
    ‖∑ k, (T f) k * g k‖ ≤ M₀.toReal ^ (1 - θ) * M₁.toReal ^ θ := by
  have := Fintype.ofFinite ι
  classical
  have hq1 : 1 ≤ q := q_ge_one_of_conj hqc
  have hq0n : q₀ ≠ 0 := ne_of_gt (one_pos.trans_le hq₀)
  have hq1n : q₁ ≠ 0 := ne_of_gt (one_pos.trans_le hq₁)
  have hqn : q ≠ 0 := ne_of_gt (one_pos.trans_le hq1)
  have f0 : q₀⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hq0n
  have f1 : q₁⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hq1n
  have f0' : q₀'⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (q'_ne_zero_of_conj hq₀c)
  have f1' : q₁'⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (q'_ne_zero_of_conj hq₁c)
  have f'' : q'⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (q'_ne_zero_of_conj hqc)
  have e0 : (q₀⁻¹).toReal + (q₀'⁻¹).toReal = 1 := by
    have h := congrArg ENNReal.toReal hq₀c
    rwa [ENNReal.toReal_add f0 f0', ENNReal.toReal_one] at h
  have e1 : (q₁⁻¹).toReal + (q₁'⁻¹).toReal = 1 := by
    have h := congrArg ENNReal.toReal hq₁c
    rwa [ENNReal.toReal_add f1 f1', ENNReal.toReal_one] at h
  have eq' : (q⁻¹).toReal =
      (1 - θ) * (q₀⁻¹).toReal + θ * (q₁⁻¹).toReal := by
    have h := congrArg ENNReal.toReal hq_eq
    rw [ENNReal.toReal_add
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top f0)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top f1),
      ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hθ₁.le),
      ENNReal.toReal_ofReal hθ₀.le] at h
    exact h
  have ereal : (q'⁻¹).toReal =
      (1 - θ) * (q₀'⁻¹).toReal + θ * (q₁'⁻¹).toReal := by
    have e0' : (q₀'⁻¹).toReal = 1 - (q₀⁻¹).toReal := by linarith [e0]
    have e1' : (q₁'⁻¹).toReal = 1 - (q₁⁻¹).toReal := by linarith [e1]
    have h := congrArg ENNReal.toReal hqc
    rw [ENNReal.toReal_add (ENNReal.inv_ne_top.mpr hqn) f'',
      ENNReal.toReal_one] at h
    have ee' : (q'⁻¹).toReal = 1 - (q⁻¹).toReal := by linarith [h]
    rw [e0', e1', ee', eq']
    ring
  have hq'_eq : q'⁻¹ = ENNReal.ofReal (1 - θ) * q₀'⁻¹ +
      ENNReal.ofReal θ * q₁'⁻¹ := by
    have h1 : q'⁻¹ = ENNReal.ofReal (q'⁻¹).toReal :=
      (ENNReal.ofReal_toReal f'').symm
    rw [h1, ereal, ENNReal.ofReal_add
      (mul_nonneg (sub_nonneg.mpr hθ₁.le) ENNReal.toReal_nonneg)
      (mul_nonneg hθ₀.le ENNReal.toReal_nonneg),
      ENNReal.ofReal_mul (sub_nonneg.mpr hθ₁.le),
      ENNReal.ofReal_mul hθ₀.le,
      ENNReal.ofReal_toReal f0', ENNReal.ofReal_toReal f1']
  have hq₀'1 : 1 ≤ q₀' := q_ge_one_of_conj (by rw [add_comm]; exact hq₀c)
  have hq₁'1 : 1 ≤ q₁' := q_ge_one_of_conj (by rw [add_comm]; exact hq₁c)
  obtain ⟨F, hFθ, hF0, hF1, hFdiff, hFbdd⟩ :=
    fam_bound f hp₀ hp₁ hp_eq hθ₀ hθ₁ hf
  obtain ⟨G, hGθ, hG0, hG1, hGdiff, hGbdd⟩ :=
    fam_bound g hq₀'1 hq₁'1 hq'_eq hθ₀ hθ₁ hg
  have hTv : ∀ v : ι → Complex,
      T v = ∑ i, v i • T (Pi.single i 1) := by
    intro v
    have hvv : v = ∑ i, v i • Pi.single i 1 := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply,
        smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
    conv_lhs => rw [hvv]
    rw [map_sum]
    apply Finset.sum_congr rfl; intro i _
    exact map_smul T _ _
  have hTk : ∀ z k, (T (F z)) k =
      ∑ i, F z i * (T (Pi.single i 1)) k := by
    intro z k
    rw [hTv (F z), Finset.sum_apply]
    apply Finset.sum_congr rfl; intro i _
    rw [Pi.smul_apply, smul_eq_mul]
  have hTdiff : ∀ k, Differentiable ℂ (fun z => (T (F z)) k) := by
    intro k
    have e1 : (fun z => (T (F z)) k) =
        (fun z => ∑ i, F z i * (T (Pi.single i 1)) k) :=
      funext fun z => hTk z k
    have e2 : (fun z => ∑ i, F z i * (T (Pi.single i 1)) k) =
        ∑ i, (fun z => F z i * (T (Pi.single i 1)) k) := by
      funext z
      exact (Finset.sum_apply z Finset.univ (fun i z => F z i * (T (Pi.single i 1)) k)).symm
    rw [e1, e2]
    exact Differentiable.sum (fun i _ => (hFdiff i).mul_const _)
  have hΦdiff : Differentiable ℂ
      (fun z => ∑ k, (T (F z)) k * G z k) := by
    have e3 : (fun z => ∑ k, (T (F z)) k * G z k) =
        ∑ k, (fun z => (T (F z)) k * G z k) := by
      funext z
      exact (Finset.sum_apply z Finset.univ
        (fun k z => (T (F z)) k * G z k)).symm
    rw [e3]
    exact Differentiable.sum (fun k _ => (hTdiff k).mul (hGdiff k))
  have hDCC : DiffContOnCl ℂ (fun z => ∑ k, (T (F z)) k * G z k)
      (Complex.HadamardThreeLines.verticalStrip 0 1) :=
    hΦdiff.diffContOnCl
  have hBdd : BddAbove (norm ∘ (fun z => ∑ k, (T (F z)) k * G z k) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    obtain ⟨BF, hBF⟩ := hFbdd
    obtain ⟨BG, hBG⟩ := hGbdd
    refine ⟨∑ k, (∑ i, BF i * ‖(T (Pi.single i 1)) k‖) * BG k, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    change ‖∑ k, (T (F z)) k * G z k‖ ≤ _
    have hTkB : ∀ k, ‖(T (F z)) k‖ ≤
        ∑ i, BF i * ‖(T (Pi.single i 1)) k‖ := by
      intro k
      calc ‖(T (F z)) k‖ = ‖∑ i, F z i * (T (Pi.single i 1)) k‖ := by
              rw [hTk z k]
        _ ≤ ∑ i, ‖F z i * (T (Pi.single i 1)) k‖ := norm_sum_le _ _
        _ = ∑ i, ‖F z i‖ * ‖(T (Pi.single i 1)) k‖ := by
              apply Finset.sum_congr rfl; intro i _
              exact norm_mul _ _
        _ ≤ _ := by
              apply Finset.sum_le_sum; intro i _
              exact mul_le_mul_of_nonneg_right (hBF z hz i) (norm_nonneg _)
    calc ‖∑ k, (T (F z)) k * G z k‖
        ≤ ∑ k, ‖(T (F z)) k * G z k‖ := norm_sum_le _ _
      _ = ∑ k, ‖(T (F z)) k‖ * ‖G z k‖ := by
            apply Finset.sum_congr rfl; intro k _
            exact norm_mul _ _
      _ ≤ _ := by
            apply Finset.sum_le_sum; intro k _
            exact mul_le_mul (hTkB k) (hBG z hz k) (norm_nonneg _)
              (Finset.sum_nonneg fun i _ =>
                mul_nonneg (le_trans (norm_nonneg _) (hBF z hz i))
                  (norm_nonneg _))
  have bndry0 : ∀ z : ℂ, z.re = 0 →
      ‖∑ k, (T (F z)) k * G z k‖ ≤ M₀.toReal := by
    intro z hz
    have hle : ‖∑ k, (T (F z)) k * G z k‖ₑ ≤ M₀ := by
      calc ‖∑ k, (T (F z)) k * G z k‖ₑ
          ≤ eLpNorm (T (F z)) q₀ _ * eLpNorm (G z) q₀' _ :=
            pairing_le _ _ hq₀c
        _ = eLpNorm (T (F z)) q₀ _ * 1 := by rw [hG0 z hz]
        _ = eLpNorm (T (F z)) q₀ _ := mul_one _
        _ ≤ M₀ * eLpNorm (F z) p₀ _ := h₀ _
        _ = M₀ * 1 := by rw [hF0 z hz]
        _ = M₀ := mul_one _
    calc ‖∑ k, (T (F z)) k * G z k‖
        = (‖∑ k, (T (F z)) k * G z k‖ₑ).toReal := by
          rw [enorm_complex_eq_ofReal,
            ENNReal.toReal_ofReal (norm_nonneg _)]
      _ ≤ M₀.toReal := ENNReal.toReal_mono hM₀ hle
  have bndry1 : ∀ z : ℂ, z.re = 1 →
      ‖∑ k, (T (F z)) k * G z k‖ ≤ M₁.toReal := by
    intro z hz
    have hle : ‖∑ k, (T (F z)) k * G z k‖ₑ ≤ M₁ := by
      calc ‖∑ k, (T (F z)) k * G z k‖ₑ
          ≤ eLpNorm (T (F z)) q₁ _ * eLpNorm (G z) q₁' _ :=
            pairing_le _ _ hq₁c
        _ = eLpNorm (T (F z)) q₁ _ * 1 := by rw [hG1 z hz]
        _ = eLpNorm (T (F z)) q₁ _ := mul_one _
        _ ≤ M₁ * eLpNorm (F z) p₁ _ := h₁ _
        _ = M₁ * 1 := by rw [hF1 z hz]
        _ = M₁ := mul_one _
    calc ‖∑ k, (T (F z)) k * G z k‖
        = (‖∑ k, (T (F z)) k * G z k‖ₑ).toReal := by
          rw [enorm_complex_eq_ofReal,
            ENNReal.toReal_ofReal (norm_nonneg _)]
      _ ≤ M₁.toReal := ENNReal.toReal_mono hM₁ hle
  have hmem : ((θ : ℝ) : ℂ) ∈
      Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    unfold Complex.HadamardThreeLines.verticalClosedStrip
    simp only [Set.mem_preimage, Set.mem_Icc, Complex.ofReal_re]
    exact ⟨hθ₀.le, hθ₁.le⟩
  have hmain :=
    Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'
      (fun z => ∑ k, (T (F z)) k * G z k) hmem hDCC hBdd
      (fun z hz => bndry0 z (by simpa using hz))
      (fun z hz => bndry1 z (by simpa using hz))
  simpa only [hFθ, hGθ, Complex.ofReal_re] using hmain

private lemma riesz_thorin_unit {ι κ : Type*} [Finite ι] [Finite κ]
    [MeasurableSpace ι] [MeasurableSpace κ]
    [MeasurableSingletonClass ι] [MeasurableSingletonClass κ]
    {p₀ p₁ q₀ q₁ p q : ENNReal} {θ : ℝ}
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q)
    (hp_eq : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hq_eq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    {M₀ M₁ : ENNReal} (hM₀ : M₀ ≠ ⊤) (hM₁ : M₁ ≠ ⊤)
    (T : (ι → Complex) →ₗ[Complex] (κ → Complex))
    (h₀ : ∀ f : ι → Complex,
      eLpNorm (T f) q₀ (Measure.count : Measure κ) ≤
        M₀ * eLpNorm f p₀ (Measure.count : Measure ι))
    (h₁ : ∀ f : ι → Complex,
      eLpNorm (T f) q₁ (Measure.count : Measure κ) ≤
        M₁ * eLpNorm f p₁ (Measure.count : Measure ι))
    {q₀' q₁' q' : ENNReal}
    (hq₀c : q₀⁻¹ + q₀'⁻¹ = 1) (hq₁c : q₁⁻¹ + q₁'⁻¹ = 1)
    (hqc : q⁻¹ + q'⁻¹ = 1)
    {f : ι → Complex}
    (hf : eLpNorm f p (Measure.count : Measure ι) = 1) :
    eLpNorm (T f) q (Measure.count : Measure κ) ≤
      ENNReal.ofReal (M₀.toReal ^ (1 - θ) * M₁.toReal ^ θ) := by
  have := Fintype.ofFinite κ
  have := Fintype.ofFinite ι
  classical
  have hq0 : q ≠ 0 := ne_of_gt (one_pos.trans_le hq)
  rcases eq_or_ne (T f) 0 with hTf0 | hTf
  · rw [hTf0, eLpNorm_zero]
    exact zero_le
  · obtain ⟨g, hg1, hgp⟩ := dual_attain (T f) hTf hq hqc
    have hb := unit_bound hθ₀ hθ₁ hp₀ hp₁ hq₀ hq₁ hp_eq hq_eq hM₀ hM₁ T h₀ h₁
      hq₀c hq₁c hqc hf hg1
    have hA : (eLpNorm (T f) q (Measure.count : Measure κ)).toReal =
        ‖∑ k, (T f) k * g k‖ := by
      rw [hgp, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ENNReal.toReal_nonneg]
    have hle : (eLpNorm (T f) q (Measure.count : Measure κ)).toReal ≤
        M₀.toReal ^ (1 - θ) * M₁.toReal ^ θ := by
      rw [hA]; exact hb
    have hfin : eLpNorm (T f) q (Measure.count : Measure κ) ≠ ⊤ :=
      eLpNorm_count_ne_top _ hq0
    rw [← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal hle

private lemma riesz_thorin_top {ι κ : Type*} [Finite ι] [Finite κ]
    [MeasurableSpace ι] [MeasurableSpace κ]
    [MeasurableSingletonClass ι] [MeasurableSingletonClass κ]
    {p q : ENNReal} {θ : ℝ} {M₀ M₁ : ENNReal}
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hp : 1 ≤ p)
    (hM₀ : M₀ ≠ 0) (hM₁ : M₁ ≠ 0) (hT : M₀ = ⊤ ∨ M₁ = ⊤)
    (T : (ι → Complex) →ₗ[Complex] (κ → Complex)) :
    ∀ f : ι → Complex,
      eLpNorm (T f) q (Measure.count : Measure κ) ≤
        (M₀ ^ (1 - θ) * M₁ ^ θ) * eLpNorm f p (Measure.count : Measure ι) := by
  have := Fintype.ofFinite κ
  have := Fintype.ofFinite ι
  have hp0 : p ≠ 0 := ne_of_gt (one_pos.trans_le hp)
  have h1θ : (0 : ℝ) < 1 - θ := sub_pos.mpr hθ₁
  intro f
  rcases eq_or_ne (eLpNorm f p _) 0 with hf0 | hfn0
  · have hf : f = 0 := (eLpNorm_count_eq_zero_iff hp0 f).mp hf0
    rw [hf]
    simp
  · have hC : M₀ ^ (1 - θ) * M₁ ^ θ = ⊤ := by
      rcases hT with rfl | rfl
      · rw [ENNReal.top_rpow_of_pos h1θ]
        have hne : M₁ ^ θ ≠ 0 := by
          intro hcon
          rw [ENNReal.rpow_eq_zero_iff] at hcon
          rcases hcon with ⟨h0, _⟩ | ⟨hT, hneg⟩
          · exact hM₁ h0
          · exact absurd hneg (not_lt.mpr hθ₀.le)
        exact ENNReal.top_mul hne
      · rw [ENNReal.top_rpow_of_pos hθ₀]
        have hne : M₀ ^ (1 - θ) ≠ 0 := by
          intro hcon
          rw [ENNReal.rpow_eq_zero_iff] at hcon
          rcases hcon with ⟨h0, _⟩ | ⟨hT, hneg⟩
          · exact hM₀ h0
          · exact absurd hneg (not_lt.mpr h1θ.le)
        exact ENNReal.mul_top hne
    rw [hC, ENNReal.top_mul hfn0]
    exact le_top

private lemma riesz_thorin_scale {ι κ : Type*} [Finite ι] [Finite κ]
    [MeasurableSpace ι] [MeasurableSpace κ]
    [MeasurableSingletonClass ι] [MeasurableSingletonClass κ]
    {p₀ p₁ q₀ q₁ p q : ENNReal} {θ : ℝ}
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁) (hp : 1 ≤ p)
    (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q)
    (hp_eq : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hq_eq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    {M₀ M₁ : ENNReal} (hM₀ : M₀ ≠ ⊤) (hM₁ : M₁ ≠ ⊤)
    (T : (ι → Complex) →ₗ[Complex] (κ → Complex))
    (h₀ : ∀ f : ι → Complex,
      eLpNorm (T f) q₀ (Measure.count : Measure κ) ≤
        M₀ * eLpNorm f p₀ (Measure.count : Measure ι))
    (h₁ : ∀ f : ι → Complex,
      eLpNorm (T f) q₁ (Measure.count : Measure κ) ≤
        M₁ * eLpNorm f p₁ (Measure.count : Measure ι)) :
    ∀ f : ι → Complex,
      eLpNorm (T f) q (Measure.count : Measure κ) ≤
        (M₀ ^ (1 - θ) * M₁ ^ θ) * eLpNorm f p (Measure.count : Measure ι) := by
  have := Fintype.ofFinite κ
  have := Fintype.ofFinite ι
  classical
  have hp0 : p ≠ 0 := ne_of_gt (one_pos.trans_le hp)
  obtain ⟨q₀', hq₀c⟩ := holder_conj hq₀
  obtain ⟨q₁', hq₁c⟩ := holder_conj hq₁
  obtain ⟨q', hqc⟩ := holder_conj hq
  intro f
  rcases eq_or_ne (eLpNorm f p (Measure.count : Measure ι)) 0 with hf0 | hfn0
  · have hf : f = 0 := (eLpNorm_count_eq_zero_iff hp0 f).mp hf0
    rw [hf0, hf, map_zero T, eLpNorm_zero, mul_zero]
  · have hafin : eLpNorm f p (Measure.count : Measure ι) ≠ ⊤ :=
      eLpNorm_count_ne_top _ hp0
    have ha0 : 0 < (eLpNorm f p (Measure.count : Measure ι)).toReal :=
      ENNReal.toReal_pos hfn0 hafin
    have haC : ENNReal.ofReal
        (eLpNorm f p (Measure.count : Measure ι)).toReal =
        eLpNorm f p (Measure.count : Measure ι) :=
      ENNReal.ofReal_toReal hafin
    set f₁ : ι → Complex :=
      (((eLpNorm f p (Measure.count : Measure ι)).toReal⁻¹ : ℝ) : ℂ) • f
      with hf₁
    have hf₁1 : eLpNorm f₁ p (Measure.count : Measure ι) = 1 := by
      rw [hf₁, eLpNorm_const_smul, enorm_complex_eq_ofReal,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (le_of_lt (inv_pos.mpr ha0)),
        ENNReal.ofReal_inv_of_pos ha0, haC,
        ENNReal.inv_mul_cancel hfn0 hafin]
    have h1 : (((eLpNorm f p (Measure.count : Measure ι)).toReal : ℝ) : ℂ) *
        ((((eLpNorm f p (Measure.count : Measure ι)).toReal⁻¹ : ℝ)) : ℂ) =
        1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ ha0.ne', Complex.ofReal_one]
    have hff : f =
        (((eLpNorm f p (Measure.count : Measure ι)).toReal : ℝ) : ℂ) • f₁ := by
      funext i
      rw [Pi.smul_apply, hf₁, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
        ← mul_assoc, h1, one_mul]
    have hTf : T f =
        (((eLpNorm f p (Measure.count : Measure ι)).toReal : ℝ) : ℂ) •
          T f₁ := by
      conv_lhs => rw [hff]
      exact map_smul T _ _
    have hunit := riesz_thorin_unit hθ₀ hθ₁ hp₀ hp₁ hq₀ hq₁ hq hp_eq hq_eq
      hM₀ hM₁ T h₀ h₁ hq₀c hq₁c hqc hf₁1
    have hCval : ENNReal.ofReal (M₀.toReal ^ (1 - θ) * M₁.toReal ^ θ) =
        M₀ ^ (1 - θ) * M₁ ^ θ := by
      have e1 : M₀ ^ (1 - θ) = ENNReal.ofReal (M₀.toReal ^ (1 - θ)) := by
        rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg
          (sub_nonneg.mpr hθ₁.le),
          ENNReal.ofReal_toReal hM₀]
      have e2 : M₁ ^ θ = ENNReal.ofReal (M₁.toReal ^ θ) := by
        rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hθ₀.le,
          ENNReal.ofReal_toReal hM₁]
      rw [e1, e2,
        ← ENNReal.ofReal_mul
          (Real.rpow_nonneg ENNReal.toReal_nonneg _)]
    calc eLpNorm (T f) q (Measure.count : Measure κ)
        = ENNReal.ofReal
            (eLpNorm f p (Measure.count : Measure ι)).toReal *
          eLpNorm (T f₁) q (Measure.count : Measure κ) := by
          rw [hTf, eLpNorm_const_smul, enorm_complex_eq_ofReal,
            Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ENNReal.toReal_nonneg]
      _ ≤ ENNReal.ofReal
            (eLpNorm f p (Measure.count : Measure ι)).toReal *
          ENNReal.ofReal (M₀.toReal ^ (1 - θ) * M₁.toReal ^ θ) :=
          mul_le_mul_right hunit _
      _ = (M₀ ^ (1 - θ) * M₁ ^ θ) *
          eLpNorm f p (Measure.count : Measure ι) := by
          rw [hCval, haC]
          exact mul_comm _ _

/-- **Riesz–Thorin interpolation on finite sets, auxiliary form.** Let $\iota$ and $\kappa$ be
finite sets, each with a σ-algebra in which singletons are measurable and with the counting
measure, and write $\|g\|_r \in [0, \infty]$ for the $\ell^r$ norm of $g$ with respect to the
counting measure. Let $p_0, p_1, p, q_0, q_1, q \in [1, \infty]$ and $\theta \in [0, 1]$ satisfy
$1/p = (1-\theta)/p_0 + \theta/p_1$ and $1/q = (1-\theta)/q_0 + \theta/q_1$, where $1/\infty = 0$.
Let $M_0, M_1 \in [0, \infty]$ and let $T : \mathbb{C}^\iota \to \mathbb{C}^\kappa$ be a
$\mathbb{C}$-linear map with $\|Tf\|_{q_0} \le M_0 \|f\|_{p_0}$ and
$\|Tf\|_{q_1} \le M_1 \|f\|_{p_1}$ for all $f \in \mathbb{C}^\iota$. Then
$\|Tf\|_q \le M_0^{1-\theta} M_1^{\theta} \|f\|_p$ for all $f \in \mathbb{C}^\iota$, where
products and powers are computed in $[0, \infty]$ with $0 \cdot \infty = 0$ and $c^0 = 1$.

This is the Riesz–Thorin interpolation theorem on finite sets with finiteness assumed as a
property rather than given by an explicit enumeration of the elements; that theorem is derived
from this one. -/
theorem riesz_thorin_finite
    {ι κ : Type*} [Finite ι] [Finite κ]
    [MeasurableSpace ι] [MeasurableSpace κ]
    [MeasurableSingletonClass ι] [MeasurableSingletonClass κ]
    {p₀ p₁ q₀ q₁ p q : ENNReal}
    {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁) (hp : 1 ≤ p)
    (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q)
    (hp_eq : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hq_eq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    {M₀ M₁ : ENNReal}
    (T : (ι → Complex) →ₗ[Complex] (κ → Complex))
    (h₀ : ∀ f : ι → Complex,
      eLpNorm (T f) q₀ (Measure.count : Measure κ) ≤
        M₀ * eLpNorm f p₀ (Measure.count : Measure ι))
    (h₁ : ∀ f : ι → Complex,
      eLpNorm (T f) q₁ (Measure.count : Measure κ) ≤
        M₁ * eLpNorm f p₁ (Measure.count : Measure ι)) :
    ∀ f : ι → Complex,
      eLpNorm (T f) q (Measure.count : Measure κ) ≤
        (M₀ ^ (1 - θ) * M₁ ^ θ) * eLpNorm f p (Measure.count : Measure ι) := by
  classical
  rcases eq_or_ne θ 0 with rfl | hθne0
  · have hp0e : p⁻¹ = p₀⁻¹ := by simpa using hp_eq
    have hq0e : q⁻¹ = q₀⁻¹ := by simpa using hq_eq
    have hpp : p = p₀ := by
      have h := congrArg Inv.inv hp0e
      rwa [inv_inv, inv_inv] at h
    have hqq : q = q₀ := by
      have h := congrArg Inv.inv hq0e
      rwa [inv_inv, inv_inv] at h
    intro f
    rw [hpp, hqq]
    simp only [sub_zero, ENNReal.rpow_one, ENNReal.rpow_zero, mul_one]
    exact h₀ f
  rcases eq_or_ne θ 1 with rfl | hθne1
  · have hp1e : p⁻¹ = p₁⁻¹ := by simpa using hp_eq
    have hq1e : q⁻¹ = q₁⁻¹ := by simpa using hq_eq
    have hpp : p = p₁ := by
      have h := congrArg Inv.inv hp1e
      rwa [inv_inv, inv_inv] at h
    have hqq : q = q₁ := by
      have h := congrArg Inv.inv hq1e
      rwa [inv_inv, inv_inv] at h
    intro f
    rw [hpp, hqq]
    simp only [sub_self, ENNReal.rpow_zero, ENNReal.rpow_one, one_mul]
    exact h₁ f
  have hθpos : 0 < θ := lt_of_le_of_ne hθ₀ (Ne.symm hθne0)
  have hθlt1 : θ < 1 := lt_of_le_of_ne hθ₁ hθne1
  have h1θ : (0 : ℝ) < 1 - θ := sub_pos.mpr hθlt1
  rcases eq_or_ne M₀ 0 with rfl | hM₀0
  · intro f
    have hq00 : q₀ ≠ 0 := ne_of_gt (one_pos.trans_le hq₀)
    have hTf : T f = 0 := by
      have h0f := h₀ f
      rw [zero_mul] at h0f
      have hz : eLpNorm (T f) q₀ (Measure.count : Measure κ) = 0 :=
        le_antisymm h0f zero_le
      exact (eLpNorm_count_eq_zero_iff hq00 (T f)).mp hz
    have hRHS : ((0 : ENNReal) ^ (1 - θ) * M₁ ^ θ) *
        eLpNorm f p (Measure.count : Measure ι) = 0 := by
      rw [ENNReal.zero_rpow_of_pos h1θ, zero_mul, zero_mul]
    rw [hTf, eLpNorm_zero, hRHS]
  rcases eq_or_ne M₁ 0 with rfl | hM₁0
  · intro f
    have hq10 : q₁ ≠ 0 := ne_of_gt (one_pos.trans_le hq₁)
    have hTf : T f = 0 := by
      have h1f := h₁ f
      rw [zero_mul] at h1f
      have hz : eLpNorm (T f) q₁ (Measure.count : Measure κ) = 0 :=
        le_antisymm h1f zero_le
      exact (eLpNorm_count_eq_zero_iff hq10 (T f)).mp hz
    have hRHS : (M₀ ^ (1 - θ) * (0 : ENNReal) ^ θ) *
        eLpNorm f p (Measure.count : Measure ι) = 0 := by
      rw [ENNReal.zero_rpow_of_pos hθpos, mul_zero, zero_mul]
    rw [hTf, eLpNorm_zero, hRHS]
  rcases eq_or_ne M₀ ⊤ with rfl | hM₀T
  · exact riesz_thorin_top hθpos hθlt1 hp (by simp) hM₁0 (Or.inl rfl) T
  · rcases eq_or_ne M₁ ⊤ with rfl | hM₁T
    · exact riesz_thorin_top hθpos hθlt1 hp hM₀0 (by simp) (Or.inr rfl) T
    · exact riesz_thorin_scale hθpos hθlt1 hp₀ hp₁ hp hq₀ hq₁ hq hp_eq hq_eq
        hM₀T hM₁T T h₀ h₁

/--
**Riesz–Thorin interpolation theorem on finite sets.** Let $\iota$ and $\kappa$ be finite
sets, each with a σ-algebra in which singletons are measurable and with the counting measure, and
write $\|g\|_r \in [0, \infty]$ for the $\ell^r$ norm of $g$ with respect to the counting measure.
Let $p_0, p_1, p, q_0, q_1, q \in [1, \infty]$ and $\theta \in [0, 1]$ satisfy
$1/p = (1-\theta)/p_0 + \theta/p_1$ and $1/q = (1-\theta)/q_0 + \theta/q_1$, where $1/\infty = 0$.
Let $M_0, M_1 \in [0, \infty]$ and let $T : \mathbb{C}^\iota \to \mathbb{C}^\kappa$ be a
$\mathbb{C}$-linear map with $\|Tf\|_{q_0} \le M_0 \|f\|_{p_0}$ and
$\|Tf\|_{q_1} \le M_1 \|f\|_{p_1}$ for all $f \in \mathbb{C}^\iota$. Then
$\|Tf\|_q \le M_0^{1-\theta} M_1^{\theta} \|f\|_p$ for all $f \in \mathbb{C}^\iota$, where
products and powers are computed in $[0, \infty]$ with $0 \cdot \infty = 0$ and $c^0 = 1$.

Proves `Wanted` entry `riesz_thorin`.

Source:
M. Riesz, Sur les maxima des formes bilinéaires et sur les fonctionnelles linéaires,
Acta Math. 49 (1927), 465–497, DOI 10.1007/BF02564121; and G. O. Thorin, Convexity theorems
generalizing those of M. Riesz and Hadamard with some applications,
Comm. Sem. Math. Univ. Lund 9 (1948), 1–58, Riesz-Thorin interpolation theorem; Stein-Shakarchi
Complex interpolation; Lean states finite counting-measure complex `→ₗ[ℂ]` form with explicit
interpolation identities `p⁻¹=(1-θ)p₀⁻¹+θp₁⁻¹` and bound `M₀^(1-θ)M₁^θ`.
-/
theorem riesz_thorin
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace ι] [MeasurableSpace κ]
    [MeasurableSingletonClass ι] [MeasurableSingletonClass κ]
    {p₀ p₁ q₀ q₁ p q : ENNReal}
    {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁) (hp : 1 ≤ p)
    (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q)
    (hp_eq : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hq_eq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    {M₀ M₁ : ENNReal}
    (T : (ι → Complex) →ₗ[Complex] (κ → Complex))
    (h₀ : ∀ f : ι → Complex,
      eLpNorm (T f) q₀ (Measure.count : Measure κ) ≤
        M₀ * eLpNorm f p₀ (Measure.count : Measure ι))
    (h₁ : ∀ f : ι → Complex,
      eLpNorm (T f) q₁ (Measure.count : Measure κ) ≤
        M₁ * eLpNorm f p₁ (Measure.count : Measure ι)) :
    ∀ f : ι → Complex,
      eLpNorm (T f) q (Measure.count : Measure κ) ≤
        (M₀ ^ (1 - θ) * M₁ ^ θ) * eLpNorm f p (Measure.count : Measure ι) := by
  exact riesz_thorin_finite hθ₀ hθ₁ hp₀ hp₁ hp hq₀ hq₁ hq hp_eq hq_eq T h₀ h₁

end MathlibExt.Analysis.FunctionalAnalysis.RieszThorinWanted
end
