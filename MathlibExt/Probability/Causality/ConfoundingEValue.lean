/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.NormNum
public import MathlibExt.Probability.Causality.ConfoundingBounds

/-!
# Sharpness and the confounding E-value

The equality statements concern standardization of risk kernels. They cover
positive target standardized risk ratios and exposure prevalences in `(0, 1)`.

T. J. VanderWeele and P. Ding, *Sensitivity analysis in observational research:
Introducing the E-value*, Annals of Internal Medicine 167 (2017), 268–274.
-/

@[expose] public section

namespace MathlibExt.Probability.Causality

open scoped BigOperators

/-- The confounding E-value of a positive risk ratio. Below one, orient the
comparison by exchanging the exposure arms. -/
noncomputable def confoundingEValue (rr : ℝ) : ℝ :=
  let x := if rr < 1 then rr⁻¹ else rr
  x + Real.sqrt (x * (x - 1))

/-- At the null the E-value is one. -/
theorem confoundingEValue_one : confoundingEValue 1 = 1 := by
  simp [confoundingEValue]

/-- The diagonal bounding factor at the E-value recovers the input ratio. -/
theorem confoundingBoundingFactor_eValue {rr : ℝ} (hrr : 1 ≤ rr) :
    confoundingBoundingFactor (confoundingEValue rr) (confoundingEValue rr) = rr := by
  have hr : 0 ≤ rr * (rr - 1) :=
    mul_nonneg (by linarith) (sub_nonneg.mpr hrr)
  have hs := Real.sqrt_nonneg (rr * (rr - 1))
  have hsq := Real.sq_sqrt hr
  have hd : 0 < (rr + Real.sqrt (rr * (rr - 1))) +
      (rr + Real.sqrt (rr * (rr - 1))) - 1 := by linarith
  simp only [confoundingEValue, ite_eq_right (not_lt.mpr hrr)]
  unfold confoundingBoundingFactor
  apply (div_eq_iff hd.ne').mpr
  nlinarith [hsq]

namespace FiniteRiskModel

/-- The generalized Cornfield high threshold. -/
theorem cornfield_high_threshold {n : ℕ} (m : FiniteRiskModel n)
    (h : 1 ≤ m.confoundingRR) :
    confoundingEValue m.confoundingRR ≤ max m.exposureConfounderRR m.confounderOutcomeRR := by
  let x := m.exposureConfounderRR
  let y := m.confounderOutcomeRR
  let M := max x y
  have hx : 1 ≤ x := m.exposureConfounderRR_one_le
  have hy : 1 ≤ y := m.confounderOutcomeRR_one_le
  have hM : 1 ≤ M := hx.trans (le_max_left _ _)
  have hsym (a b : ℝ) : confoundingBoundingFactor a b =
      confoundingBoundingFactor b a := by
    simp only [confoundingBoundingFactor, mul_comm a b, add_comm a b]
  have hdiag : confoundingBoundingFactor x y ≤ confoundingBoundingFactor M M := by
    calc
      _ ≤ confoundingBoundingFactor x M :=
        confoundingBoundingFactor_mono_right hx hy (le_max_right _ _)
      _ = confoundingBoundingFactor M x := hsym x M
      _ ≤ confoundingBoundingFactor M M :=
        confoundingBoundingFactor_mono_right hM hx (le_max_left _ _)
  have hb := (m.confoundingRR_le_boundingFactor).trans hdiag
  have hd : 0 < M + M - 1 := by linarith
  change m.confoundingRR ≤ M * M / (M + M - 1) at hb
  have hb' := (le_div_iff₀ hd).mp hb
  have hrM : m.confoundingRR ≤ M :=
    (m.cornfield_low_threshold).trans ((min_le_left _ _).trans (le_max_left _ _))
  have hs := Real.sqrt_nonneg (m.confoundingRR * (m.confoundingRR - 1))
  have hsq := Real.sq_sqrt (mul_nonneg (by linarith : 0 ≤ m.confoundingRR)
    (sub_nonneg.mpr h))
  simp only [confoundingEValue, ite_eq_right (not_lt.mpr h)]
  change m.confoundingRR + Real.sqrt (m.confoundingRR * (m.confoundingRR - 1)) ≤ M
  nlinarith [hb', hsq]

/-- The high threshold expressed in observed and standardized risk ratios. -/
theorem high_threshold_eq_ratio {n : ℕ} (m : FiniteRiskModel n)
    (h : m.standardizedRR ≤ m.observedRR) :
    confoundingEValue m.confoundingRR =
      (m.observedRR + Real.sqrt (m.observedRR * (m.observedRR - m.standardizedRR))) /
        m.standardizedRR := by
  have hs := m.standardizedRR_pos
  have hr : 1 ≤ m.confoundingRR := (one_le_div hs).mpr h
  have hn : 0 ≤ m.observedRR * (m.observedRR - m.standardizedRR) :=
    mul_nonneg m.observedRR_pos.le (sub_nonneg.mpr h)
  have he : m.confoundingRR * (m.confoundingRR - 1) =
      (m.observedRR * (m.observedRR - m.standardizedRR)) / m.standardizedRR ^ 2 := by
    unfold confoundingRR
    field_simp
  simp only [confoundingEValue, ite_eq_right (not_lt.mpr hr)]
  rw [he, Real.sqrt_div hn, Real.sqrt_sq hs.le]
  unfold confoundingRR
  ring

/-- E-value necessity for explaining an observed risk ratio above one. -/
theorem confoundingEValue_le_max {n : ℕ} (m : FiniteRiskModel n)
    (h : 1 < m.observedRR) (hnull : m.standardizedRR = 1) :
    confoundingEValue m.observedRR ≤ max m.exposureConfounderRR m.confounderOutcomeRR := by
  have hr : m.confoundingRR = m.observedRR := by simp [confoundingRR, hnull]
  simpa only [hr] using m.cornfield_high_threshold (by rw [hr]; exact h.le)

private noncomputable def twoLevelLaw (q : ℝ) (hq : q ∈ Set.Icc 0 1) :
    Convexity.StdSimplex ℝ (Fin 2) :=
  Convexity.StdSimplex.duple 0 1 (sub_nonneg.mpr hq.2) hq.1 (sub_add_cancel 1 q)

private theorem sup_fin_two (f : Fin 2 → ℝ) :
    Finset.univ.sup' Finset.univ_nonempty f = max (f 0) (f 1) := by
  have h : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  simp only [h]
  rfl

private theorem inf_fin_two (f : Fin 2 → ℝ) :
    Finset.univ.inf' Finset.univ_nonempty f = min (f 0) (f 1) := by
  have h : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  simp only [h]
  rfl

private noncomputable def binaryScale (y β : ℝ) : ℝ := 1 / (2 * max 1 β * y)

private theorem binaryScale_pos {y β : ℝ} (hy : 1 ≤ y) : 0 < binaryScale y β := by
  unfold binaryScale
  have hM : 0 < max 1 β := zero_lt_one.trans_le (le_max_left _ _)
  have hy0 : 0 < y := by linarith
  positivity

private noncomputable def binaryModel {q₀ q₁ y p β : ℝ}
    (hq₀ : q₀ ∈ Set.Ioo 0 1) (hq₁ : q₁ ∈ Set.Icc 0 1)
    (hy : 1 ≤ y) (hp : p ∈ Set.Ioo 0 1) (hβ : 0 < β) : FiniteRiskModel 1 where
  exposureProb := p
  exposureProb_mem := hp
  confounderLaw e := if e then twoLevelLaw q₁ hq₁
    else twoLevelLaw q₀ ⟨hq₀.1.le, hq₀.2.le⟩
  control_mass_pos u := by
    fin_cases u
    · simpa [twoLevelLaw, Convexity.StdSimplex.weights_duple] using sub_pos.mpr hq₀.2
    · simpa [twoLevelLaw, Convexity.StdSimplex.weights_duple] using hq₀.1
  risk e := if e then ![β * binaryScale y β, β * binaryScale y β * y]
    else ![binaryScale y β, binaryScale y β * y]
  risk_mem e u := by
    have ha := binaryScale_pos (β := β) hy
    have hM : 0 < max 1 β := zero_lt_one.trans_le (le_max_left _ _)
    have hy0 : 0 < y := by linarith
    have hhigh : binaryScale y β * y = 1 / (2 * max 1 β) := by
      unfold binaryScale
      field_simp
    have hhigh_le : binaryScale y β * y ≤ 1 := by
      rw [hhigh, div_le_one (by positivity)]
      linarith [le_max_left (1 : ℝ) β]
    have hβhigh_le : β * binaryScale y β * y ≤ 1 := by
      rw [mul_assoc, hhigh, mul_one_div, div_le_one (by positivity)]
      linarith [le_max_right (1 : ℝ) β]
    have halow : binaryScale y β ≤ binaryScale y β * y := by
      nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hy)]
    fin_cases u <;> cases e
    · exact ⟨ha, halow.trans hhigh_le⟩
    · exact ⟨mul_pos hβ ha, (mul_le_mul_of_nonneg_left halow hβ.le).trans
        (by simpa only [mul_assoc] using hβhigh_le)⟩
    · exact ⟨mul_pos ha hy0, hhigh_le⟩
    · exact ⟨mul_pos (mul_pos hβ ha) hy0, hβhigh_le⟩

private theorem binaryModel_mass {q₀ q₁ y p β : ℝ}
    (hq₀ : q₀ ∈ Set.Ioo 0 1) (hq₁ : q₁ ∈ Set.Icc 0 1)
    (hy : 1 ≤ y) (hp : p ∈ Set.Ioo 0 1) (hβ : 0 < β) :
    let m := binaryModel hq₀ hq₁ hy hp hβ
    m.mass false 0 = 1 - q₀ ∧ m.mass false 1 = q₀ ∧
      m.mass true 0 = 1 - q₁ ∧ m.mass true 1 = q₁ := by
  simp [mass, binaryModel, twoLevelLaw, Convexity.StdSimplex.weights_duple]

private theorem binaryModel_outcome {q₀ q₁ y p β : ℝ}
    (hq₀ : q₀ ∈ Set.Ioo 0 1) (hq₁ : q₁ ∈ Set.Icc 0 1)
    (hy : 1 ≤ y) (hp : p ∈ Set.Ioo 0 1) (hβ : 0 < β) :
    (binaryModel hq₀ hq₁ hy hp hβ).confounderOutcomeRR = y := by
  let m := binaryModel hq₀ hq₁ hy hp hβ
  have ha := binaryScale_pos (β := β) hy
  have halow : binaryScale y β ≤ binaryScale y β * y := by
    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hy)]
  have he (e : Bool) : m.armConfounderOutcomeRR e = y := by
    rw [armConfounderOutcomeRR, sup_fin_two, inf_fin_two]
    cases e
    · change max (binaryScale y β) (binaryScale y β * y) /
        min (binaryScale y β) (binaryScale y β * y) = y
      rw [max_eq_right halow, min_eq_left halow]
      field_simp
    · change max (β * binaryScale y β) (β * binaryScale y β * y) /
        min (β * binaryScale y β) (β * binaryScale y β * y) = y
      have hb : β * binaryScale y β ≤ β * binaryScale y β * y := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left halow hβ.le
      rw [max_eq_right hb, min_eq_left hb]
      field_simp
  exact show max (m.armConfounderOutcomeRR true) (m.armConfounderOutcomeRR false) = y
    by rw [he true, he false, max_self]

private theorem binaryModel_standardized {q₀ q₁ y p β : ℝ}
    (hq₀ : q₀ ∈ Set.Ioo 0 1) (hq₁ : q₁ ∈ Set.Icc 0 1)
    (hy : 1 ≤ y) (hp : p ∈ Set.Ioo 0 1) (hβ : 0 < β) :
    (binaryModel hq₀ hq₁ hy hp hβ).standardizedRR = β := by
  let m := binaryModel hq₀ hq₁ hy hp hβ
  have hscale (u : Fin 2) : m.risk true u = β * m.risk false u := by
    fin_cases u <;> simp [m, binaryModel, mul_assoc]
  have hstd : m.standardizedRisk true = β * m.standardizedRisk false := by
    simp only [standardizedRisk, hscale, mul_assoc, Finset.mul_sum]
  change m.standardizedRisk true / m.standardizedRisk false = β
  rw [hstd]
  exact mul_div_cancel_right₀ β (m.standardizedRisk_pos false).ne'

/-- The population-standardized bound is attained by a binary risk kernel
at any two association strengths above one. -/
theorem confoundingBoundingFactor_attained {x y p β : ℝ}
    (hx : 1 < x) (hy : 1 < y) (hp : p ∈ Set.Ioo 0 1) (hβ : 0 < β) :
    ∃ m : FiniteRiskModel 1, m.exposureProb = p ∧
      m.exposureConfounderRR = x ∧ m.confounderOutcomeRR = y ∧
      m.standardizedRR = β ∧ m.confoundingRR = confoundingBoundingFactor x y := by
  have hx0 : 0 < x := by linarith
  have hq₀ : 1 / x ∈ Set.Ioo 0 1 :=
    ⟨one_div_pos.mpr hx0, (div_lt_one hx0).mpr hx⟩
  have hq₁ : (1 : ℝ) ∈ Set.Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  let m := binaryModel hq₀ hq₁ hy.le hp hβ
  obtain ⟨hf0, hf1, ht0, ht1⟩ := binaryModel_mass hq₀ hq₁ hy.le hp hβ
  have hEU : m.exposureConfounderRR = x := by
    rw [exposureConfounderRR, sup_fin_two, ht0, ht1, hf0, hf1]
    simp only [sub_self, zero_div, one_div, inv_inv, max_eq_right hx0.le]
  have hstd : m.standardizedRR = β := binaryModel_standardized hq₀ hq₁ hy.le hp hβ
  refine ⟨m, rfl, hEU, binaryModel_outcome hq₀ hq₁ hy.le hp hβ, hstd, ?_⟩
  have ha := binaryScale_pos (β := β) hy.le
  have hd : 0 < x + y - 1 := by linarith
  have hc : binaryScale y β * (1 - 1 / x) + binaryScale y β * y * (1 / x) =
      binaryScale y β * (x + y - 1) / x := by
    field_simp
    ring
  rw [confoundingRR, hstd, observedRR, observedRisk, observedRisk,
    Fin.sum_univ_two, Fin.sum_univ_two, ht0, ht1, hf0, hf1]
  change ((β * binaryScale y β) * (1 - 1) +
    (β * binaryScale y β * y) * 1) /
    (binaryScale y β * (1 - 1 / x) + (binaryScale y β * y) * (1 / x)) / β = _
  simp only [sub_self, mul_zero, zero_add, mul_one]
  rw [hc]
  unfold confoundingBoundingFactor
  field_simp

/-- Boundary attainment at exposure-confounder strength one, with both
confounder laws strictly positive. -/
theorem confoundingBoundingFactor_attained_one_left {y p β : ℝ}
    (hy : 1 ≤ y) (hp : p ∈ Set.Ioo 0 1) (hβ : 0 < β) :
    ∃ m : FiniteRiskModel 1, m.exposureProb = p ∧ (∀ u, 0 < m.mass true u) ∧
      m.exposureConfounderRR = 1 ∧ m.confounderOutcomeRR = y ∧
      m.standardizedRR = β ∧ m.confoundingRR = confoundingBoundingFactor 1 y := by
  have hq : (1 / 2 : ℝ) ∈ Set.Ioo 0 1 := by norm_num [Set.mem_Ioo]
  let m := binaryModel hq ⟨hq.1.le, hq.2.le⟩ hy hp hβ
  obtain ⟨hf0, hf1, ht0, ht1⟩ := binaryModel_mass hq ⟨hq.1.le, hq.2.le⟩ hy hp hβ
  have hmass : ∀ u, m.mass true u = m.mass false u := by
    intro u
    rfl
  have hEU : m.exposureConfounderRR = 1 := by
    rw [exposureConfounderRR]
    have hr (u : Fin 2) : m.mass true u / m.mass false u = 1 := by
      rw [hmass u]
      exact div_self (m.control_mass_pos u).ne'
    simp [hr]
  have hstd := binaryModel_standardized hq ⟨hq.1.le, hq.2.le⟩ hy hp hβ
  have hobs : m.observedRR = m.standardizedRR := by
    have hmarg (u : Fin 2) : m.marginalMass u = m.mass false u := by
      rw [marginalMass, hmass]
      ring
    unfold observedRR standardizedRR observedRisk standardizedRisk
    simp only [hmass, hmarg]
  refine ⟨m, rfl, ?_, hEU, binaryModel_outcome hq ⟨hq.1.le, hq.2.le⟩ hy hp hβ,
    hstd, ?_⟩
  · intro u
    rw [hmass]
    exact m.control_mass_pos u
  · rw [confoundingRR, hobs, div_self m.standardizedRR_pos.ne',
      confoundingBoundingFactor_one_left hy]

/-- Boundary attainment at confounder-outcome strength one, with both
confounder laws strictly positive. -/
theorem confoundingBoundingFactor_attained_one_right {x p β : ℝ}
    (hx : 1 ≤ x) (hp : p ∈ Set.Ioo 0 1) (hβ : 0 < β) :
    ∃ m : FiniteRiskModel 1, m.exposureProb = p ∧ (∀ u, 0 < m.mass true u) ∧
      m.exposureConfounderRR = x ∧ m.confounderOutcomeRR = 1 ∧
      m.standardizedRR = β ∧ m.confoundingRR = confoundingBoundingFactor x 1 := by
  have hx0 : 0 < x := by linarith
  have hq₀ : 1 / (2 * x) ∈ Set.Ioo 0 1 := by
    constructor
    · positivity
    · apply (div_lt_one (by positivity : 0 < 2 * x)).mpr
      linarith
  have hq₁ : (1 / 2 : ℝ) ∈ Set.Icc 0 1 := by norm_num [Set.mem_Icc]
  let m := binaryModel hq₀ hq₁ (le_refl 1) hp hβ
  obtain ⟨hf0, hf1, ht0, ht1⟩ := binaryModel_mass hq₀ hq₁ (le_refl 1) hp hβ
  have hratio1 : (1 / 2 : ℝ) / (1 / (2 * x)) = x := by field_simp
  have hratio0 : (1 - 1 / 2 : ℝ) / (1 - 1 / (2 * x)) ≤ x := by
    have hd : 0 < 1 - 1 / (2 * x) := sub_pos.mpr hq₀.2
    apply (div_le_iff₀ hd).mpr
    have he : x * (1 - 1 / (2 * x)) = x - 1 / 2 := by
      field_simp
    rw [he]
    linarith
  have hEU : m.exposureConfounderRR = x := by
    rw [exposureConfounderRR, sup_fin_two, ht0, ht1, hf0, hf1, hratio1]
    exact max_eq_right hratio0
  have hstd := binaryModel_standardized hq₀ hq₁ (le_refl 1) hp hβ
  have hrisk (e : Bool) (u : Fin 2) : m.risk e u =
      if e then β * binaryScale 1 β else binaryScale 1 β := by
    fin_cases u <;> cases e <;> simp [m, binaryModel]
  have hobs : m.observedRR = β := by
    unfold observedRR observedRisk
    simp only [hrisk, Bool.false_eq_true, ↓reduceIte, ← Finset.mul_sum]
    have hs (e : Bool) : ∑ u, m.mass e u = 1 := (m.confounderLaw e).total_of_fintype
    rw [hs true, hs false, mul_one, mul_one]
    exact mul_div_cancel_right₀ β (binaryScale_pos (β := β) (le_refl 1)).ne'
  refine ⟨m, rfl, ?_, hEU, binaryModel_outcome hq₀ hq₁ (le_refl 1) hp hβ, hstd, ?_⟩
  · intro u
    fin_cases u <;> norm_num [m, mass, binaryModel, twoLevelLaw,
      Convexity.StdSimplex.weights_duple]
  · rw [confoundingRR, hobs, hstd, div_self hβ.ne',
      confoundingBoundingFactor_one_right hx]

/-- A finite binary risk-kernel model explains the observed association at
exactly the E-value in both sensitivity parameters. -/
theorem confoundingEValue_attained {rr p : ℝ} (hrr : 1 < rr) (hp : p ∈ Set.Ioo 0 1) :
    ∃ m : FiniteRiskModel 1, m.exposureProb = p ∧
      m.observedRR = rr ∧ m.standardizedRR = 1 ∧
      m.exposureConfounderRR = confoundingEValue rr ∧
      m.confounderOutcomeRR = confoundingEValue rr := by
  have hE : 1 < confoundingEValue rr := by
    simp only [confoundingEValue, ite_eq_right (not_lt.mpr hrr.le)]
    linarith [Real.sqrt_nonneg (rr * (rr - 1))]
  obtain ⟨m, hp', hx, hy, hs, hc⟩ := confoundingBoundingFactor_attained
    hE hE hp (show (0 : ℝ) < 1 by norm_num)
  refine ⟨m, hp', ?_, hs, hx, hy⟩
  rw [confoundingBoundingFactor_eValue hrr.le] at hc
  simpa [confoundingRR, hs] using hc

end FiniteRiskModel

end MathlibExt.Probability.Causality
