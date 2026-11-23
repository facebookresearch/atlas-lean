/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_MvPolynomial_LogMahlerMeasure.lean`,
`Theorems/Thm_MvPolynomial_integrableOn_log_norm_eval_circleMap.lean`,
`Theorems/Thm_Polynomial_log_norm_coeff_le_logMahlerMeasure_add.lean`,
`Theorems/Thm_MvPolynomial_ae_restrict_torusBox_eval_circleMap_ne_zero.lean`
and
`P2M/Sol/S_MvPolynomial_integrableOn_log_norm_eval_circleMap.lean`,
`P2M/Sol/S_Polynomial_log_norm_coeff_le_logMahlerMeasure_add.lean`,
`P2M/Sol/S_MvPolynomial_ae_restrict_torusBox_eval_circleMap_ne_zero.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.TorusIntegral
public import Mathlib.Topology.Algebra.MvPolynomial

@[expose] public section

open MeasureTheory Real

namespace MvPolynomial

variable {n : ℕ}

/-- The box `(0, 2π]ⁿ` in angle space, the domain of the unit torus. -/
noncomputable def torusBox (n : ℕ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ fun _ : Fin n ↦ Set.Ioc 0 (2 * π)

theorem torusBox_def (n : ℕ) :
    torusBox n = Set.pi Set.univ fun _ : Fin n ↦ Set.Ioc 0 (2 * π) := rfl

theorem mem_torusBox {θ : Fin n → ℝ} : θ ∈ torusBox n ↔ ∀ i, θ i ∈ Set.Ioc 0 (2 * π) := by
  simp [torusBox]

theorem measurableSet_torusBox : MeasurableSet (torusBox n) :=
  MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioc

theorem volume_restrict_torusBox (n : ℕ) :
    (volume : Measure (Fin n → ℝ)).restrict (torusBox n) =
      Measure.pi fun _ : Fin n ↦ (volume : Measure ℝ).restrict (Set.Ioc 0 (2 * π)) := by
  rw [torusBox, volume_pi, Measure.restrict_pi_pi]

private theorem continuous_eval_circleMap (P : MvPolynomial (Fin n) ℂ) :
    Continuous fun θ : Fin n → ℝ ↦ eval (fun i ↦ circleMap 0 1 (θ i)) P :=
  (continuous_eval P).comp
    (continuous_pi fun i ↦ (continuous_circleMap 0 1).comp (continuous_apply i))

private theorem measurable_log_norm_eval_circleMap (P : MvPolynomial (Fin n) ℂ) :
    Measurable fun θ : Fin n → ℝ ↦ Real.log ‖eval (fun i ↦ circleMap 0 1 (θ i)) P‖ :=
  measurable_log.comp (continuous_eval_circleMap P).norm.measurable

private theorem norm_eval_circleMap_le_sum_norm_coeff (P : MvPolynomial (Fin n) ℂ)
    (θ : Fin n → ℝ) :
    ‖eval (fun i ↦ circleMap 0 1 (θ i)) P‖ ≤ ∑ m ∈ P.support, ‖P.coeff m‖ := by
  rw [eval_eq]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun m _ ↦ ?_))
  simp [norm_prod, norm_pow]

private noncomputable abbrev circleParamMeasure : Measure ℝ :=
  (volume : Measure ℝ).restrict (Set.Ioc 0 (2 * π))

private noncomputable abbrev torusMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ : Fin n ↦ circleParamMeasure

private instance : IsFiniteMeasure (circleParamMeasure) := by
  unfold circleParamMeasure; infer_instance

private instance : IsFiniteMeasure (torusMeasure n) := by
  unfold torusMeasure; infer_instance

private noncomputable def torusFiber (P : MvPolynomial (Fin (n + 1)) ℂ)
    (θ' : Fin n → ℝ) : Polynomial ℂ :=
  Polynomial.map (eval (fun i ↦ circleMap 0 1 (θ' i))) (finSuccEquiv ℂ n P)

private theorem eval_circleMap_cons (P : MvPolynomial (Fin (n + 1)) ℂ) (x : ℝ)
    (θ' : Fin n → ℝ) :
    eval (fun i ↦ circleMap 0 1 ((Fin.cons x θ' : Fin (n + 1) → ℝ) i)) P =
      (torusFiber P θ').eval (circleMap 0 1 x) := by
  have h : (fun i ↦ circleMap 0 1 ((Fin.cons x θ' : Fin (n + 1) → ℝ) i)) =
      Fin.cons (circleMap 0 1 x) (fun i ↦ circleMap 0 1 (θ' i)) := by
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
  rw [h, eval_eq_eval_mv_eval']
  rfl

private theorem coeff_torusFiber (P : MvPolynomial (Fin (n + 1)) ℂ) (θ' : Fin n → ℝ)
    (k : ℕ) :
    (torusFiber P θ').coeff k =
      eval (fun i ↦ circleMap 0 1 (θ' i)) ((finSuccEquiv ℂ n P).coeff k) := by
  simp [torusFiber, Polynomial.coeff_map]

private theorem natDegree_torusFiber_le (P : MvPolynomial (Fin (n + 1)) ℂ)
    (θ' : Fin n → ℝ) :
    (torusFiber P θ').natDegree ≤ P.degreeOf 0 :=
  Polynomial.natDegree_map_le.trans (natDegree_finSuccEquiv P).le

private noncomputable abbrev torusSplit (n : ℕ) :
    (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
  MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) 0

private theorem torusSplit_symm_apply (z : ℝ × (Fin n → ℝ)) :
    (torusSplit n).symm z = Fin.cons z.1 z.2 := by
  funext j
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply,
    Fin.insertNth_zero']

private theorem measurePreserving_torusSplit (n : ℕ) :
    MeasurePreserving (torusSplit n) (torusMeasure (n + 1))
      (circleParamMeasure.prod (torusMeasure n)) :=
  measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ circleParamMeasure) 0

private theorem finSuccEquiv_ne_zero {P : MvPolynomial (Fin (n + 1)) ℂ} (hP : P ≠ 0) :
    finSuccEquiv ℂ n P ≠ 0 := by
  simpa using (finSuccEquiv ℂ n).injective.ne hP

private theorem Polynomial_finite_setOf_eval_circleMap_eq_zero {p : Polynomial ℂ}
    (hp : p ≠ 0) :
    ({x | p.eval (circleMap 0 1 x) = 0} ∩ Set.Ioc 0 (2 * π)).Finite := by
  apply Set.Finite.of_finite_image (f := circleMap 0 1)
  · refine (p.finite_setOfPred_isRoot hp).subset ?_
    rintro _ ⟨x, ⟨hx, -⟩, rfl⟩
    exact hx
  · have h := injOn_circleMap_of_abs_sub_le (c := (0 : ℂ)) (a := 0) (b := 2 * π)
      one_ne_zero (by simp [abs_of_nonneg two_pi_pos.le])
    rw [Set.uIoc_of_le two_pi_pos.le] at h
    exact h.mono Set.inter_subset_right

private theorem Polynomial_circleParamMeasure_setOf_eval_circleMap_eq_zero
    {p : Polynomial ℂ} (hp : p ≠ 0) :
    circleParamMeasure {x | p.eval (circleMap 0 1 x) = 0} = 0 := by
  rw [circleParamMeasure, Measure.restrict_apply' measurableSet_Ioc]
  exact Polynomial_finite_setOf_eval_circleMap_eq_zero hp |>.measure_zero _

private theorem measurableSet_setOf_eval_circleMap_eq_zero
    (P : MvPolynomial (Fin n) ℂ) :
    MeasurableSet {θ : Fin n → ℝ | eval (fun i ↦ circleMap 0 1 (θ i)) P = 0} :=
  (isClosed_singleton.preimage (continuous_eval_circleMap P)).measurableSet

private theorem ae_eval_circleMap_ne_zero :
    ∀ {n : ℕ} {P : MvPolynomial (Fin n) ℂ}, P ≠ 0 →
      ∀ᵐ θ ∂(torusMeasure n), eval (fun i ↦ circleMap 0 1 (θ i)) P ≠ 0 := by
  intro n
  induction n with
  | zero =>
    intro P hP
    obtain ⟨c, rfl⟩ : ∃ c, P = C c := ⟨_, eq_C_of_isEmpty P⟩
    have hc : c ≠ 0 := by rintro rfl; simp at hP
    exact ae_of_all _ fun θ ↦ by simpa using hc
  | succ n ih =>
    intro P hP
    set S := {θ : Fin (n + 1) → ℝ | eval (fun i ↦ circleMap 0 1 (θ i)) P = 0} with hS_def
    have hS : MeasurableSet S := measurableSet_setOf_eval_circleMap_eq_zero P
    rw [ae_iff]
    simp only [ne_eq, not_not]
    change torusMeasure (n + 1) S = 0
    have hpre : MeasurableSet ((torusSplit n).symm ⁻¹' S) :=
      hS.preimage (torusSplit n).symm.measurable
    rw [← (measurePreserving_torusSplit n).symm.measure_preimage hS.nullMeasurableSet,
      Measure.prod_apply_symm hpre,
      lintegral_eq_zero_iff' (measurable_measure_prodMk_right hpre).aemeasurable]
    set k := (finSuccEquiv ℂ n P).natDegree
    have hQ : (finSuccEquiv ℂ n P).coeff k ≠ 0 := by
      simpa [k] using Polynomial.leadingCoeff_ne_zero.mpr (finSuccEquiv_ne_zero hP)
    filter_upwards [ih hQ] with θ' hθ'
    have hfib : torusFiber P θ' ≠ 0 :=
      fun h ↦ hθ' (by rw [← coeff_torusFiber, h, Polynomial.coeff_zero])
    have hthis : (fun x : ℝ ↦ (x, θ')) ⁻¹' ((torusSplit n).symm ⁻¹' S) =
        {x | (torusFiber P θ').eval (circleMap 0 1 x) = 0} := by
      ext x
      simp [hS_def, torusSplit_symm_apply, eval_circleMap_cons,
        -MeasurableEquiv.piFinSuccAbove_symm_apply]
    simp only [Pi.zero_apply, hthis]
    exact Polynomial_circleParamMeasure_setOf_eval_circleMap_eq_zero hfib

private theorem ae_restrict_torusBox_eval_circleMap_ne_zero {P : MvPolynomial (Fin n) ℂ}
    (hP : P ≠ 0) :
    ∀ᵐ θ ∂(volume.restrict (torusBox n)),
      eval (fun i ↦ circleMap 0 1 (θ i)) P ≠ 0 := by
  rw [volume_restrict_torusBox]
  exact ae_eval_circleMap_ne_zero hP

private theorem Real_abs_log_eq_two_mul_posLog_sub_log (t : ℝ) :
    |Real.log t| = 2 * t.posLog - Real.log t := by
  rw [Real.posLog_apply]
  rcases le_total 0 (Real.log t) with h | h
  · rw [max_eq_right h, abs_of_nonneg h]; ring
  · rw [max_eq_left h, abs_of_nonpos h]; ring

private theorem Polynomial_integral_log_norm_eval_circleMap (p : Polynomial ℂ) :
    ∫ x in Set.Ioc 0 (2 * π), Real.log ‖p.eval (circleMap 0 1 x)‖ =
      (2 * π) * p.logMahlerMeasure := by
  rw [p.logMahlerMeasure_def, Real.circleAverage_def, smul_eq_mul,
    intervalIntegral.integral_of_le two_pi_pos.le, ← mul_assoc,
    mul_inv_cancel₀ two_pi_pos.ne', one_mul]

private theorem Polynomial_integrableOn_log_norm_eval_circleMap (p : Polynomial ℂ) :
    IntegrableOn (fun x ↦ Real.log ‖p.eval (circleMap 0 1 x)‖) (Set.Ioc 0 (2 * π)) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).mp
    p.intervalIntegrable_mahlerMeasure

private theorem Polynomial_log_norm_coeff_le_logMahlerMeasure_add {p : Polynomial ℂ}
    {k : ℕ} (hk : p.coeff k ≠ 0) :
    Real.log ‖p.coeff k‖ ≤ p.logMahlerMeasure + p.natDegree * Real.log 2 := by
  have hp : p ≠ 0 := fun h ↦ hk (by simp [h])
  have hkn : k ≤ p.natDegree := Polynomial.le_natDegree_of_ne_zero hk
  have hchoose : (0 : ℝ) < p.natDegree.choose k := by exact_mod_cast Nat.choose_pos hkn
  have h1 := p.norm_coeff_le_choose_mul_mahlerMeasure k
  have hM := p.mahlerMeasure_pos_of_ne_zero hp
  calc Real.log ‖p.coeff k‖
      ≤ Real.log (p.natDegree.choose k * p.mahlerMeasure) :=
        Real.log_le_log (norm_pos_iff.mpr hk) h1
    _ = Real.log (p.natDegree.choose k) + p.logMahlerMeasure := by
        rw [Real.log_mul hchoose.ne' hM.ne', p.logMahlerMeasure_eq_log_MahlerMeasure]
    _ ≤ p.natDegree * Real.log 2 + p.logMahlerMeasure := by
        gcongr
        rw [← Real.log_pow]
        exact Real.log_le_log hchoose (by exact_mod_cast Nat.choose_le_two_pow _ _)
    _ = _ := add_comm _ _

private theorem Polynomial_integral_abs_log_norm_eval_circleMap_le (p : Polynomial ℂ)
    {B : ℝ} (hB : ∀ x : ℝ, ‖p.eval (circleMap 0 1 x)‖ ≤ B) {k : ℕ}
    (hk : p.coeff k ≠ 0) :
    ∫ x in Set.Ioc 0 (2 * π), |Real.log ‖p.eval (circleMap 0 1 x)‖| ≤
      2 * (2 * π) * B.posLog + (2 * π) * (p.natDegree * Real.log 2) -
        (2 * π) * Real.log ‖p.coeff k‖ := by
  have hint := Polynomial_integrableOn_log_norm_eval_circleMap p
  have hle : ∀ x, |Real.log ‖p.eval (circleMap 0 1 x)‖| ≤
      2 * B.posLog - Real.log ‖p.eval (circleMap 0 1 x)‖ := by
    intro x
    rw [Real_abs_log_eq_two_mul_posLog_sub_log]
    gcongr 2 * ?_ - _
    exact Real.posLog_le_posLog (le_trans (by norm_num) (norm_nonneg _)) (hB x)
  calc ∫ x in Set.Ioc 0 (2 * π), |Real.log ‖p.eval (circleMap 0 1 x)‖|
      ≤ ∫ x in Set.Ioc 0 (2 * π), (2 * B.posLog - Real.log ‖p.eval (circleMap 0 1 x)‖) :=
        integral_mono hint.abs ((integrable_const _).sub hint) hle
    _ = 2 * (2 * π) * B.posLog - (2 * π) * p.logMahlerMeasure := by
        rw [integral_sub (integrable_const _) hint, setIntegral_const,
          Polynomial_integral_log_norm_eval_circleMap]
        simp [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal Real.pi_pos.le]
        ring
    _ ≤ _ := by
        have h := Polynomial_log_norm_coeff_le_logMahlerMeasure_add hk
        nlinarith [two_pi_pos, h]

private theorem integrable_log_norm_eval_circleMap :
    ∀ {n : ℕ} (P : MvPolynomial (Fin n) ℂ),
      Integrable (fun θ : Fin n → ℝ ↦ Real.log ‖eval (fun i ↦ circleMap 0 1 (θ i)) P‖)
        (torusMeasure n) := by
  intro n
  induction n with
  | zero =>
    intro P
    obtain ⟨c, rfl⟩ : ∃ c, P = C c := ⟨_, eq_C_of_isEmpty P⟩
    simp
  | succ n ih =>
    intro P
    by_cases hP : P = 0
    · subst hP; simp
    set F := fun θ : Fin (n + 1) → ℝ ↦ Real.log ‖eval (fun i ↦ circleMap 0 1 (θ i)) P‖
      with hF_def
    set G : ℝ × (Fin n → ℝ) → ℝ :=
      fun z ↦ Real.log ‖(torusFiber P z.2).eval (circleMap 0 1 z.1)‖ with hG_def
    have hFG : F ∘ (torusSplit n).symm = G := by
      funext z
      simp [hF_def, hG_def, torusSplit_symm_apply, eval_circleMap_cons,
        -MeasurableEquiv.piFinSuccAbove_symm_apply]
    have hGm : Measurable G :=
      hFG ▸ (measurable_log_norm_eval_circleMap P).comp (torusSplit n).symm.measurable
    rw [← (measurePreserving_torusSplit n).symm.integrable_comp_emb
      (torusSplit n).symm.measurableEmbedding, hFG,
      integrable_prod_iff' hGm.aestronglyMeasurable]
    refine ⟨ae_of_all _ fun θ' ↦ Polynomial_integrableOn_log_norm_eval_circleMap
      (torusFiber P θ'), ?_⟩
    set k := (finSuccEquiv ℂ n P).natDegree
    set Q := (finSuccEquiv ℂ n P).coeff k with hQ_def
    have hQ : Q ≠ 0 := by
      simpa [Q, k] using Polynomial.leadingCoeff_ne_zero.mpr (finSuccEquiv_ne_zero hP)
    set B := ∑ m ∈ P.support, ‖P.coeff m‖
    set d := P.degreeOf 0
    have hg : Integrable (fun θ' : Fin n → ℝ ↦ 2 * (2 * π) * B.posLog +
        (2 * π) * (d * Real.log 2) +
        (2 * π) * |Real.log ‖eval (fun i ↦ circleMap 0 1 (θ' i)) Q‖|) (torusMeasure n) :=
      (integrable_const _).add ((ih Q).abs.const_mul _)
    refine hg.mono' (hGm.norm.stronglyMeasurable.integral_prod_left).aestronglyMeasurable ?_
    filter_upwards [ae_eval_circleMap_ne_zero hQ] with θ' hθ'
    have hk : (torusFiber P θ').coeff k ≠ 0 := by rwa [coeff_torusFiber]
    have hBx : ∀ x : ℝ, ‖(torusFiber P θ').eval (circleMap 0 1 x)‖ ≤ B := fun x ↦ by
      rw [← eval_circleMap_cons]; exact norm_eval_circleMap_le_sum_norm_coeff P _
    have hmain : ∫ x, |Real.log ‖(torusFiber P θ').eval (circleMap 0 1 x)‖|
        ∂circleParamMeasure ≤
        2 * (2 * π) * B.posLog + (2 * π) * ((torusFiber P θ').natDegree * Real.log 2) -
          (2 * π) * Real.log ‖eval (fun i ↦ circleMap 0 1 (θ' i)) Q‖ := by
      have h := Polynomial_integral_abs_log_norm_eval_circleMap_le (torusFiber P θ') hBx hk
      rwa [coeff_torusFiber] at h
    have hdeg : ((torusFiber P θ').natDegree : ℝ) ≤ d := by
      exact_mod_cast natDegree_torusFiber_le P θ'
    have h2 : (2 * π) * ((torusFiber P θ').natDegree * Real.log 2) ≤
        (2 * π) * (d * Real.log 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hdeg (Real.log_pos one_lt_two).le) two_pi_pos.le
    have h3 : -((2 * π) * Real.log ‖eval (fun i ↦ circleMap 0 1 (θ' i)) Q‖) ≤
        (2 * π) * |Real.log ‖eval (fun i ↦ circleMap 0 1 (θ' i)) Q‖| := by
      rw [← mul_neg]
      exact mul_le_mul_of_nonneg_left (neg_le_abs _) two_pi_pos.le
    have hnn : 0 ≤ ∫ x, ‖G (x, θ')‖ ∂circleParamMeasure :=
      integral_nonneg fun _ ↦ norm_nonneg _
    rw [Real.norm_of_nonneg hnn]
    simp only [hG_def, Real.norm_eq_abs]
    linarith

/-- For every multivariate complex polynomial, the logarithm of the norm of
its evaluation on the unit torus is integrable over `(0, 2π]ⁿ`. This includes
the zero polynomial and the case `n = 0`, with `Real.log` totalized. -/
theorem integrableOn_log_norm_eval_circleMap {n : ℕ} (P : MvPolynomial (Fin n) ℂ) :
    IntegrableOn
      (fun θ : Fin n → ℝ ↦ Real.log ‖eval (fun i ↦ circleMap 0 1 (θ i)) P‖)
      (torusBox n) := by
  rw [IntegrableOn, volume_restrict_torusBox]
  exact integrable_log_norm_eval_circleMap P

end MvPolynomial
