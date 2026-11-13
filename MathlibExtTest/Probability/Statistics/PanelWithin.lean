/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.PanelWithin

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Probability.Independence.Basic

/-!
# Tests for within-estimator consistency

Concrete two-period (`Fin 2`), single-regressor (`Fin 1`) panels exercising
the within (fixed-effects) estimator:

* `withinEstimator_noiseless_concrete` and `tendsto_withinEstimator_noiseless`:
  exact recovery and convergence on a noiseless panel.
* `withinGram_timeInvariant_not_unit`: time-invariant regressors are erased by
  demeaning, so the Gram matrix can never be invertible.
* `periodic_alternating_survives`: zero-mean alternating regressors survive
  demeaning (only the time-invariant component is removed).
* `lsdv_slope_noiseless`: the dummy-variable (LSDV) slope of the stacked
  noiseless panel is the within estimator, through
  `lsdv_slope_eq_withinEstimator`.
* `feedback_sequentialExogeneity`, `feedback_integral_score` and
  `sequentialExogeneity_not_estimatingEquation`: on a two-point probability
  space with a mean-zero shock `ε`, regressors `X₁ = 0`, `X₂ = ε` and errors
  `u₁ = ε`, `u₂ = 0` are sequentially exogenous (each error has conditional
  mean zero given the current and past regressors), yet the expected within
  score is `-1 / 2`. Feedback from an error to a future regressor is mixed into
  every period by demeaning, so sequential exogeneity does not give the
  estimating equation `hEE` of `tendsto_withinEstimator`.
* `integral_withinScore_concrete`, `integral_mul_concrete`, and
  `tendsto_withinEstimator_degenerate`: end-to-end use of the integral lemmas
  and of consistency on a degenerate (Dirac) probability space.

Unit roots are nonstationarity across periods, not across clusters. With the
finite period set `τ` fixed, independently replicated unit-root paths can
satisfy the cross-cluster independence, identical distribution, integrability
and identification hypotheses of `tendsto_withinEstimator` (the estimating
equation `hEE` is a separate condition), so the consistency result can apply to
them as `N → ∞`. Outside its scope are time-series (`T → ∞`) asymptotics and
triangular arrays whose cluster laws change with `N`; no formal exhibit is
attempted for those.
-/

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.PanelWithin

open MeasureTheory ProbabilityTheory Topology Filter Matrix
open MathlibExt.Probability.Statistics.PanelWithin
open MathlibExt.Probability.Statistics.WithinEstimator (groupDummy dummy_mulVec_apply)
open scoped ENNReal

/-- Varying regressor, rows `1` and `-1` (already mean-zero). -/
noncomputable def testX0 : Matrix (Fin 2) (Fin 1) ℝ :=
  Matrix.of fun t _ => if t = 0 then (1 : ℝ) else -1

/-- Constant regressor, every entry `5` (time-invariant). -/
noncomputable def testXc : Matrix (Fin 2) (Fin 1) ℝ :=
  Matrix.of fun _ _ => 5

/-- Panel regressors, constant across clusters. -/
noncomputable def testX : ℕ → Unit → Matrix (Fin 2) (Fin 1) ℝ :=
  fun _ _ => testX0

/-- Time-invariant panel regressors, constant across clusters. -/
noncomputable def testXconst : ℕ → Unit → Matrix (Fin 2) (Fin 1) ℝ :=
  fun _ _ => testXc

/-- Zero panel errors. -/
noncomputable def testU : ℕ → Unit → Fin 2 → ℝ := fun _ _ => 0

/-- Cluster-varying individual effects, erased by demeaning. -/
noncomputable def testC : ℕ → Unit → ℝ := fun i _ => (i : ℝ)

/-- True coefficient. -/
noncomputable def testB : Fin 1 → ℝ := fun _ => 3

/-- Panel outcomes from the static equation. -/
noncomputable def testY : ℕ → Unit → Fin 2 → ℝ :=
  fun i ω => testX i ω *ᵥ testB + (fun _ => testC i ω) + testU i ω

/-- Degenerate probability space. -/
noncomputable def testP : Measure Unit := Measure.dirac ()

/-- `testP` is a probability measure. -/
private instance : IsProbabilityMeasure testP :=
  Measure.dirac.isProbabilityMeasure

/-- Demeaned Gram entry of `testX0` equals `2`. -/
private theorem gram_entry_testX0 :
    ((centering (Fin 2) * testX0)ᵀ * (centering (Fin 2) * testX0)) 0 0
      = 2 := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  simp only [centering, testX0, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.one_apply, Matrix.of_apply]
  norm_num

/-- Panel Gram entry: `N` identical clusters contribute `2` each. -/
private theorem panel_gram_entry (N : ℕ) (ω : Unit) :
    (withinGram testX N ω) 0 0 = N * 2 := by
  have hterm : ∀ i, ((centering (Fin 2) * testX i ω)ᵀ
      * (centering (Fin 2) * testX i ω)) 0 0 = 2 :=
    fun _ => gram_entry_testX0
  simp only [withinGram_eq_sum_centering, Matrix.sum_apply, hterm, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]

/-- The noiseless panel Gram matrix is invertible for `N ≥ 1`. -/
private theorem panel_gram_unit {N : ℕ} (ω : Unit) (hN : 1 ≤ N) :
    IsUnit (withinGram testX N ω).det := by
  rw [Matrix.det_fin_one, panel_gram_entry N ω]
  apply isUnit_iff_ne_zero.mpr
  have hNe : N ≠ 0 := by omega
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hNe
  exact mul_ne_zero hN0 two_ne_zero

/-- The score of zero errors vanishes. -/
private theorem panel_score_zero (N : ℕ) (ω : Unit) :
    withinScore testX testU N ω = 0 := by
  have hterm : ∀ i, (centering (Fin 2) * testX i ω)ᵀ *ᵥ
      (centering (Fin 2) *ᵥ testU i ω) = 0 := by
    intro i
    show (centering (Fin 2) * testX0)ᵀ *ᵥ
      (centering (Fin 2) *ᵥ (0 : Fin 2 → ℝ)) = 0
    simp [Matrix.mulVec_zero]
  simp only [withinScore_eq_sum_centering, hterm, Finset.sum_const_zero]

/-- Noiseless exact recovery on the concrete two-period panel. -/
theorem withinEstimator_noiseless_concrete (N : ℕ) (ω : Unit)
    (hN : 1 ≤ N) : withinEstimator testX testY N ω = testB := by
  have hy : ∀ i ω, testY i ω
      = testX i ω *ᵥ testB + (fun _ => testC i ω) + testU i ω :=
    fun i ω => rfl
  have hG := panel_gram_unit (N := N) ω hN
  have hdecomp := withinEstimator_eq_add hy hG
  rw [hdecomp, panel_score_zero N ω, Matrix.mulVec_zero, add_zero]

/-- Consistency (`Tendsto`) on the concrete noiseless panel. -/
theorem tendsto_withinEstimator_noiseless (ω : Unit) :
    Tendsto (fun N => withinEstimator testX testY N ω) atTop
      (𝓝 testB) := by
  have heq : (fun _ : ℕ => testB)
      =ᶠ[atTop] fun N => withinEstimator testX testY N ω := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    exact (withinEstimator_noiseless_concrete N ω hN).symm
  exact Tendsto.congr' heq tendsto_const_nhds

/-- Demeaning kills the constant regressor in each row. -/
private theorem demeaned_timeInvariant_zero (t : Fin 2) :
    (centering (Fin 2) * testXc) t 0 = 0 := by
  have h := congrFun (centering_mulVec_const (τ := Fin 2) (5 : ℝ)) t
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h
  rw [Matrix.mul_apply]
  simp only [testXc, Matrix.of_apply]
  exact h

/-- The Gram matrix of time-invariant regressors vanishes. -/
private theorem gram_timeInvariant_vanishes (N : ℕ) (ω : Unit) :
    withinGram testXconst N ω = 0 := by
  have hterm : ∀ i, (centering (Fin 2) * testXconst i ω)ᵀ
      * (centering (Fin 2) * testXconst i ω) = 0 := by
    intro i
    have h0 : centering (Fin 2) * testXconst i ω = 0 := by
      ext t j
      fin_cases j
      exact demeaned_timeInvariant_zero t
    rw [h0]
    simp
  simp only [withinGram_eq_sum_centering, hterm, Finset.sum_const_zero]

/-- Time-invariant regressors: the Gram matrix is never invertible. -/
theorem withinGram_timeInvariant_not_unit (N : ℕ) (ω : Unit) :
    ¬IsUnit (withinGram testXconst N ω).det := by
  have hdet : (withinGram testXconst N ω).det = 0 := by
    simp [gram_timeInvariant_vanishes N ω]
  intro h
  exact (isUnit_iff_ne_zero.mp h) hdet

/-- Zero-mean alternating regressors survive demeaning. -/
theorem periodic_alternating_survives :
    centering (Fin 2) * testX0 = testX0 := by
  ext t j
  fin_cases t
  · fin_cases j
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    simp only [centering, testX0, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.one_apply, Matrix.of_apply]
    norm_num
  · fin_cases j
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    simp only [centering, testX0, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.one_apply, Matrix.of_apply]
    norm_num

/-- The LSDV bridge on the noiseless panel: with one intercept per cluster equal
to its effect, the dummy-variable residual of the stacked panel vanishes, so the
dummy-variable slope `testB` is the within estimator. -/
theorem lsdv_slope_noiseless (N : ℕ) (ω : Unit) (hN : 1 ≤ N) :
    testB = withinEstimator testX testY N ω := by
  have hres : stackVec testY N ω
      - groupDummy Prod.fst *ᵥ (fun i : Fin N => testC i ω)
      - stackMat testX N ω *ᵥ testB = 0 := by
    funext p
    rw [Pi.sub_apply, Pi.sub_apply, dummy_mulVec_apply]
    simp only [stackVec, stackMat, testY, testU, Matrix.mulVec, dotProduct,
      Matrix.of_apply, Pi.add_apply, Pi.zero_apply]
    ring
  exact lsdv_slope_eq_withinEstimator (α := fun i : Fin N => testC i ω)
    (by rw [hres, Matrix.mulVec_zero]) (by rw [hres, Matrix.mulVec_zero])
    (panel_gram_unit ω hN)

/-! ### Sequential exogeneity does not give the estimating equation -/

/-- Two-point probability space carrying the shock. -/
noncomputable def shockP : Measure Bool :=
  (2 : ℝ≥0∞)⁻¹ • (Measure.dirac true + Measure.dirac false)

/-- `shockP` is a probability measure. -/
instance : IsProbabilityMeasure shockP := by
  constructor
  simp only [shockP, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- The shock `ε = ±1`. -/
def shock : Bool → ℝ := fun b => if b then 1 else -1

/-- The shock has mean zero. -/
theorem integral_shock : ∫ ω, shock ω ∂shockP = 0 := by
  rw [shockP, integral_smul_measure,
    integral_add_measure Integrable.of_finite Integrable.of_finite,
    integral_dirac, integral_dirac]
  simp [shock]

/-- Regressors `X₁ = 0` and `X₂ = ε`. -/
noncomputable def fbX : Bool → Matrix (Fin 2) (Fin 1) ℝ :=
  fun ω => Matrix.of fun t _ => if t = 0 then 0 else shock ω

/-- Errors `u₁ = ε` and `u₂ = 0`: the period-one error feeds back into the
period-two regressor. -/
noncomputable def fbU : Bool → Fin 2 → ℝ :=
  fun ω t => if t = 0 then shock ω else 0

/-- The regressors of the periods up to `t`, with later periods set to `0`. -/
noncomputable def fbPast (t : Fin 2) : Bool → Fin 2 → ℝ :=
  fun ω s => if s ≤ t then fbX ω s 0 else 0

/-- Sequential exogeneity: each period's error has conditional mean zero given
the regressors of that period and the earlier ones. -/
theorem feedback_sequentialExogeneity (t : Fin 2) :
    shockP[fun ω => fbU ω t | MeasurableSpace.comap (fbPast t) inferInstance]
      =ᵐ[shockP] 0 := by
  fin_cases t
  · have hconst : fbPast 0 = fun _ => (0 : Fin 2 → ℝ) := by
      funext ω s
      fin_cases s <;> simp [fbPast, fbX]
    have hU : (fun ω => fbU ω 0) = shock := by
      funext ω
      simp [fbU]
    simp only [Fin.zero_eta, Fin.isValue]
    rw [hconst, MeasurableSpace.comap_const, condExp_bot, hU, integral_shock]
    rfl
  · have h0 : (fun ω => fbU ω 1) = 0 := by
      funext ω
      simp [fbU]
    simp only [Fin.mk_one, Fin.isValue]
    rw [h0, condExp_zero]

/-- At every outcome the within score is `-ε² / 2 = -1 / 2`. -/
theorem feedback_score_eq (ω : Bool) :
    ((centering (Fin 2) * fbX ω)ᵀ *ᵥ (centering (Fin 2) *ᵥ fbU ω)) 0
      = -(1 / 2) := by
  cases ω <;>
  · simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_two]
    simp only [centering, fbX, fbU, shock, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.one_apply, Matrix.of_apply]
    norm_num

/-- The expected within score is `-1 / 2`. -/
theorem feedback_integral_score :
    ∫ ω, ((centering (Fin 2) * fbX ω)ᵀ *ᵥ (centering (Fin 2) *ᵥ fbU ω)) 0 ∂shockP
      = -(1 / 2) := by
  simp_rw [feedback_score_eq]
  rw [integral_const, probReal_univ, one_smul]

/-- Sequential exogeneity holds while the expected within score is nonzero, so
sequential exogeneity does not give the estimating equation `hEE` of
`tendsto_withinEstimator`. -/
theorem sequentialExogeneity_not_estimatingEquation :
    (∀ t : Fin 2, shockP[fun ω => fbU ω t
      | MeasurableSpace.comap (fbPast t) inferInstance] =ᵐ[shockP] 0) ∧
    ∫ ω, ((centering (Fin 2) * fbX ω)ᵀ *ᵥ (centering (Fin 2) *ᵥ fbU ω)) 0 ∂shockP
      ≠ 0 :=
  ⟨feedback_sequentialExogeneity, by rw [feedback_integral_score]; norm_num⟩

/-- End-to-end: strict-exogeneity moments on the degenerate panel. -/
theorem integral_withinScore_concrete :
    ∀ j : Fin 1, ∫ ω : Unit, ((centering (Fin 2) * testX 0 ω)ᵀ *ᵥ
        (centering (Fin 2) *ᵥ testU 0 ω)) j ∂testP = 0 := by
  refine integral_withinScore_eq_zero_of_uncorrelated (X := testX)
    (u := testU) (P := testP) ?_ ?_
  · intro r s j
    have e : (fun ω : Unit => testX 0 ω r j * testU 0 ω s)
        = fun _ => testX0 r j * 0 := rfl
    rw [e]
    exact MeasureTheory.integrable_const _
  · intro r s j
    have e : (fun ω : Unit => testX 0 ω r j * testU 0 ω s)
        = fun _ => testX0 r j * 0 := rfl
    rw [e]
    simp only [mul_zero, MeasureTheory.integral_zero]

/-- End-to-end: conditional strict exogeneity on the degenerate panel. -/
theorem integral_mul_concrete (r s : Fin 2) (j : Fin 1) :
    ∫ ω : Unit, testX 0 ω r j * testU 0 ω s ∂testP = 0 := by
  refine integral_mul_eq_zero_of_condExp (X := testX) (u := testU)
    (P := testP) (r := r) (s := s) (j := j) ?_ ?_ ?_ ?_
  · have e : testX 0 = fun _ : Unit => testX0 := rfl
    rw [e]
    exact measurable_const
  · have e0 : (fun ω : Unit => testU 0 ω s) = 0 := rfl
    rw [e0]
    exact Filter.EventuallyEq.of_eq MeasureTheory.condExp_zero
  · have e0 : (fun ω : Unit => testU 0 ω s) = fun _ => (0 : ℝ) := rfl
    rw [e0]
    exact MeasureTheory.integrable_const _
  · have e : (fun ω : Unit => testX 0 ω r j * testU 0 ω s)
        = fun _ => testX0 r j * 0 := rfl
    rw [e]
    exact MeasureTheory.integrable_const _

/-- End-to-end consistency on the degenerate probability space. -/
theorem tendsto_withinEstimator_degenerate :
    ∀ᵐ ω ∂testP, Tendsto (fun N => withinEstimator testX testY N ω)
      atTop (𝓝 testB) := by
  refine tendsto_withinEstimator (X := testX) (y := testY) (c := testC)
    (u := testU) (β := testB) (P := testP) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun i ω => rfl
  · intro i
    have e : (fun ω : Unit => (testX i ω, testU i ω))
        = fun _ => (testX0, (0 : Fin 2 → ℝ)) := rfl
    rw [e]
    exact measurable_const
  · intro i j _
    have e : ∀ k, (fun ω : Unit => (testX k ω, testU k ω))
        = fun _ => (testX0, (0 : Fin 2 → ℝ)) := fun _ => rfl
    rw [e i, e j]
    exact ProbabilityTheory.indepFun_const_left _ _
  · intro i
    have e : ∀ k, (fun ω : Unit => (testX k ω, testU k ω))
        = fun _ => (testX0, (0 : Fin 2 → ℝ)) := fun _ => rfl
    rw [e i, e 0]
    exact ProbabilityTheory.IdentDistrib.refl
      measurable_const.aemeasurable
  · intro j l
    have e : (fun ω : Unit => ((centering (Fin 2) * testX 0 ω)ᵀ
        * (centering (Fin 2) * testX 0 ω)) j l)
        = fun _ => ((centering (Fin 2) * testX0)ᵀ
          * (centering (Fin 2) * testX0)) j l := rfl
    rw [e]
    exact MeasureTheory.integrable_const _
  · intro j
    have e : (fun ω : Unit => ((centering (Fin 2) * testX 0 ω)ᵀ *ᵥ
        (centering (Fin 2) *ᵥ testU 0 ω)) j) = 0 := by
      funext ω
      show ((centering (Fin 2) * testX0)ᵀ *ᵥ
        (centering (Fin 2) *ᵥ (0 : Fin 2 → ℝ))) j = 0
      simp [Matrix.mulVec_zero]
    rw [e]
    exact MeasureTheory.integrable_const _
  · have hint2 : ∀ j l : Fin 1, (∫ ω : Unit,
          ((centering (Fin 2) * testX 0 ω)ᵀ
            * (centering (Fin 2) * testX 0 ω)) j l ∂testP)
          = ((centering (Fin 2) * testX0)ᵀ
            * (centering (Fin 2) * testX0)) j l := by
      intro j l
      have e : (fun ω : Unit => ((centering (Fin 2) * testX 0 ω)ᵀ
          * (centering (Fin 2) * testX 0 ω)) j l)
          = fun _ => ((centering (Fin 2) * testX0)ᵀ
            * (centering (Fin 2) * testX0)) j l := rfl
      rw [e]
      simp [testP, MeasureTheory.integral_const]
    have hdet : (Matrix.of fun j l : Fin 1 => ∫ ω : Unit,
        ((centering (Fin 2) * testX 0 ω)ᵀ * (centering (Fin 2) * testX 0 ω)) j l
          ∂testP).det = 2 := by
      rw [Matrix.det_fin_one]
      simp only [Matrix.of_apply]
      rw [hint2 0 0]
      exact gram_entry_testX0
    rw [hdet]
    exact isUnit_iff_ne_zero.mpr (by norm_num)
  · intro j
    have h0 : (fun ω : Unit => ((centering (Fin 2) * testX 0 ω)ᵀ *ᵥ
        (centering (Fin 2) *ᵥ testU 0 ω)) j) = 0 := by
      funext ω
      show ((centering (Fin 2) * testX0)ᵀ *ᵥ
        (centering (Fin 2) *ᵥ (0 : Fin 2 → ℝ))) j = 0
      simp [Matrix.mulVec_zero]
    rw [h0]
    exact MeasureTheory.integral_zero _ _

end MathlibExtTest.Probability.Statistics.PanelWithin

end
