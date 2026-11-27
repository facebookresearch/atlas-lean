/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.StatisticalGenetics.SmithHazelIndex
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Tactic
import Mathlib.Algebra.Order.Star.Real

/-! # Smith–Hazel genetic gain tests on a concrete Gaussian model

Builds an explicit jointly Gaussian model on `Fin 5 → ℝ` and checks the genetic-gain formulas,
the zero-covariance cases and the generic Gaussian response results on it.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix
open MathlibExt.Probability.Causality.MissingData (inverseMillsRatio inverseMillsRatio_pos)
open scoped BigOperators Matrix

namespace SmithHazel.ResponseTests

abbrev Space := Fin 5 → ℝ
noncomputable def law : Measure Space := Measure.pi (fun _ => gaussianReal 0 1)
instance probability_law : IsProbabilityMeasure law :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi _))

lemma coordinate_law (i : Fin 5) : HasLaw (fun ω : Space => ω i) (gaussianReal 0 1) law :=
  (measurePreserving_eval (fun _ : Fin 5 => gaussianReal 0 1) i).hasLaw

lemma factors_gaussian : HasGaussianLaw (id : Space → Space) law := by
  exact (iIndepFun_pi (fun _ : Fin 5 => aemeasurable_id)).hasGaussianLaw
    (fun i => (coordinate_law i).hasGaussianLaw)

lemma coordinate_memLp (i : Fin 5) : MemLp (fun ω : Space => ω i) 2 law :=
  (coordinate_law i).hasGaussianLaw.memLp_two

lemma coordinate_covariance (i j : Fin 5) :
    cov[fun ω : Space => ω i, fun ω => ω j; law] = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    rw [covariance_self (coordinate_law i).aemeasurable, (coordinate_law i).variance_eq]
    simp
  · rw [ite_eq_right h]
    exact (iIndepFun_pi (fun _ : Fin 5 => aemeasurable_id)).indepFun h |>.covariance_eq_zero
      (coordinate_memLp i) (coordinate_memLp j)

lemma linear_covariance (b d : Fin 5 → ℝ) :
    cov[fun ω : Space => b ⬝ᵥ ω, fun ω => d ⬝ᵥ ω; law] = b ⬝ᵥ d := by
  simp only [dotProduct]
  rw [covariance_fun_sum_fun_sum (fun i => (coordinate_memLp i).const_mul (b i))
    (fun j => (coordinate_memLp j).const_mul (d j))]
  simp [covariance_const_mul_left, covariance_const_mul_right, coordinate_covariance,
    mul_comm]

lemma linear_gaussian (b : Fin 5 → ℝ) :
    HasGaussianLaw (fun ω : Space => b ⬝ᵥ ω) law := by
  let c : Space →L[ℝ] ℝ := ∑ i, b i • ContinuousLinearMap.proj i
  simpa [c, dotProduct, _root_.sum_apply] using factors_gaussian.map_fun c

noncomputable def additiveCoefficients : Fin 2 → Fin 5 → ℝ :=
  ![![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0]]
noncomputable def residualCoefficients : Fin 2 → Fin 5 → ℝ :=
  ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]
noncomputable def additive (ω : Space) (i : Fin 2) : ℝ := additiveCoefficients i ⬝ᵥ ω
noncomputable def residual (ω : Space) (i : Fin 2) : ℝ := residualCoefficients i ⬝ᵥ ω

lemma raw_covariances :
    (fun i j => cov[fun ω => additive ω i, fun ω => additive ω j; law]) = !![2, 1; 1, 2] ∧
    (fun i j => cov[fun ω => residual ω i, fun ω => residual ω j; law]) =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    (∀ i j, cov[fun ω => additive ω i, fun ω => residual ω j; law] = 0) := by
  simp only [additive, residual, linear_covariance]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [additiveCoefficients, dotProduct, Fin.sum_univ_succ]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [residualCoefficients, dotProduct, Fin.sum_univ_succ]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [additiveCoefficients, residualCoefficients, dotProduct, Fin.sum_univ_succ]

lemma raw_phenotypic_covariance :
    (fun i j => cov[fun ω => additive ω i + residual ω i,
      fun ω => additive ω j + residual ω j; law]) = !![3, 1; 1, 3] := by
  have heq (i : Fin 2) : (fun ω => additive ω i + residual ω i) =
      fun ω => (additiveCoefficients i + residualCoefficients i) ⬝ᵥ ω := by
    funext ω
    exact (add_dotProduct _ _ _).symm
  simp only [heq, linear_covariance]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [additiveCoefficients, residualCoefficients, dotProduct, Fin.sum_univ_succ]

lemma phenotypic_posDef : ( !![3, 1; 1, 3] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.IsHermitian]
  · intro x hx
    have h : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra hn
      apply hx
      ext i
      fin_cases i <;> simp_all
    simp only [star_trivial, dotProduct, mulVec, Fin.sum_univ_two]
    norm_num
    rcases h with h | h
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (x 1), sq_nonneg (x 0 + x 1)]
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (x 0), sq_nonneg (x 0 + x 1)]

noncomputable def model : Model 2 Space law where
  additive := additive
  residual := residual
  economic := ![1, 0]
  measurable_additive := by
    apply Measurable.of_eval
    intro i
    change Measurable (fun ω : Space => ∑ j, additiveCoefficients i j * ω j)
    exact Finset.measurable_sum _ fun j _ => measurable_const.mul (measurable_pi_apply j)
  measurable_residual := by
    apply Measurable.of_eval
    intro i
    change Measurable (fun ω : Space => ∑ j, residualCoefficients i j * ω j)
    exact Finset.measurable_sum _ fun j _ => measurable_const.mul (measurable_pi_apply j)
  memLp_additive := fun i => (linear_gaussian (additiveCoefficients i)).memLp_two
  memLp_residual := fun i => (linear_gaussian (residualCoefficients i)).memLp_two
  orthogonal := raw_covariances.2.2
  posDef := raw_phenotypic_covariance ▸ phenotypic_posDef

lemma model_gaussian : HasGaussianLaw (fun ω => (model.additive ω, model.residual ω)) law := by
  let a : Space →L[ℝ] (Fin 2 → ℝ) := ContinuousLinearMap.pi fun i =>
    ∑ j, additiveCoefficients i j • ContinuousLinearMap.proj j
  let e : Space →L[ℝ] (Fin 2 → ℝ) := ContinuousLinearMap.pi fun i =>
    ∑ j, residualCoefficients i j • ContinuousLinearMap.proj j
  convert factors_gaussian.map_fun (a.prod e) using 1
  ext ω i <;> simp [a, e, model, additive, residual, dotProduct, _root_.sum_apply]

lemma model_covariances : model.geneticCov = !![2, 1; 1, 2] ∧
    model.residualCov = 1 ∧ model.phenotypicCov = !![3, 1; 1, 3] := by
  exact ⟨raw_covariances.1, raw_covariances.2.1, raw_phenotypic_covariance⟩

lemma objective_covariance : model.objectiveCov = ![2, 1] := by
  rw [objectiveCov_eq_geneticCov_mulVec, model_covariances.1]
  ext i
  fin_cases i <;> norm_num [model, mulVec, dotProduct, Fin.sum_univ_two]

lemma canonical_weights : model.regressionWeights = ![(5 / 8 : ℝ), 1 / 8] := by
  symm
  apply (normalEquations_iff model _).mp
  rw [model_covariances.2.2, objective_covariance]
  ext i
  fin_cases i <;> norm_num [mulVec, dotProduct, Fin.sum_univ_two]

lemma objective_variance : Var[model.aggregate; law] = 2 := by
  rw [variance_aggregate, model_covariances.1]
  norm_num [model, dotProduct, mulVec, Fin.sum_univ_two]

lemma objective_nonzero : model.objectiveCov ≠ 0 := by
  rw [objective_covariance]
  intro h
  have := congrFun h 0
  norm_num at this

lemma canonical_nonzero : model.regressionWeights ≠ 0 := by
  rw [canonical_weights]
  intro h
  have := congrFun h 0
  norm_num at this

lemma baseline_nonzero : (![1, 0] : Fin 2 → ℝ) ≠ 0 := by
  intro h
  have := congrFun h 0
  norm_num at this

lemma canonical_correlation_squared : pearsonRatio law (model.index model.regressionWeights)
    model.aggregate ^ 2 = 11 / 16 := by
  have hc : cov[model.index model.regressionWeights, model.aggregate; law] = 11 / 8 := by
    rw [covariance_index_aggregate, objective_covariance, canonical_weights]
    norm_num [dotProduct, Fin.sum_univ_two]
  have hv : Var[model.index model.regressionWeights; law] = 11 / 8 := by
    rw [variance_index, canonical_weights, model_covariances.2.2]
    norm_num [dotProduct, mulVec, Fin.sum_univ_two]
  rw [pearsonRatio, populationSD, populationSD, hc, hv, objective_variance, div_pow, mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 11 / 8), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

lemma canonical_gain (z : ℝ) :
    model.gain model.regressionWeights z = inverseMillsRatio (-z) * √22 / 4 := by
  have hc : cov[model.index model.regressionWeights, model.aggregate; law] = 11 / 8 := by
    rw [covariance_index_aggregate, objective_covariance, canonical_weights]
    norm_num [dotProduct, Fin.sum_univ_two]
  have hv : Var[model.index model.regressionWeights; law] = 11 / 8 := by
    rw [variance_index, canonical_weights, model_covariances.2.2]
    norm_num [dotProduct, mulVec, Fin.sum_univ_two]
  rw [gain_eq_covariance model model_gaussian canonical_nonzero, hc, populationSD, hv]
  have h : √((11 : ℝ) / 8) = √22 / 4 := by
    have hleft := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 11 / 8)
    have hright := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 22)
    have hn := Real.sqrt_nonneg ((11 : ℝ) / 8)
    have hn' := Real.sqrt_nonneg (22 : ℝ)
    nlinarith
  rw [h]
  have hne : √(22 : ℝ) ≠ 0 := by positivity
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 22)]
  ring

lemma baseline_gain (z : ℝ) : model.gain ![1, 0] z = inverseMillsRatio (-z) * 2 / √3 := by
  rw [gain_eq_pearsonRatio model model_gaussian baseline_nonzero
    (by rw [objective_variance]; norm_num), pearsonRatio]
  rw [populationSD, populationSD, covariance_index_aggregate, variance_index,
    objective_variance, objective_covariance, model_covariances.2.2]
  norm_num [dotProduct, mulVec, Fin.sum_univ_two]
  field_simp

lemma positive_gain_comparison (z : ℝ) :
    0 < model.gain ![1, 0] z ∧ model.gain ![1, 0] z < model.gain model.regressionWeights z := by
  rw [baseline_gain, canonical_gain]
  have hi := inverseMillsRatio_pos (-z)
  have h3 : 0 < √(3 : ℝ) := by positivity
  have h22 : 0 < √(22 : ℝ) := by positivity
  have hratio : 2 / √(3 : ℝ) < √22 / 4 := by
    apply (div_lt_iff₀ h3).mpr
    have hs3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have hs22 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 22)
    nlinarith [mul_pos h3 h22, sq_nonneg (√3 * √22 - 8)]
  constructor
  · positivity
  · simpa only [mul_div_assoc] using mul_lt_mul_of_pos_left hratio hi

lemma positive_multiple_maximizes :
    ∀ d : Fin 2 → ℝ, d ≠ 0 → model.gain d 0 ≤ model.gain ((2 : ℝ) • model.regressionWeights) 0 := by
  apply (gain_max_iff model model_gaussian (smul_ne_zero (by norm_num) canonical_nonzero)
    (by rw [objective_variance]; norm_num) objective_nonzero 0).mpr
  exact ⟨2, by norm_num, rfl⟩

lemma baseline_does_not_maximize :
    ¬ (∀ d : Fin 2 → ℝ, d ≠ 0 → model.gain d 0 ≤ model.gain ![1, 0] 0) := by
  rw [gain_max_iff model model_gaussian baseline_nonzero
    (by rw [objective_variance]; norm_num) objective_nonzero]
  rintro ⟨k, hk, heq⟩
  rw [canonical_weights] at heq
  have h₀ := congrFun heq 0
  have h₁ := congrFun heq 1
  norm_num [Pi.smul_apply, smul_eq_mul] at h₀ h₁
  linarith

lemma negative_gain (z : ℝ) :
    model.gain (-model.regressionWeights) z = -inverseMillsRatio (-z) * √22 / 4 := by
  rw [gain_eq_pearsonRatio model model_gaussian (neg_ne_zero.mpr canonical_nonzero)
    (by rw [objective_variance]; norm_num)]
  have hp : pearsonRatio law (model.index (-model.regressionWeights)) model.aggregate =
      -pearsonRatio law (model.index model.regressionWeights) model.aggregate := by
    unfold pearsonRatio populationSD
    have heq : model.index (-model.regressionWeights) =
        fun ω => -model.index model.regressionWeights ω := by
      funext ω
      exact neg_dotProduct _ _
    rw [heq, covariance_fun_neg_left, variance_fun_neg]
    ring
  rw [hp]
  have hg := gain_eq_pearsonRatio model model_gaussian canonical_nonzero
    (by rw [objective_variance]; norm_num) z
  rw [canonical_gain] at hg
  nlinarith [hg]

lemma negative_minimizes :
    ∀ d : Fin 2 → ℝ, d ≠ 0 → model.gain (-model.regressionWeights) 0 ≤ model.gain d 0 := by
  apply (gain_min_iff model model_gaussian (neg_ne_zero.mpr canonical_nonzero)
    (by rw [objective_variance]; norm_num) objective_nonzero 0).mpr
  exact ⟨-1, by norm_num, by simp⟩

noncomputable def zero_model : Model 2 Space law := { model with economic := 0 }

lemma zero_objective_gain (z : ℝ) : zero_model.gain ![1, 0] z = 0 := by
  apply gain_eq_zero_of_variance_aggregate_eq_zero zero_model model_gaussian baseline_nonzero
  have h : zero_model.aggregate = 0 := by
    funext ω
    simp [Model.aggregate, zero_model]
  rw [h]
  simp

lemma scalar_response (z : ℝ) : conditionalMeanShift law (fun ω : Space => ω 0 + ω 1)
    (standardizedUpperEvent law (fun ω => ω 0) z) = inverseMillsRatio (-z) := by
  have hg : HasGaussianLaw (fun ω : Space => (ω 0 + ω 1, ω 0)) law := by
    exact factors_gaussian.map_fun
      (((ContinuousLinearMap.proj 0 : Space →L[ℝ] ℝ) + ContinuousLinearMap.proj 1).prod
        (ContinuousLinearMap.proj 0))
  rw [conditionalMeanShift_standardizedUpperEvent_gaussian (measurable_pi_apply 0) hg
    (by rw [(coordinate_law 0).variance_eq]; norm_num)]
  have hc : cov[fun ω : Space => ω 0, fun ω => ω 0 + ω 1; law] = 1 := by
    rw [show (fun ω : Space => ω 0 + ω 1) =
        (fun ω => ω 0) + (fun ω => ω 1) from rfl,
      covariance_add_right (coordinate_memLp 0) (coordinate_memLp 0) (coordinate_memLp 1)]
    norm_num [coordinate_covariance]
  rw [hc, populationSD, (coordinate_law 0).variance_eq]
  norm_num

lemma scalar_zero_covariance (z : ℝ) : conditionalMeanShift law (fun ω : Space => ω 1)
    (standardizedUpperEvent law (fun ω => ω 0) z) = 0 := by
  apply conditionalMeanShift_eq_zero_of_covariance_eq_zero (measurable_pi_apply 0)
    (factors_gaussian.prodMk 1 0)
  · change 0 < Var[fun ω : Space => ω 0; law]
    rw [(coordinate_law 0).variance_eq]
    norm_num
  · norm_num [coordinate_covariance]

lemma independent_objective (z : ℝ) : conditionalMeanShift law (fun ω : Space => ω 2)
    (standardizedUpperEvent law (fun ω => (![1, 0] : Fin 2 → ℝ) ⬝ᵥ ![ω 0, ω 1]) z) = 0 := by
  have hg : HasGaussianLaw (fun ω : Space => (![ω 0, ω 1], ω 2)) law := by
    let x : Space →L[ℝ] (Fin 2 → ℝ) := ContinuousLinearMap.pi fun i =>
      ContinuousLinearMap.proj (if i = 0 then 0 else 1)
    convert factors_gaussian.map_fun (x.prod (ContinuousLinearMap.proj 2)) using 1
    ext ω i
    · fin_cases i <;> simp [x]
    · rfl
  apply conditionalMeanShift_linear_eq_zero_of_crossCovariance_eq_zero
    (by measurability) hg
  · have heq : (fun i j : Fin 2 => cov[fun ω : Space => ![ω 0, ω 1] i,
        fun ω => ![ω 0, ω 1] j; law]) = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [coordinate_covariance]
    rw [heq]
    exact Matrix.PosDef.one
  · intro i
    fin_cases i <;> norm_num [coordinate_covariance]
  · exact baseline_nonzero

#print axioms Space
#print axioms law
#print axioms probability_law
#print axioms coordinate_law
#print axioms factors_gaussian
#print axioms coordinate_memLp
#print axioms coordinate_covariance
#print axioms linear_covariance
#print axioms linear_gaussian
#print axioms additiveCoefficients
#print axioms residualCoefficients
#print axioms additive
#print axioms residual
#print axioms raw_covariances
#print axioms raw_phenotypic_covariance
#print axioms phenotypic_posDef
#print axioms model
#print axioms model_gaussian
#print axioms model_covariances
#print axioms objective_covariance
#print axioms canonical_weights
#print axioms objective_variance
#print axioms objective_nonzero
#print axioms canonical_nonzero
#print axioms baseline_nonzero
#print axioms canonical_correlation_squared
#print axioms canonical_gain
#print axioms baseline_gain
#print axioms positive_gain_comparison
#print axioms positive_multiple_maximizes
#print axioms baseline_does_not_maximize
#print axioms negative_gain
#print axioms negative_minimizes
#print axioms zero_model
#print axioms zero_objective_gain
#print axioms scalar_response
#print axioms scalar_zero_covariance
#print axioms independent_objective

end SmithHazel.ResponseTests
