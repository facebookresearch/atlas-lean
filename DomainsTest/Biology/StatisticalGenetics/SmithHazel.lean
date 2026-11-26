/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.StatisticalGenetics.SmithHazel
import MathlibExt.Probability.Causality.MissingData.GaussianSelection
import MathlibExt.Probability.Distributions.GaussianCdf
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! Independent boundary checks for the Smith–Hazel model. -/

open MeasureTheory ProbabilityTheory Matrix SmithHazel
open MathlibExt.Probability.Causality.MissingData
open scoped Matrix RealInnerProductSpace

namespace SmithHazel.Test

private theorem solve_two {P : Matrix (Fin 2) (Fin 2) ℝ} {c b : Fin 2 → ℝ}
    (hP : P.det ≠ 0) (hb : P *ᵥ b = c) : P⁻¹ *ᵥ c = b := by
  rw [← hb, mulVec_mulVec, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hP), one_mulVec]

private abbrev G : Matrix (Fin 2) (Fin 2) ℝ := !![(2 : ℝ), 1; 1, 2]
private abbrev P : Matrix (Fin 2) (Fin 2) ℝ := !![(3 : ℝ), 1; 1, 3]
private abbrev D : Matrix (Fin 2) (Fin 2) ℝ := !![(3 : ℝ), 0; 0, 3]
private abbrev a : Fin 2 → ℝ := ![(1 : ℝ), 0]

private theorem nondiagonal_weights : P⁻¹ *ᵥ (G *ᵥ a) = ![(5 : ℝ) / 8, 1 / 8] := by
  apply solve_two
  · norm_num [P, Matrix.det_fin_two_of]
  · ext i
    fin_cases i <;> norm_num [P, G, a, mulVec, dotProduct, Fin.sum_univ_two]

private theorem nondiagonal_squared_ratio :
    ((G *ᵥ a) ⬝ᵥ (P⁻¹ *ᵥ (G *ᵥ a))) / (a ⬝ᵥ (G *ᵥ a)) = 11 / 16 := by
  rw [nondiagonal_weights]
  norm_num [P, G, a, mulVec, dotProduct, Fin.sum_univ_two]

private theorem phenotypic_diagonal_only :
    (D⁻¹ *ᵥ (G *ᵥ a)) 1 ≠ a 1 * (G 1 1 / D 1 1) := by
  have h : D⁻¹ *ᵥ (G *ᵥ a) = ![(2 : ℝ) / 3, 1 / 3] := by
    apply solve_two
    · norm_num [D, Matrix.det_fin_two_of]
    · ext i
      fin_cases i <;> norm_num [D, G, a, mulVec, dotProduct, Fin.sum_univ_two]
  rw [h]
  norm_num [a, G, D]

private theorem genetic_diagonal_only :
    (P⁻¹ *ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ a)) 1 ≠ a 1 * (1 / P 1 1) := by
  rw [one_mulVec]
  have h : P⁻¹ *ᵥ a = ![(3 : ℝ) / 8, -(1 / 8)] := by
    apply solve_two
    · norm_num [P, Matrix.det_fin_two_of]
    · ext i
      fin_cases i <;> norm_num [P, a, mulVec, dotProduct, Fin.sum_univ_two]
  rw [h]
  norm_num [a, P]

private abbrev Latents := EuclideanSpace ℝ (Fin 5)
private noncomputable abbrev γ : Measure Latents := stdGaussian Latents

private noncomputable def loading (u : Fin 5 → ℝ) : Latents →L[ℝ] ℝ :=
  innerSL ℝ (WithLp.toLp 2 u)

private theorem loading_cov (u v : Fin 5 → ℝ) :
    cov[loading u, loading v; γ] = u ⬝ᵥ v := by
  change cov[fun x => ⟪WithLp.toLp 2 u, x⟫, fun x => ⟪WithLp.toLp 2 v, x⟫; γ] = u ⬝ᵥ v
  rw [← covarianceBilin_apply_eq_cov
    (IsGaussian.hasGaussianLaw_id (μ := γ)).memLp_two,
    covarianceBilin_stdGaussian, innerSL_apply_apply, PiLp.inner_apply, dotProduct]
  simp only [RCLike.inner_apply, conj_trivial, mul_comm]

private theorem loading_memLp (u : Fin 5 → ℝ) : MemLp (loading u) 2 γ :=
  (IsGaussian.hasGaussianLaw_id.map_fun (loading u)).memLp_two

private abbrev additiveLoading : Fin 2 → Fin 5 → ℝ :=
  ![![(1 : ℝ), 1, 0, 0, 0], ![1, 0, 1, 0, 0]]

private abbrev residualLoading : Fin 2 → Fin 5 → ℝ :=
  ![![(0 : ℝ), 0, 0, 1, 0], ![0, 0, 0, 0, 1]]

private noncomputable def additiveScore : Latents →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi fun i => loading (additiveLoading i)

private noncomputable def residualScore : Latents →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi fun i => loading (residualLoading i)

private theorem phenotypeScore (i : Fin 2) :
    (fun x => additiveScore x i + residualScore x i) =
      loading (additiveLoading i + residualLoading i) := by
  funext x
  change ⟪WithLp.toLp 2 (additiveLoading i), x⟫ + ⟪WithLp.toLp 2 (residualLoading i), x⟫ =
    ⟪WithLp.toLp 2 (additiveLoading i + residualLoading i), x⟫
  exact (inner_add_left _ _ _).symm

private theorem twoTrait_phenotypeCov :
    (fun i j => cov[fun x => additiveScore x i + residualScore x i,
      fun x => additiveScore x j + residualScore x j; γ]) = P := by
  ext i j
  rw [phenotypeScore, phenotypeScore, loading_cov]
  fin_cases i <;> fin_cases j <;> norm_num [P, dotProduct, Fin.sum_univ_succ]

private theorem P_posDef : P.PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [P, Matrix.conjTranspose_apply]
  · intro x hx
    change 0 < x ⬝ᵥ (P *ᵥ x)
    simp [P, mulVec, dotProduct, Fin.sum_univ_two]
    have h : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra! h
      apply hx
      funext i
      fin_cases i
      · exact h.1
      · exact h.2
    rcases h with h | h <;>
      nlinarith [sq_pos_of_ne_zero h, sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 0 + x 1)]

/-- Two additive traits with a shared Gaussian factor and independent residual coordinates. -/
private noncomputable def twoTrait : Model 2 Latents γ where
  additive := additiveScore
  residual := residualScore
  economic := a
  measurable_additive := additiveScore.continuous.measurable
  measurable_residual := residualScore.continuous.measurable
  memLp_additive i := loading_memLp (additiveLoading i)
  memLp_residual i := loading_memLp (residualLoading i)
  orthogonal i j := by
    change cov[loading (additiveLoading i), loading (residualLoading j); γ] = 0
    rw [loading_cov]
    fin_cases i <;> fin_cases j <;> norm_num [dotProduct, Fin.sum_univ_succ]
  posDef := twoTrait_phenotypeCov ▸ P_posDef

private theorem twoTrait_joint :
    HasGaussianLaw (fun x => (twoTrait.additive x, twoTrait.residual x)) γ :=
  IsGaussian.hasGaussianLaw_id.map_fun (additiveScore.prod residualScore)

private theorem twoTrait_covariances : twoTrait.phenotypicCov = P ∧ twoTrait.geneticCov = G := by
  refine ⟨twoTrait_phenotypeCov, ?_⟩
  ext i j
  change cov[loading (additiveLoading i), loading (additiveLoading j); γ] = G i j
  rw [loading_cov]
  fin_cases i <;> fin_cases j <;> norm_num [G, dotProduct, Fin.sum_univ_succ]

private theorem twoTrait_aggregate : twoTrait.aggregate = loading (additiveLoading 0) := by
  funext x
  simp [Model.aggregate, twoTrait, a, dotProduct, Fin.sum_univ_two, additiveScore]

private theorem twoTrait_objectiveCov : twoTrait.objectiveCov = G *ᵥ a := by
  funext i
  unfold Model.objectiveCov
  rw [twoTrait_aggregate]
  change cov[fun x => additiveScore x i + residualScore x i, loading (additiveLoading 0); γ] =
    (G *ᵥ a) i
  rw [phenotypeScore, loading_cov]
  fin_cases i <;> norm_num [G, a, mulVec, dotProduct, Fin.sum_univ_succ]

private theorem twoTrait_regression : twoTrait.regressionWeights = ![(5 : ℝ) / 8, 1 / 8] := by
  rw [Model.regressionWeights, twoTrait_covariances.1, twoTrait_objectiveCov, nondiagonal_weights]

private theorem twoTrait_diagonal_rule :
    (fun i => twoTrait.economic i * twoTrait.heritability i) = ![(2 : ℝ) / 3, 0] ∧
      twoTrait.regressionWeights ≠ (fun i => twoTrait.economic i * twoTrait.heritability i) := by
  have h : (fun i => twoTrait.economic i * twoTrait.heritability i) = ![(2 : ℝ) / 3, 0] := by
    funext i
    rw [Model.heritability, twoTrait_covariances.1, twoTrait_covariances.2]
    change a i * (G i i / P i i) = _
    fin_cases i <;> norm_num [a, G, P]
  refine ⟨h, ?_⟩
  rw [twoTrait_regression, h]
  intro hEq
  have := congrFun hEq (1 : Fin 2)
  norm_num at this

private theorem twoTrait_index :
    twoTrait.index twoTrait.regressionWeights = loading ![(3 : ℝ) / 4, 5 / 8, 1 / 8, 5 / 8, 1 / 8] := by
  rw [twoTrait_regression]
  funext x
  simp only [Model.index, dotProduct, Fin.sum_univ_two]
  change (5 / 8 : ℝ) * (additiveScore x 0 + residualScore x 0) +
    (1 / 8 : ℝ) * (additiveScore x 1 + residualScore x 1) = _
  simp only [additiveScore, residualScore, ContinuousLinearMap.pi_apply, loading,
    innerSL_apply_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_succ]
  simp
  ring

private theorem twoTrait_squared_correlation :
    (pearsonRatio γ (twoTrait.index twoTrait.regressionWeights) twoTrait.aggregate) ^ 2 = 11 / 16 := by
  rw [twoTrait_index, twoTrait_aggregate, pearsonRatio, populationSD, populationSD,
    ← covariance_self (loading _).continuous.measurable.aemeasurable,
    ← covariance_self (loading _).continuous.measurable.aemeasurable]
  simp only [loading_cov, dotProduct, Fin.sum_univ_succ]
  norm_num
  simp only [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 11),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
  norm_num

private noncomputable abbrev ν : Measure ℝ := gaussianReal 0 1
private abbrev unitWeight : Fin 1 → ℝ := fun _ => 1

private theorem standard_hasLaw : HasLaw (fun x : ℝ => x) (gaussianReal 0 1) ν := by
  refine ⟨measurable_id.aemeasurable, ?_⟩
  exact Measure.map_id

private theorem standard_mean : (∫ x : ℝ, x ∂ν) = 0 :=
  integral_id_gaussianReal

private theorem standard_variance : Var[(fun x : ℝ => x); ν] = 1 := by
  exact variance_fun_id_gaussianReal

private theorem standard_cov : cov[(fun x : ℝ => x), (fun x : ℝ => x); ν] = 1 :=
  (covariance_self (X := fun x : ℝ => x) measurable_id.aemeasurable).trans standard_variance

private theorem standard_sd : populationSD ν (fun x : ℝ => x) = 1 := by
  rw [populationSD, standard_variance, Real.sqrt_one]

private noncomputable def oneTrait (weight : ℝ) : Model 1 ℝ ν where
  additive x _ := x
  residual _ _ := 0
  economic _ := weight
  measurable_additive := measurable_pi_iff.mpr fun _ => measurable_id
  measurable_residual := measurable_const
  memLp_additive _ := standard_hasLaw.hasGaussianLaw.memLp_two
  memLp_residual _ := MemLp.zero
  orthogonal _ _ := covariance_const_right _
  posDef := by
    have h : (fun i j : Fin 1 => cov[fun x : ℝ => x + 0, fun x : ℝ => x + 0; ν]) =
        (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
      ext i j
      have hij : i = j := Subsingleton.elim _ _
      subst j
      simp only [add_zero]
      exact standard_cov.trans (Matrix.one_apply_eq i).symm
    change Matrix.PosDef (fun i j : Fin 1 => cov[fun x : ℝ => x + 0, fun x : ℝ => x + 0; ν])
    rw [h]
    exact Matrix.PosDef.one

private theorem oneTrait_joint (weight : ℝ) :
    HasGaussianLaw (fun ω => ((oneTrait weight).additive ω, (oneTrait weight).residual ω)) ν := by
  let L : ℝ →ₗ[ℝ] (Fin 1 → ℝ) × (Fin 1 → ℝ) :=
    { toFun := fun x => (fun _ => x, fun _ => 0)
      map_add' := by aesop
      map_smul' := by aesop }
  exact standard_hasLaw.hasGaussianLaw.map_fun L.toContinuousLinearMap

private theorem oneTrait_index (b weight : ℝ) :
    (oneTrait weight).index (fun _ => b) = fun x : ℝ => b * x := by
  funext x
  simp [Model.index, Model.phenotype, oneTrait, dotProduct]

private theorem oneTrait_objective (weight : ℝ) :
    (oneTrait weight).aggregate = fun x : ℝ => weight * x := by
  funext x
  simp [Model.aggregate, oneTrait, dotProduct]

private theorem oneTrait_P (weight : ℝ) :
    (oneTrait weight).phenotypicCov = 1 := by
  ext i j
  have hij : i = j := Subsingleton.elim _ _
  subst j
  have h : (fun ω => (oneTrait weight).phenotype ω i) = fun x : ℝ => x := by
    funext x
    change x + 0 = x
    exact add_zero x
  change cov[(fun ω => (oneTrait weight).phenotype ω i),
    (fun ω => (oneTrait weight).phenotype ω i); ν] = (1 : Matrix (Fin 1) (Fin 1) ℝ) i i
  rw [h]
  exact standard_cov.trans (Matrix.one_apply_eq i).symm

private theorem oneTrait_regression :
    (oneTrait 1).regressionWeights = unitWeight := by
  unfold Model.regressionWeights
  rw [oneTrait_P, inv_one, one_mulVec]
  funext i
  have hX : (fun ω => (oneTrait 1).phenotype ω i) = fun x : ℝ => x := by
    funext x
    change x + 0 = x
    exact add_zero x
  change cov[(fun ω => (oneTrait 1).phenotype ω i), (oneTrait 1).aggregate; ν] = 1
  rw [hX, oneTrait_objective]
  simpa only [one_mul] using standard_cov

private theorem oneTrait_event (weight z : ℝ) :
    standardizedUpperEvent ν ((oneTrait weight).index unitWeight) z = Set.Ici z := by
  rw [oneTrait_index]
  simp only [one_mul]
  ext x
  change (∫ y, y ∂ν) + z * populationSD ν (fun y => y) ≤ x ↔ z ≤ x
  rw [standard_mean, standard_sd, mul_one, zero_add]

private theorem oneTrait_nonzero (b : ℝ) (hb : b ≠ 0) :
    (fun _ : Fin 1 => b) ≠ 0 := by
  intro h
  exact hb (congrFun h 0)

private theorem oneTrait_positive_variances :
    0 < Var[(oneTrait 1).index unitWeight; ν] ∧ 0 < Var[(oneTrait 1).aggregate; ν] := by
  rw [oneTrait_index, oneTrait_objective]
  simp only [one_mul, standard_variance, zero_lt_one, and_self]

private theorem oneTrait_proportion (z : ℝ) :
    ν.real (standardizedUpperEvent ν ((oneTrait 1).index unitWeight) z) =
      cdf (gaussianReal 0 1) (-z) := by
  rw [oneTrait_event]
  have h := measureReal_selection_eq_cdf (c := -z) standard_hasLaw
  simpa only [neg_neg, Set.Ici] using h

private theorem oneTrait_gain (z : ℝ) :
    (oneTrait 1).gain unitWeight z = inverseMillsRatio (-z) := by
  rw [Model.gain, oneTrait_event, oneTrait_objective]
  have h := integral_cond_selectionError_eq (c := -z) standard_hasLaw measurable_id
  rw [conditionalMeanShift]
  simpa only [one_mul, standard_mean, sub_zero, neg_neg, Set.Ici] using h

private theorem oneTrait_gain_pos (z : ℝ) : 0 < (oneTrait 1).gain unitWeight z := by
  rw [oneTrait_gain]
  exact inverseMillsRatio_pos _

private theorem oneTrait_rescale (z : ℝ) :
    standardizedUpperEvent ν ((oneTrait 1).index ((2 : ℝ) • unitWeight)) z =
      standardizedUpperEvent ν ((oneTrait 1).index unitWeight) z :=
  (oneTrait 1).upperEvent_smul unitWeight z (k := 2) (by norm_num)

private theorem oneTrait_negative (z : ℝ) :
    standardizedUpperEvent ν ((oneTrait 1).index (-unitWeight)) z = Set.Iic (-z) := by
  rw [(oneTrait 1).upperEvent_neg, oneTrait_index]
  simp only [one_mul]
  ext x
  change x ≤ (∫ y, y ∂ν) - z * populationSD ν (fun y => y) ↔ x ≤ -z
  rw [standard_mean, standard_sd, mul_one, zero_sub]

private theorem oneTrait_negative_gain (z : ℝ) :
    (oneTrait 1).gain (-unitWeight) z = -inverseMillsRatio (-z) := by
  have hneg : HasLaw (fun x : ℝ => -x) (gaussianReal 0 1) ν := by
    convert gaussianReal_neg standard_hasLaw using 1
    rw [neg_zero]
  rw [Model.gain, oneTrait_objective, oneTrait_negative]
  have hi := integral_cond_selectionError_eq (c := -z) hneg measurable_id.neg
  have hset : {ω : ℝ | -(-z) ≤ -ω} = Set.Iic (-z) := by
    ext ω
    change -(-z) ≤ -ω ↔ ω ≤ -z
    exact neg_le_neg_iff
  rw [hset, integral_neg] at hi
  have hg : (∫ x, x ∂ν[|Set.Iic (-z)]) = -inverseMillsRatio (-z) := by linarith
  simpa [conditionalMeanShift, standard_mean] using hg

private theorem oneTrait_zero_objective (z : ℝ) :
    Var[(oneTrait 0).aggregate; ν] = 0 ∧ (oneTrait 0).gain unitWeight z = 0 := by
  rw [Model.gain, oneTrait_objective, conditionalMeanShift]
  simp [← Pi.zero_def, variance_zero]

private theorem oneTrait_zero_index :
    Var[(oneTrait 1).index (0 : Fin 1 → ℝ); ν] = 0 := by
  change Var[(oneTrait 1).index (fun _ => 0); ν] = 0
  rw [oneTrait_index]
  simp [← Pi.zero_def]

private theorem oneTrait_half_selected :
    ν.real (standardizedUpperEvent ν ((oneTrait 1).index unitWeight) 0) = 1 / 2 := by
  rw [oneTrait_proportion, neg_zero, cdf_gaussianReal_zero]

private theorem oneTrait_raw_threshold_not_scale_invariant :
    {ω | (1 : ℝ) ≤ (oneTrait 1).index unitWeight ω} ≠
      {ω | (1 : ℝ) ≤ (oneTrait 1).index (fun _ => 2) ω} := by
  intro h
  have hm := Set.ext_iff.mp h (3 / 4)
  rw [oneTrait_index, oneTrait_index] at hm
  norm_num at hm

#print axioms nondiagonal_weights
#print axioms nondiagonal_squared_ratio
#print axioms phenotypic_diagonal_only
#print axioms genetic_diagonal_only
#print axioms twoTrait_joint
#print axioms twoTrait_covariances
#print axioms twoTrait_regression
#print axioms twoTrait_diagonal_rule
#print axioms twoTrait_squared_correlation
#print axioms oneTrait_joint
#print axioms oneTrait_regression
#print axioms oneTrait_nonzero
#print axioms oneTrait_positive_variances
#print axioms oneTrait_proportion
#print axioms oneTrait_gain_pos
#print axioms oneTrait_rescale
#print axioms oneTrait_negative_gain
#print axioms oneTrait_zero_objective
#print axioms oneTrait_zero_index
#print axioms oneTrait_half_selected
#print axioms oneTrait_raw_threshold_not_scale_invariant
#print axioms ProbabilityTheory.conditionalMeanShift_eq_indicator_quotient
#print axioms MathlibExt.Probability.Causality.MissingData.integral_cond_selectionError_eq

end SmithHazel.Test
