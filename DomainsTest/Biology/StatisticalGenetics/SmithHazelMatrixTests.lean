/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.StatisticalGenetics.SmithHazel
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

public import Domains.Biology.StatisticalGenetics.SmithHazelIndex

/-! # Smith–Hazel index tests on explicit covariance matrices

Applies the index covariance, correlation-bound, normal-equation and diagonal-case theorems of
`Domains.Biology.StatisticalGenetics.SmithHazelIndex` to explicit two- and three-trait models,
including degenerate and zero-covariance cases.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix SmithHazel
open scoped BigOperators Matrix RealInnerProductSpace

namespace SmithHazel.MatrixTests

private abbrev G : Matrix (Fin 2) (Fin 2) ℝ := !![(2 : ℝ), 1; 1, 2]
private abbrev P : Matrix (Fin 2) (Fin 2) ℝ := !![(3 : ℝ), 1; 1, 3]
private abbrev a : Fin 2 → ℝ := ![(1 : ℝ), 0]
private abbrev e : Fin 2 → ℝ := ![(0 : ℝ), 1]
private noncomputable abbrev w : Fin 2 → ℝ := ![(5 : ℝ) / 8, 1 / 8]

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


private theorem fixture_covariances :
    twoTrait.phenotypicCov = P ∧ twoTrait.geneticCov = G ∧ twoTrait.residualCov = 1 := by
  refine ⟨twoTrait_phenotypeCov, ?_, ?_⟩
  · ext i j
    change cov[loading (additiveLoading i), loading (additiveLoading j); γ] = G i j
    rw [loading_cov]
    fin_cases i <;> fin_cases j <;> norm_num [G, dotProduct, Fin.sum_univ_succ]
  · ext i j
    change cov[loading (residualLoading i), loading (residualLoading j); γ] =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) i j
    rw [loading_cov]
    fin_cases i <;> fin_cases j <;> norm_num [dotProduct, Fin.sum_univ_succ]

private theorem a_ne : a ≠ 0 := by
  intro h
  have := congrFun h 0
  norm_num [a] at this

private theorem index_covariance : cov[twoTrait.index a, twoTrait.index e; γ] = 1 := by
  rw [covariance_index_index, fixture_covariances.1]
  norm_num [P, a, e, mulVec, dotProduct, Fin.sum_univ_two]

private theorem index_variance : Var[twoTrait.index a; γ] = 3 := by
  rw [variance_index, fixture_covariances.1]
  norm_num [P, a, mulVec, dotProduct, Fin.sum_univ_two]

private theorem aggregate_variance : Var[twoTrait.aggregate; γ] = 2 := by
  rw [variance_aggregate, fixture_covariances.2.1]
  change a ⬝ᵥ (G *ᵥ a) = 2
  norm_num [G, a, mulVec, dotProduct, Fin.sum_univ_two]

private theorem aggregate_positive : 0 < Var[twoTrait.aggregate; γ] := by
  rw [aggregate_variance]
  norm_num

private theorem covariance_decomposition :
    twoTrait.phenotypicCov = twoTrait.geneticCov + twoTrait.residualCov ∧
    twoTrait.phenotypicCov 0 1 = twoTrait.geneticCov 0 1 + twoTrait.residualCov 0 1 ∧
    twoTrait.phenotypicCov 0 1 = 1 := by
  have h := phenotypicCov_eq_add twoTrait
  refine ⟨h, congrFun (congrFun h 0) 1, ?_⟩
  rw [fixture_covariances.1]
  norm_num [P]

private theorem objective_covariance : twoTrait.objectiveCov = ![(2 : ℝ), 1] := by
  rw [objectiveCov_eq_geneticCov_mulVec, fixture_covariances.2.1]
  change G *ᵥ a = _
  ext i
  fin_cases i <;> norm_num [G, a, mulVec, dotProduct, Fin.sum_univ_two]

private theorem aggregate_covariance : cov[twoTrait.index e, twoTrait.aggregate; γ] = 1 := by
  rw [covariance_index_aggregate, objective_covariance]
  norm_num [e, dotProduct, Fin.sum_univ_two]

private theorem solve_two {Q : Matrix (Fin 2) (Fin 2) ℝ} {c b : Fin 2 → ℝ}
    (hQ : Q.det ≠ 0) (hb : Q *ᵥ b = c) : Q⁻¹ *ᵥ c = b := by
  rw [← hb, mulVec_mulVec, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hQ), one_mulVec]

private theorem regression_weights : twoTrait.regressionWeights = w := by
  rw [regressionWeights_eq_geneticCov, fixture_covariances.1, fixture_covariances.2.1]
  change P⁻¹ *ᵥ (G *ᵥ a) = w
  apply solve_two
  · norm_num [P, Matrix.det_fin_two_of]
  · ext i
    fin_cases i <;> norm_num [P, G, a, w, mulVec, dotProduct, Fin.sum_univ_two]

private theorem objective_nonzero : twoTrait.objectiveCov ≠ 0 := by
  rw [objective_covariance]
  intro h
  have := congrFun h 0
  norm_num at this

private theorem signed_quotient :
    0 < Var[twoTrait.index a; γ] ∧
    pearsonRatio γ (twoTrait.index a) twoTrait.aggregate = 2 / (√3 * √2) := by
  refine ⟨by rw [index_variance]; norm_num, ?_⟩
  rw [pearsonRatio_index_eq twoTrait a_ne aggregate_positive,
    fixture_covariances.1, fixture_covariances.2.1, objective_covariance]
  change _ / (_ * √(a ⬝ᵥ (G *ᵥ a))) = _
  norm_num [P, G, a, mulVec, dotProduct, Fin.sum_univ_two]

private theorem positive_index : 0 < Var[twoTrait.index a; γ] :=
  (variance_index_pos_iff twoTrait a).mpr a_ne

private theorem zero_index : Var[twoTrait.index (0 : Fin 2 → ℝ); γ] = 0 :=
  (variance_index_eq_zero_iff twoTrait 0).mpr rfl

private theorem economic_pairing : twoTrait.economic ⬝ᵥ twoTrait.objectiveCov = 2 := by
  rw [economic_dot_objectiveCov, aggregate_variance]

private noncomputable def zeroObjective : Model 2 Latents γ := { twoTrait with economic := 0 }

private theorem zero_objective :
    Var[zeroObjective.aggregate; γ] = 0 ∧ zeroObjective.objectiveCov = 0 := by
  have hc : zeroObjective.objectiveCov = 0 := by
    rw [objectiveCov_eq_geneticCov_mulVec]
    change twoTrait.geneticCov *ᵥ 0 = 0
    exact mulVec_zero _
  exact ⟨(variance_aggregate_eq_zero_iff zeroObjective).mpr hc, hc⟩

private theorem phenotype_variance (i : Fin 2) :
    Var[fun x => twoTrait.phenotype x i; γ] = 3 := by
  have hm : MemLp (fun x => twoTrait.phenotype x i) 2 γ :=
    (twoTrait.memLp_additive i).add (twoTrait.memLp_residual i)
  rw [← covariance_self hm.aemeasurable]
  change twoTrait.phenotypicCov i i = 3
  rw [fixture_covariances.1]
  fin_cases i <;> norm_num [P]

private theorem phenotype_correlation (i j : Fin 2) :
    pearsonRatio γ (fun x => twoTrait.phenotype x i) (fun x => twoTrait.phenotype x j) =
      P i j / 3 := by
  rw [pearsonRatio, populationSD, populationSD, phenotype_variance, phenotype_variance]
  change twoTrait.phenotypicCov i j / (√3 * √3) = _
  rw [fixture_covariances.1, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

private theorem phenotype_objective_correlation (i : Fin 2) :
    pearsonRatio γ (fun x => twoTrait.phenotype x i) twoTrait.aggregate =
      (![(2 : ℝ), 1] i) / (√3 * √2) := by
  rw [pearsonRatio, populationSD, populationSD, phenotype_variance, aggregate_variance]
  change twoTrait.objectiveCov i / (√3 * √2) = _
  rw [objective_covariance]

private theorem beta_value (i : Fin 2) : twoTrait.beta i = w i * √3 / √2 := by
  rw [Model.beta, regression_weights, populationSD, populationSD,
    phenotype_variance, aggregate_variance]

private theorem normal_equations :
    twoTrait.phenotypicCov *ᵥ w = ![(2 : ℝ), 1] ∧ w = twoTrait.regressionWeights := by
  have h : twoTrait.phenotypicCov *ᵥ w = twoTrait.objectiveCov := by
    rw [fixture_covariances.1, objective_covariance]
    ext i
    fin_cases i <;> norm_num [P, w, mulVec, dotProduct, Fin.sum_univ_two]
  exact ⟨h.trans objective_covariance, (normalEquations_iff twoTrait w).mp h⟩

private theorem standardized_equation :
    twoTrait.beta 0 + (1 / 3 : ℝ) * twoTrait.beta 1 = 2 / (√3 * √2) ∧
    (1 / 3 : ℝ) * twoTrait.beta 1 ≠ 0 := by
  have h := standardized_normalEquations twoTrait aggregate_positive 0
  rw [Fin.sum_univ_two, phenotype_correlation, phenotype_correlation,
    phenotype_objective_correlation] at h
  norm_num [P] at h
  refine ⟨h, ?_⟩
  rw [beta_value]
  apply ne_of_gt
  exact mul_pos (by norm_num) (div_pos
    (mul_pos (by norm_num [w]) (Real.sqrt_pos.mpr (by norm_num)))
    (Real.sqrt_pos.mpr (by norm_num)))

private theorem error_variance (b : Fin 2 → ℝ) :
    Var[fun x => twoTrait.aggregate x - twoTrait.index b x; γ] =
      2 - 2 * (b ⬝ᵥ ![(2 : ℝ), 1]) + b ⬝ᵥ (P *ᵥ b) := by
  have hH : MemLp twoTrait.aggregate 2 γ := by
    exact memLp_finsetSum' Finset.univ
      (fun i _ => (twoTrait.memLp_additive i).const_mul (twoTrait.economic i))
  have hI : MemLp (twoTrait.index b) 2 γ := by
    exact memLp_finsetSum' Finset.univ (fun i _ =>
      ((twoTrait.memLp_additive i).add (twoTrait.memLp_residual i)).const_mul (b i))
  rw [variance_fun_sub hH hI,
    covariance_comm, covariance_index_aggregate, variance_index,
    aggregate_variance, objective_covariance, fixture_covariances.1]

private theorem canonical_loss :
    Var[fun x => twoTrait.aggregate x - twoTrait.index w x; γ] = 5 / 8 := by
  rw [error_variance]
  norm_num [w, P, mulVec, dotProduct, Fin.sum_univ_two]

private theorem rescaled_loss :
    Var[fun x => twoTrait.aggregate x - twoTrait.index ((2 : ℝ) • w) x; γ] = 2 := by
  rw [error_variance]
  norm_num [w, P, mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]

private theorem minimum_variance :
    (∀ d, Var[fun x => twoTrait.aggregate x - twoTrait.index w x; γ] ≤
      Var[fun x => twoTrait.aggregate x - twoTrait.index d x; γ]) ∧
    ¬ (∀ d, Var[fun x => twoTrait.aggregate x - twoTrait.index ((2 : ℝ) • w) x; γ] ≤
      Var[fun x => twoTrait.aggregate x - twoTrait.index d x; γ]) ∧
    pearsonRatio γ (twoTrait.index ((2 : ℝ) • w)) twoTrait.aggregate =
      pearsonRatio γ (twoTrait.index w) twoTrait.aggregate ∧
    Var[fun x => twoTrait.aggregate x - twoTrait.index w x; γ] = 5 / 8 ∧
    Var[fun x => twoTrait.aggregate x - twoTrait.index ((2 : ℝ) • w) x; γ] = 2 := by
  have hr : pearsonRatio γ (twoTrait.index ((2 : ℝ) • w)) twoTrait.aggregate =
      pearsonRatio γ (twoTrait.index w) twoTrait.aggregate := by
    have hi : twoTrait.index ((2 : ℝ) • w) = fun x => 2 * twoTrait.index w x := by
      funext x
      exact smul_dotProduct 2 w (twoTrait.phenotype x)
    have hs : populationSD γ (fun x => 2 * twoTrait.index w x) =
        2 * populationSD γ (twoTrait.index w) := by
      rw [populationSD, variance_const_mul, Real.sqrt_mul (sq_nonneg (2 : ℝ)),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
      rfl
    rw [hi, pearsonRatio, pearsonRatio, covariance_const_mul_left, hs]
    field_simp
  refine ⟨(regressionWeights_iff_min_variance twoTrait w).mpr regression_weights.symm,
    ?_, hr, canonical_loss, rescaled_loss⟩
  rw [regressionWeights_iff_min_variance, regression_weights]
  intro h
  have := congrFun h 0
  norm_num [w, Pi.smul_apply, smul_eq_mul] at this

private abbrev coordinateLoading : Fin 2 → Fin 5 → ℝ :=
  ![![(1 : ℝ), 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
private abbrev outsideLoading : Fin 5 → ℝ := ![(0 : ℝ), 0, 0, 0, 1]

private theorem loading_variance (u : Fin 5 → ℝ) : Var[loading u; γ] = u ⬝ᵥ u := by
  rw [← covariance_self (loading_memLp u).aemeasurable, loading_cov]

private theorem orthogonal_correlation :
    Var[loading (coordinateLoading 0); γ] = 1 ∧
    Var[loading (coordinateLoading 1); γ] = 1 ∧
    cov[loading (coordinateLoading 0), loading (coordinateLoading 1); γ] = 0 ∧
    pearsonRatio γ (loading (coordinateLoading 0)) (loading (coordinateLoading 1)) = 0 := by
  have h0 : Var[loading (coordinateLoading 0); γ] = 1 := by
    rw [loading_variance]
    norm_num [dotProduct, Fin.sum_univ_succ]
  have h1 : Var[loading (coordinateLoading 1); γ] = 1 := by
    rw [loading_variance]
    norm_num [dotProduct, Fin.sum_univ_succ]
  have hc : cov[loading (coordinateLoading 0), loading (coordinateLoading 1); γ] = 0 := by
    rw [loading_cov]
    norm_num [dotProduct, Fin.sum_univ_succ]
  exact ⟨h0, h1, hc, pearsonRatio_eq_zero_of_covariance_eq_zero
    (by rw [h0]; norm_num) (by rw [h1]; norm_num) hc⟩

private noncomputable def independentScore : Latents →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi fun i => loading (coordinateLoading i)

private theorem independent_covariance :
    (fun i j => cov[fun x => independentScore x i, fun x => independentScore x j; γ]) =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  change cov[loading (coordinateLoading i), loading (coordinateLoading j); γ] = _
  rw [loading_cov]
  fin_cases i <;> fin_cases j <;> norm_num [dotProduct, Fin.sum_univ_succ]

private theorem outside_variance : Var[loading outsideLoading; γ] = 1 := by
  rw [loading_variance]
  norm_num [dotProduct, Fin.sum_univ_succ]

private theorem outside_covariance (i : Fin 2) :
    cov[fun x => independentScore x i, loading outsideLoading; γ] = 0 := by
  change cov[loading (coordinateLoading i), loading outsideLoading; γ] = 0
  rw [loading_cov]
  fin_cases i <;> norm_num [dotProduct, Fin.sum_univ_succ]

private theorem gaussian_independence :
    IndepFun (fun x => independentScore x 0) (fun x => independentScore x 1) γ ∧
    (∀ i, IndepFun (fun x => independentScore x i) (loading outsideLoading) γ) ∧
    (∀ i, cov[fun x => twoTrait.additive x i, loading outsideLoading; γ] = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · have hg : HasGaussianLaw (fun x =>
        (loading (coordinateLoading 0) x, loading (coordinateLoading 1) x)) γ :=
      IsGaussian.hasGaussianLaw_id.map_fun
        ((loading (coordinateLoading 0)).prod (loading (coordinateLoading 1)))
    exact hg.indepFun_of_covariance_eq_zero orthogonal_correlation.2.2.1
  · intro i
    have hg : HasGaussianLaw (fun x => (loading (coordinateLoading i) x, loading outsideLoading x)) γ :=
      IsGaussian.hasGaussianLaw_id.map_fun ((loading (coordinateLoading i)).prod (loading outsideLoading))
    exact hg.indepFun_of_covariance_eq_zero (outside_covariance i)
  · intro i
    change cov[loading (additiveLoading i), loading outsideLoading; γ] = 0
    rw [loading_cov]
    fin_cases i <;> norm_num [dotProduct, Fin.sum_univ_succ]

private theorem linear_zero_correlation :
    Matrix.PosDef (fun i j => cov[fun x => independentScore x i,
      fun x => independentScore x j; γ] : Matrix (Fin 2) (Fin 2) ℝ) ∧
    Var[loading outsideLoading; γ] = 1 ∧ a ≠ 0 ∧
    Var[fun x => a ⬝ᵥ independentScore x; γ] = 1 ∧
    pearsonRatio γ (fun x => a ⬝ᵥ independentScore x) (loading outsideLoading) = 0 := by
  have hp : Matrix.PosDef (fun i j => cov[fun x => independentScore x i,
      fun x => independentScore x j; γ] : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [independent_covariance]
    exact Matrix.PosDef.one
  have hv : Var[fun x => a ⬝ᵥ independentScore x; γ] = 1 := by
    have hf : (fun x => a ⬝ᵥ independentScore x) = loading (coordinateLoading 0) := by
      funext x
      simp [a, dotProduct, Fin.sum_univ_two, independentScore]
    rw [hf]
    exact orthogonal_correlation.1
  refine ⟨hp, outside_variance, a_ne, hv, ?_⟩
  exact pearsonRatio_linear_eq_zero_of_crossCovariance_eq_zero
    (fun i => loading_memLp (coordinateLoading i)) (loading_memLp outsideLoading)
    (by rw [outside_variance]; norm_num) hp outside_covariance a_ne

private theorem weights_nonzero : w ≠ 0 := by
  intro h
  have := congrFun h 0
  norm_num [w] at this

private theorem scaled_nonzero (k : ℝ) (hk : k ≠ 0) : k • w ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [w, Pi.smul_apply, smul_eq_mul] at h0
  exact hk (by linarith)

private theorem off_ray (k : ℝ) : a ≠ k • w := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  norm_num [a, w, Pi.smul_apply, smul_eq_mul] at h0 h1
  linarith

private theorem positive_ray (k : ℝ) :
    (∃ t : ℝ, 0 < t ∧ k • w = t • twoTrait.regressionWeights) ↔ 0 < k := by
  rw [regression_weights]
  constructor
  · rintro ⟨t, ht, h⟩
    have h0 := congrFun h 0
    norm_num [w, Pi.smul_apply, smul_eq_mul] at h0
    linarith
  · intro hk
    exact ⟨k, hk, rfl⟩

private theorem negative_ray (k : ℝ) :
    (∃ t : ℝ, t < 0 ∧ k • w = t • twoTrait.regressionWeights) ↔ k < 0 := by
  rw [regression_weights]
  constructor
  · rintro ⟨t, ht, h⟩
    have h0 := congrFun h 0
    norm_num [w, Pi.smul_apply, smul_eq_mul] at h0
    linarith
  · intro hk
    exact ⟨k, hk, rfl⟩

private noncomputable abbrev upper : ℝ :=
  √(twoTrait.objectiveCov ⬝ᵥ twoTrait.regressionWeights) / populationSD γ twoTrait.aggregate

private theorem upper_bound : pearsonRatio γ (twoTrait.index a) twoTrait.aggregate ≤ upper :=
  pearsonRatio_le twoTrait a_ne aggregate_positive objective_nonzero

private theorem upper_cases :
    pearsonRatio γ (twoTrait.index w) twoTrait.aggregate = upper ∧
    pearsonRatio γ (twoTrait.index (-w)) twoTrait.aggregate ≠ upper ∧
    pearsonRatio γ (twoTrait.index ((2 : ℝ) • w)) twoTrait.aggregate = upper ∧
    pearsonRatio γ (twoTrait.index a) twoTrait.aggregate ≠ upper := by
  have hp := pearsonRatio_eq_upper_iff twoTrait weights_nonzero aggregate_positive objective_nonzero
  have hn := pearsonRatio_eq_upper_iff twoTrait (neg_ne_zero.mpr weights_nonzero)
    aggregate_positive objective_nonzero
  have h2 := pearsonRatio_eq_upper_iff twoTrait (scaled_nonzero 2 (by norm_num))
    aggregate_positive objective_nonzero
  have he := pearsonRatio_eq_upper_iff twoTrait a_ne aggregate_positive objective_nonzero
  refine ⟨hp.mpr ⟨1, by norm_num, by rw [regression_weights]; simp⟩, ?_,
    h2.mpr ⟨2, by norm_num, by rw [regression_weights]⟩, ?_⟩
  · rw [← neg_one_smul ℝ w] at hn
    rw [positive_ray] at hn
    norm_num at hn
    convert hn using 1 <;> norm_num [upper, w, dotProduct, Fin.sum_univ_two]
  · intro h
    obtain ⟨k, _, hk⟩ := he.mp h
    rw [regression_weights] at hk
    exact off_ray k hk

private theorem lower_bound : -upper ≤ pearsonRatio γ (twoTrait.index a) twoTrait.aggregate :=
  lower_le_pearsonRatio twoTrait a_ne aggregate_positive objective_nonzero

private theorem lower_cases :
    pearsonRatio γ (twoTrait.index (-w)) twoTrait.aggregate = -upper ∧
    pearsonRatio γ (twoTrait.index w) twoTrait.aggregate ≠ -upper ∧
    pearsonRatio γ (twoTrait.index ((2 : ℝ) • w)) twoTrait.aggregate ≠ -upper ∧
    pearsonRatio γ (twoTrait.index a) twoTrait.aggregate ≠ -upper := by
  have hn := pearsonRatio_eq_lower_iff twoTrait (neg_ne_zero.mpr weights_nonzero)
    aggregate_positive objective_nonzero
  have hp := pearsonRatio_eq_lower_iff twoTrait weights_nonzero aggregate_positive objective_nonzero
  have h2 := pearsonRatio_eq_lower_iff twoTrait (scaled_nonzero 2 (by norm_num))
    aggregate_positive objective_nonzero
  have he := pearsonRatio_eq_lower_iff twoTrait a_ne aggregate_positive objective_nonzero
  refine ⟨hn.mpr ⟨-1, by norm_num, by rw [regression_weights]; simp⟩, ?_, ?_, ?_⟩
  · rw [← one_smul ℝ w, negative_ray] at hp
    norm_num at hp
    convert hp using 1
    norm_num [upper, dotProduct, Fin.sum_univ_two]
  · rw [negative_ray] at h2
    norm_num at h2
    convert h2 using 1 <;> norm_num [upper, w, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
  · intro h
    obtain ⟨k, _, hk⟩ := he.mp h
    rw [regression_weights] at hk
    exact off_ray k hk

private theorem strictly_between :
    -upper < pearsonRatio γ (twoTrait.index a) twoTrait.aggregate ∧
    pearsonRatio γ (twoTrait.index a) twoTrait.aggregate < upper := by
  exact ⟨lt_of_le_of_ne lower_bound (Ne.symm lower_cases.2.2.2),
    lt_of_le_of_ne upper_bound upper_cases.2.2.2⟩

private theorem optimal_squared_value :
    (twoTrait.objectiveCov ⬝ᵥ twoTrait.regressionWeights) / Var[twoTrait.aggregate; γ] =
      11 / 16 := by
  rw [objective_covariance, regression_weights, aggregate_variance]
  norm_num [w, dotProduct, Fin.sum_univ_two]

private theorem coordinate_squared :
    pearsonRatio γ (twoTrait.index a) twoTrait.aggregate ^ 2 = 2 / 3 := by
  rw [signed_quotient.2, div_pow, mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

private theorem squared_bound :
    pearsonRatio γ (twoTrait.index a) twoTrait.aggregate ^ 2 ≤ 11 / 16 ∧
    pearsonRatio γ (twoTrait.index a) twoTrait.aggregate ^ 2 = 2 / 3 ∧
    pearsonRatio γ (twoTrait.index a) twoTrait.aggregate ^ 2 < 11 / 16 := by
  have h := pearsonRatio_sq_le twoTrait a_ne aggregate_positive objective_nonzero
  rw [optimal_squared_value] at h
  exact ⟨h, coordinate_squared, by rw [coordinate_squared]; norm_num⟩

private theorem squared_cases :
    pearsonRatio γ (twoTrait.index w) twoTrait.aggregate ^ 2 = 11 / 16 ∧
    pearsonRatio γ (twoTrait.index (-w)) twoTrait.aggregate ^ 2 = 11 / 16 ∧
    pearsonRatio γ (twoTrait.index ((2 : ℝ) • w)) twoTrait.aggregate ^ 2 = 11 / 16 ∧
    pearsonRatio γ (twoTrait.index a) twoTrait.aggregate ^ 2 ≠ 11 / 16 := by
  have hp := pearsonRatio_sq_eq_upper_iff twoTrait weights_nonzero
    aggregate_positive objective_nonzero
  have hn := pearsonRatio_sq_eq_upper_iff twoTrait (neg_ne_zero.mpr weights_nonzero)
    aggregate_positive objective_nonzero
  have h2 := pearsonRatio_sq_eq_upper_iff twoTrait (scaled_nonzero 2 (by norm_num))
    aggregate_positive objective_nonzero
  have he := pearsonRatio_sq_eq_upper_iff twoTrait a_ne aggregate_positive objective_nonzero
  rw [optimal_squared_value] at hp hn h2 he
  refine ⟨hp.mpr ⟨1, by norm_num, by rw [regression_weights]; simp⟩,
    hn.mpr ⟨-1, by norm_num, by rw [regression_weights]; simp⟩,
    h2.mpr ⟨2, by norm_num, by rw [regression_weights]⟩, ?_⟩
  intro h
  obtain ⟨k, _, hk⟩ := he.mp h
  rw [regression_weights] at hk
  exact off_ray k hk

private theorem beta_sum :
    (∑ i, twoTrait.beta i *
      pearsonRatio γ (fun x => twoTrait.phenotype x i) twoTrait.aggregate) = 11 / 16 := by
  rw [sum_beta_mul_pearsonRatio twoTrait aggregate_positive, optimal_squared_value]

private theorem canonical_squared_sum :
    pearsonRatio γ (twoTrait.index w) twoTrait.aggregate ^ 2 =
      (∑ i, twoTrait.beta i *
        pearsonRatio γ (fun x => twoTrait.phenotype x i) twoTrait.aggregate) ∧
    pearsonRatio γ (twoTrait.index w) twoTrait.aggregate ^ 2 = 11 / 16 := by
  have h := pearsonRatio_sq_regressionWeights_eq_sum twoTrait aggregate_positive objective_nonzero
  rw [regression_weights] at h
  exact ⟨h, h.trans beta_sum⟩

private theorem canonical_positive_sqrt :
    pearsonRatio γ (twoTrait.index w) twoTrait.aggregate = √(11 / 16) ∧
    0 < pearsonRatio γ (twoTrait.index w) twoTrait.aggregate := by
  have h := pearsonRatio_regressionWeights_eq_sqrt_sum twoTrait
    aggregate_positive objective_nonzero
  rw [regression_weights, beta_sum] at h
  exact ⟨h, by rw [h]; exact Real.sqrt_pos.mpr (by norm_num)⟩

private noncomputable def score (U : Fin 2 → Fin 5 → ℝ) : Latents →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi fun i => loading (U i)

private theorem score_phenotype (U V : Fin 2 → Fin 5 → ℝ) (i : Fin 2) :
    (fun x => score U x i + score V x i) = loading (U i + V i) := by
  funext x
  change ⟪WithLp.toLp 2 (U i), x⟫ + ⟪WithLp.toLp 2 (V i), x⟫ =
    ⟪WithLp.toLp 2 (U i + V i), x⟫
  exact (inner_add_left _ _ _).symm

private theorem score_covariance (U V : Fin 2 → Fin 5 → ℝ)
    (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (h : ∀ i j, (U i + V i) ⬝ᵥ (U j + V j) = Q i j) :
    (fun i j => cov[fun x => score U x i + score V x i,
      fun x => score U x j + score V x j; γ]) = Q := by
  ext i j
  rw [score_phenotype, score_phenotype, loading_cov]
  exact h i j

private noncomputable def fromLoadings (U V : Fin 2 → Fin 5 → ℝ)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hp : Q.PosDef)
    (hc : ∀ i j, (U i + V i) ⬝ᵥ (U j + V j) = Q i j)
    (ho : ∀ i j, U i ⬝ᵥ V j = 0) : Model 2 Latents γ where
  additive := score U
  residual := score V
  economic := a
  measurable_additive := (score U).continuous.measurable
  measurable_residual := (score V).continuous.measurable
  memLp_additive i := loading_memLp (U i)
  memLp_residual i := loading_memLp (V i)
  orthogonal i j := (loading_cov (U i) (V j)).trans (ho i j)
  posDef := score_covariance U V Q hc ▸ hp

private theorem diagonal_posDef (d : ℝ) (hd : 0 < d) :
    Matrix.PosDef (!![d, 0; 0, d] : Matrix (Fin 2) (Fin 2) ℝ) := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  · intro x hx
    change 0 < x ⬝ᵥ (!![d, 0; 0, d] *ᵥ x)
    simp [mulVec, dotProduct, Fin.sum_univ_two]
    have h : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra! h
      apply hx
      funext i
      fin_cases i
      · exact h.1
      · exact h.2
    have hs : 0 < (x 0) ^ 2 + (x 1) ^ 2 := by
      rcases h with h | h <;> nlinarith [sq_pos_of_ne_zero h, sq_nonneg (x 0), sq_nonneg (x 1)]
    nlinarith [mul_pos hd hs]

private abbrev diagonalP : Matrix (Fin 2) (Fin 2) ℝ := !![(2 : ℝ), 0; 0, 2]
private abbrev onlyP : Matrix (Fin 2) (Fin 2) ℝ := !![(3 : ℝ), 0; 0, 3]
private abbrev oppositeResidual : Fin 2 → Fin 5 → ℝ :=
  ![![(0 : ℝ), 0, 0, 1, 0], ![0, 0, 0, -1, 0]]
private abbrev sharedResidual : Fin 2 → Fin 5 → ℝ :=
  ![![(0 : ℝ), 0, 1, 1, 0], ![0, 0, 1, 0, 1]]

private noncomputable def diagonal : Model 2 Latents γ :=
  fromLoadings coordinateLoading residualLoading diagonalP (diagonal_posDef 2 (by norm_num))
    (by intro i j; fin_cases i <;> fin_cases j <;>
      norm_num [diagonalP, dotProduct, Fin.sum_univ_succ])
    (by intro i j; fin_cases i <;> fin_cases j <;>
      norm_num [dotProduct, Fin.sum_univ_succ])

private noncomputable def phenotypicOnly : Model 2 Latents γ :=
  fromLoadings additiveLoading oppositeResidual onlyP (diagonal_posDef 3 (by norm_num))
    (by intro i j; fin_cases i <;> fin_cases j <;>
      norm_num [onlyP, dotProduct, Fin.sum_univ_succ])
    (by intro i j; fin_cases i <;> fin_cases j <;>
      norm_num [dotProduct, Fin.sum_univ_succ])

private noncomputable def geneticOnly : Model 2 Latents γ :=
  fromLoadings coordinateLoading sharedResidual P P_posDef
    (by intro i j; fin_cases i <;> fin_cases j <;>
      norm_num [P, dotProduct, Fin.sum_univ_succ])
    (by intro i j; fin_cases i <;> fin_cases j <;>
      norm_num [dotProduct, Fin.sum_univ_succ])

private theorem diagonal_covariances : diagonal.phenotypicCov = diagonalP ∧ diagonal.geneticCov = 1 := by
  constructor
  · ext i j
    change cov[fun x => score coordinateLoading x i + score residualLoading x i,
      fun x => score coordinateLoading x j + score residualLoading x j; γ] = _
    rw [score_phenotype, score_phenotype, loading_cov]
    fin_cases i <;> fin_cases j <;> norm_num [diagonalP, dotProduct, Fin.sum_univ_succ]
  · ext i j
    change cov[loading (coordinateLoading i), loading (coordinateLoading j); γ] = _
    rw [loading_cov]
    fin_cases i <;> fin_cases j <;> norm_num [dotProduct, Fin.sum_univ_succ]

private theorem phenotypicOnly_covariances :
    phenotypicOnly.phenotypicCov = onlyP ∧ phenotypicOnly.geneticCov = G := by
  constructor
  · ext i j
    change cov[fun x => score additiveLoading x i + score oppositeResidual x i,
      fun x => score additiveLoading x j + score oppositeResidual x j; γ] = _
    rw [score_phenotype, score_phenotype, loading_cov]
    fin_cases i <;> fin_cases j <;> norm_num [onlyP, dotProduct, Fin.sum_univ_succ]
  · ext i j
    change cov[loading (additiveLoading i), loading (additiveLoading j); γ] = _
    rw [loading_cov]
    fin_cases i <;> fin_cases j <;> norm_num [G, dotProduct, Fin.sum_univ_succ]

private theorem geneticOnly_covariances : geneticOnly.phenotypicCov = P ∧ geneticOnly.geneticCov = 1 := by
  constructor
  · ext i j
    change cov[fun x => score coordinateLoading x i + score sharedResidual x i,
      fun x => score coordinateLoading x j + score sharedResidual x j; γ] = _
    rw [score_phenotype, score_phenotype, loading_cov]
    fin_cases i <;> fin_cases j <;> norm_num [P, dotProduct, Fin.sum_univ_succ]
  · ext i j
    change cov[loading (coordinateLoading i), loading (coordinateLoading j); γ] = _
    rw [loading_cov]
    fin_cases i <;> fin_cases j <;> norm_num [dotProduct, Fin.sum_univ_succ]

private theorem diagonal_phenotypic (i j : Fin 2) (h : i ≠ j) : diagonal.phenotypicCov i j = 0 := by
  rw [diagonal_covariances.1]
  fin_cases i <;> fin_cases j <;> simp_all [diagonalP]

private theorem diagonal_genetic (i j : Fin 2) (h : i ≠ j) : diagonal.geneticCov i j = 0 := by
  rw [diagonal_covariances.2]
  exact Matrix.one_apply_ne h

private theorem diagonal_shortcut :
    diagonal.regressionWeights 0 = diagonal.economic 0 * diagonal.heritability 0 ∧
    diagonal.regressionWeights 1 = diagonal.economic 1 * diagonal.heritability 1 ∧
    diagonal.regressionWeights = ![(1 : ℝ) / 2, 0] := by
  have h0 := regressionWeights_eq_economic_mul_heritability diagonal
    diagonal_phenotypic diagonal_genetic 0
  have h1 := regressionWeights_eq_economic_mul_heritability diagonal
    diagonal_phenotypic diagonal_genetic 1
  refine ⟨h0, h1, ?_⟩
  ext i
  fin_cases i
  · change diagonal.regressionWeights 0 = (1 / 2 : ℝ)
    rw [h0, Model.heritability, diagonal_covariances.1, diagonal_covariances.2]
    norm_num [diagonalP, diagonal, fromLoadings, a]
  · change diagonal.regressionWeights 1 = 0
    rw [h1, Model.heritability, diagonal_covariances.1, diagonal_covariances.2]
    norm_num [diagonalP, diagonal, fromLoadings, a]

private theorem diagonal_objective : diagonal.objectiveCov = a := by
  rw [objectiveCov_eq_geneticCov_mulVec, diagonal_covariances.2, one_mulVec]
  rfl

private theorem diagonal_positive : 0 < Var[diagonal.aggregate; γ] := by
  rw [variance_aggregate, diagonal_covariances.2, one_mulVec]
  change 0 < a ⬝ᵥ a
  norm_num [a, dotProduct, Fin.sum_univ_two]

private theorem diagonal_nonzero : diagonal.objectiveCov ≠ 0 := by
  rw [diagonal_objective]
  exact a_ne

private theorem diagonal_maximizers :
    (∀ d : Fin 2 → ℝ, d ≠ 0 →
      pearsonRatio γ (diagonal.index d) diagonal.aggregate ≤
      pearsonRatio γ (diagonal.index a) diagonal.aggregate) ∧
    ¬ (∀ d : Fin 2 → ℝ, d ≠ 0 →
      pearsonRatio γ (diagonal.index d) diagonal.aggregate ≤
      pearsonRatio γ (diagonal.index (-a)) diagonal.aggregate) ∧
    ¬ (∀ d : Fin 2 → ℝ, d ≠ 0 →
      pearsonRatio γ (diagonal.index d) diagonal.aggregate ≤
      pearsonRatio γ (diagonal.index e) diagonal.aggregate) := by
  have hecon : (fun i => diagonal.economic i * diagonal.heritability i) = ![(1 : ℝ) / 2, 0] := by
    rw [← diagonal_shortcut.2.2]
    funext i
    exact (regressionWeights_eq_economic_mul_heritability diagonal
      diagonal_phenotypic diagonal_genetic i).symm
  have he : e ≠ 0 := by
    intro h
    have := congrFun h 1
    norm_num [e] at this
  have hp := diagonal_pearsonRatio_max_iff diagonal diagonal_phenotypic diagonal_genetic
    a_ne diagonal_positive diagonal_nonzero
  have hn := diagonal_pearsonRatio_max_iff diagonal diagonal_phenotypic diagonal_genetic
    (neg_ne_zero.mpr a_ne) diagonal_positive diagonal_nonzero
  have ho := diagonal_pearsonRatio_max_iff diagonal diagonal_phenotypic diagonal_genetic
    he diagonal_positive diagonal_nonzero
  rw [hecon] at hp hn ho
  refine ⟨hp.mpr ⟨2, by norm_num, by ext i; fin_cases i <;>
    norm_num [a, Pi.smul_apply, smul_eq_mul]⟩, ?_, ?_⟩
  · intro h
    obtain ⟨k, hk, hb⟩ := hn.mp h
    have := congrFun hb 0
    norm_num [a, Pi.smul_apply, smul_eq_mul] at this
    linarith
  · intro h
    obtain ⟨k, _, hb⟩ := ho.mp h
    have := congrFun hb 1
    norm_num [e, Pi.smul_apply, smul_eq_mul] at this

private theorem phenotypic_diagonal_only :
    (∀ i j : Fin 2, i ≠ j → phenotypicOnly.phenotypicCov i j = 0) ∧
    phenotypicOnly.geneticCov 0 1 = 1 ∧
    phenotypicOnly.regressionWeights = ![(2 : ℝ) / 3, 1 / 3] ∧
    phenotypicOnly.regressionWeights 1 ≠ phenotypicOnly.economic 1 * phenotypicOnly.heritability 1 := by
  have hw : phenotypicOnly.regressionWeights = ![(2 : ℝ) / 3, 1 / 3] := by
    rw [regressionWeights_eq_geneticCov, phenotypicOnly_covariances.1, phenotypicOnly_covariances.2]
    change onlyP⁻¹ *ᵥ (G *ᵥ a) = _
    apply solve_two
    · norm_num [onlyP, Matrix.det_fin_two_of]
    · ext i
      fin_cases i <;> norm_num [onlyP, G, a, mulVec, dotProduct, Fin.sum_univ_two]
  refine ⟨?_, ?_, hw, ?_⟩
  · intro i j hij
    rw [phenotypicOnly_covariances.1]
    fin_cases i <;> fin_cases j <;> simp_all [onlyP]
  · rw [phenotypicOnly_covariances.2]
    norm_num [G]
  · rw [hw]
    change (1 / 3 : ℝ) ≠ a 1 * phenotypicOnly.heritability 1
    norm_num [a]

private theorem genetic_diagonal_only :
    (∀ i j : Fin 2, i ≠ j → geneticOnly.geneticCov i j = 0) ∧
    geneticOnly.phenotypicCov 0 1 = 1 ∧
    geneticOnly.regressionWeights = ![(3 : ℝ) / 8, -(1 / 8)] ∧
    geneticOnly.regressionWeights 1 ≠ geneticOnly.economic 1 * geneticOnly.heritability 1 := by
  have hw : geneticOnly.regressionWeights = ![(3 : ℝ) / 8, -(1 / 8)] := by
    rw [regressionWeights_eq_geneticCov, geneticOnly_covariances.1, geneticOnly_covariances.2,
      one_mulVec]
    change P⁻¹ *ᵥ a = _
    apply solve_two
    · norm_num [P, Matrix.det_fin_two_of]
    · ext i
      fin_cases i <;> norm_num [P, a, mulVec, dotProduct, Fin.sum_univ_two]
  refine ⟨?_, ?_, hw, ?_⟩
  · intro i j hij
    rw [geneticOnly_covariances.2]
    exact Matrix.one_apply_ne hij
  · rw [geneticOnly_covariances.1]
    norm_num [P]
  · rw [hw]
    change -(1 / 8 : ℝ) ≠ a 1 * geneticOnly.heritability 1
    norm_num [a]

#print axioms loading_cov
#print axioms loading_memLp
#print axioms phenotypeScore
#print axioms twoTrait_phenotypeCov
#print axioms P_posDef
#print axioms fixture_covariances
#print axioms a_ne
#print axioms index_covariance
#print axioms index_variance
#print axioms aggregate_variance
#print axioms aggregate_positive
#print axioms covariance_decomposition
#print axioms objective_covariance
#print axioms aggregate_covariance
#print axioms solve_two
#print axioms regression_weights
#print axioms objective_nonzero
#print axioms signed_quotient
#print axioms positive_index
#print axioms zero_index
#print axioms economic_pairing
#print axioms zero_objective
#print axioms phenotype_variance
#print axioms phenotype_correlation
#print axioms phenotype_objective_correlation
#print axioms beta_value
#print axioms normal_equations
#print axioms standardized_equation
#print axioms error_variance
#print axioms canonical_loss
#print axioms rescaled_loss
#print axioms minimum_variance
#print axioms loading_variance
#print axioms orthogonal_correlation
#print axioms independent_covariance
#print axioms outside_variance
#print axioms outside_covariance
#print axioms gaussian_independence
#print axioms linear_zero_correlation
#print axioms weights_nonzero
#print axioms scaled_nonzero
#print axioms off_ray
#print axioms positive_ray
#print axioms negative_ray
#print axioms upper_bound
#print axioms upper_cases
#print axioms lower_bound
#print axioms lower_cases
#print axioms strictly_between
#print axioms optimal_squared_value
#print axioms coordinate_squared
#print axioms squared_bound
#print axioms squared_cases
#print axioms beta_sum
#print axioms canonical_squared_sum
#print axioms canonical_positive_sqrt
#print axioms score_phenotype
#print axioms score_covariance
#print axioms diagonal_posDef
#print axioms diagonal_covariances
#print axioms phenotypicOnly_covariances
#print axioms geneticOnly_covariances
#print axioms diagonal_phenotypic
#print axioms diagonal_genetic
#print axioms diagonal_shortcut
#print axioms diagonal_objective
#print axioms diagonal_positive
#print axioms diagonal_nonzero
#print axioms diagonal_maximizers
#print axioms phenotypic_diagonal_only
#print axioms genetic_diagonal_only

end SmithHazel.MatrixTests
