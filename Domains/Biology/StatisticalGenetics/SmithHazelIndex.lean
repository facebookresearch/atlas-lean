/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Domains.Biology.StatisticalGenetics.SmithHazel
import Domains.Biology.PopulationGenetics.Classical.LandeResponse
import MathlibExt.Probability.Causality.MissingData.GaussianSelection
import MathlibExt.Probability.Distributions.GaussianCdf

/-!
# Smith–Hazel selection index

Frozen proof targets for Hazel (1943), equations (1)–(8) and pp. 486–487.
Joint Gaussianity is an explicit hypothesis for the truncation results.
-/

open MeasureTheory ProbabilityTheory Matrix
open MathlibExt.Probability.Causality.MissingData (inverseMillsRatio)
open scoped BigOperators Matrix

namespace SmithHazel

private lemma memLp_linear {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → Fin n → ℝ} (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ)
    (b : Fin n → ℝ) : MemLp (fun ω => b ⬝ᵥ X ω) 2 μ := by
  convert! memLp_finsetSum' Finset.univ (fun i _ => (hX i).const_mul (b i)) using 1
  funext ω
  simp [dotProduct]

private lemma covariance_linear_left {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → Fin n → ℝ} {H : Ω → ℝ}
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ) (hH : MemLp H 2 μ)
    (b : Fin n → ℝ) :
    cov[fun ω => b ⬝ᵥ X ω, H; μ] =
      b ⬝ᵥ (fun i => cov[fun ω => X ω i, H; μ]) := by
  simp only [dotProduct]
  rw [covariance_fun_sum_left (fun i => (hX i).const_mul (b i)) hH]
  simp only [covariance_const_mul_left]

private lemma covariance_linear_linear {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X Y : Ω → Fin n → ℝ}
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ)
    (hY : ∀ i, MemLp (fun ω => Y ω i) 2 μ) (b d : Fin n → ℝ) :
    cov[fun ω => b ⬝ᵥ X ω, fun ω => d ⬝ᵥ Y ω; μ] =
      b ⬝ᵥ ((fun i j => cov[fun ω => X ω i, fun ω => Y ω j; μ]) *ᵥ d) := by
  simp only [dotProduct, mulVec]
  rw [covariance_fun_sum_fun_sum (fun i => (hX i).const_mul (b i))
    (fun j => (hY j).const_mul (d j))]
  simp only [covariance_const_mul_left, covariance_const_mul_right,
    Finset.mul_sum]
  congr 1
  funext i
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma Model.memLp_phenotype {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) (i : Fin n) : MemLp (fun ω => M.phenotype ω i) 2 μ :=
  (M.memLp_additive i).add (M.memLp_residual i)

private lemma Model.memLp_index {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) (b : Fin n → ℝ) : MemLp (M.index b) 2 μ :=
  memLp_linear M.memLp_phenotype b

private lemma Model.memLp_aggregate {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) : MemLp M.aggregate 2 μ :=
  memLp_linear M.memLp_additive M.economic


private lemma Model.phenotypicCov_posDef {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (M : Model n Ω μ) : M.phenotypicCov.PosDef := by
  change Matrix.PosDef (fun i j => cov[fun ω => M.additive ω i + M.residual ω i,
    fun ω => M.additive ω j + M.residual ω j; μ])
  exact M.posDef

/-- B1. The covariance of two actual indices is the finite bilinear form. -/
theorem covariance_index_index {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) (b d : Fin n → ℝ) :
    cov[M.index b, M.index d; μ] = b ⬝ᵥ (M.phenotypicCov *ᵥ d) := by
  exact covariance_linear_linear M.memLp_phenotype M.memLp_phenotype b d

/-- B1. The variance of an actual index is the phenotypic quadratic form. -/
theorem variance_index {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) (b : Fin n → ℝ) :
    Var[M.index b; μ] = b ⬝ᵥ (M.phenotypicCov *ᵥ b) := by
  rw [← covariance_self (M.memLp_index b).aemeasurable]
  exact covariance_index_index M b b

/-- B1. The covariance of an actual index with the objective is the finite pairing. -/
theorem covariance_index_aggregate {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) (b : Fin n → ℝ) :
    cov[M.index b, M.aggregate; μ] = b ⬝ᵥ M.objectiveCov := by
  exact covariance_linear_left M.memLp_phenotype M.memLp_aggregate b

/-- B1. The variance of the actual objective is the genetic quadratic form. -/
theorem variance_aggregate {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) :
    Var[M.aggregate; μ] = M.economic ⬝ᵥ (M.geneticCov *ᵥ M.economic) := by
  rw [← covariance_self M.memLp_aggregate.aemeasurable]
  exact covariance_linear_linear M.memLp_additive M.memLp_additive M.economic M.economic

/-- B1. The population Pearson quotient agrees with its finite matrix expression. -/
theorem pearsonRatio_index_eq {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) {b : Fin n → ℝ} (_hb : b ≠ 0)
    (_hH : 0 < Var[M.aggregate; μ]) :
    pearsonRatio μ (M.index b) M.aggregate =
      (b ⬝ᵥ M.objectiveCov) /
        (√(b ⬝ᵥ (M.phenotypicCov *ᵥ b)) *
          √(M.economic ⬝ᵥ (M.geneticCov *ᵥ M.economic))) := by
  simp only [pearsonRatio, populationSD, covariance_index_aggregate,
    variance_index, variance_aggregate]

/-- K3. The variance decomposition in Hazel's equation (8), including cross-trait entries. -/
theorem phenotypicCov_eq_add {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) :
    M.phenotypicCov = M.geneticCov + M.residualCov := by
  ext i j
  change cov[(fun ω => M.additive ω i) + (fun ω => M.residual ω i),
    (fun ω => M.additive ω j) + (fun ω => M.residual ω j); μ] = _
  rw [covariance_add_left (M.memLp_additive i) (M.memLp_residual i)
    ((M.memLp_additive j).add (M.memLp_residual j)),
    covariance_add_right (M.memLp_additive i) (M.memLp_additive j) (M.memLp_residual j),
    covariance_add_right (M.memLp_residual i) (M.memLp_additive j) (M.memLp_residual j),
    M.orthogonal i j, covariance_comm (fun ω => M.residual ω i), M.orthogonal j i]
  simp [Model.geneticCov, Model.residualCov]

/-- B2 and K3. Hazel's path-coefficient formula in unstandardized covariance form. -/
theorem objectiveCov_eq_geneticCov_mulVec {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (M : Model n Ω μ) :
    M.objectiveCov = M.geneticCov *ᵥ M.economic := by
  funext i
  change cov[fun ω => M.phenotype ω i, fun ω => ∑ j, M.economic j * M.additive ω j; μ] = _
  rw [covariance_fun_sum_right (fun j => (M.memLp_additive j).const_mul (M.economic j))
    (M.memLp_phenotype i)]
  simp only [covariance_const_mul_right, mulVec, dotProduct, Model.geneticCov]
  apply Finset.sum_congr rfl
  intro j _
  change M.economic j * cov[(fun ω => M.additive ω i) + (fun ω => M.residual ω i),
    fun ω => M.additive ω j; μ] = _
  rw [covariance_add_left (M.memLp_additive i) (M.memLp_residual i) (M.memLp_additive j),
    covariance_comm (fun ω => M.residual ω i), M.orthogonal j i]
  simp [mul_comm]

/-- K3. The canonical weights in genetic covariance form. -/
theorem regressionWeights_eq_geneticCov {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (M : Model n Ω μ) :
    M.regressionWeights = M.phenotypicCov⁻¹ *ᵥ (M.geneticCov *ᵥ M.economic) := by
  rw [Model.regressionWeights, objectiveCov_eq_geneticCov_mulVec]

/-- K0. An index has positive variance exactly when its coefficient vector is nonzero. -/
theorem variance_index_pos_iff {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) (b : Fin n → ℝ) :
    0 < Var[M.index b; μ] ↔ b ≠ 0 := by
  rw [variance_index]
  constructor
  · intro h hz
    simp [hz] at h
  · intro hb
    simpa using M.phenotypicCov_posDef.dotProduct_mulVec_pos hb

/-- K0. The zero index is precisely the excluded zero-variance case. -/
theorem variance_index_eq_zero_iff {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) (b : Fin n → ℝ) :
    Var[M.index b; μ] = 0 ↔ b = 0 := by
  constructor
  · intro h
    by_contra hb
    have := (variance_index_pos_iff M b).mpr hb
    linarith
  · intro h
    simp [variance_index, h]

/-- K0. Pairing the economic weights with the cross-covariance gives objective variance. -/
theorem economic_dot_objectiveCov {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) :
    M.economic ⬝ᵥ M.objectiveCov = Var[M.aggregate; μ] := by
  rw [objectiveCov_eq_geneticCov_mulVec, variance_aggregate]

/-- K0. In the additive/residual model the objective variance vanishes exactly when c does. -/
theorem variance_aggregate_eq_zero_iff {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) :
    Var[M.aggregate; μ] = 0 ↔ M.objectiveCov = 0 := by
  have hG : M.geneticCov.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · ext i j
      simpa [Model.geneticCov] using
        covariance_comm (fun ω => M.additive ω j) (fun ω => M.additive ω i) (μ := μ)
    · intro x
      have hx := covariance_linear_linear M.memLp_additive M.memLp_additive x x
      rw [covariance_self (memLp_linear M.memLp_additive x).aemeasurable] at hx
      change Var[fun ω => x ⬝ᵥ M.additive ω; μ] = x ⬝ᵥ (M.geneticCov *ᵥ x) at hx
      simpa only [star_trivial, ← hx] using
        variance_nonneg (fun ω => x ⬝ᵥ M.additive ω) μ
  rw [variance_aggregate, objectiveCov_eq_geneticCov_mulVec]
  simpa using hG.dotProduct_mulVec_zero_iff (x := M.economic)

/-- K0. For a general pair, zero covariance gives zero correlation on its defined domain. -/
theorem pearsonRatio_eq_zero_of_covariance_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f g : Ω → ℝ}
    (_hf : 0 < Var[f; μ]) (_hg : 0 < Var[g; μ]) (hcov : cov[f, g; μ] = 0) :
    pearsonRatio μ f g = 0 := by
  simp [pearsonRatio, hcov]

/-- K0. Outside the additive decomposition, a zero phenotype–objective covariance vector
gives zero correlation for each nonzero index with positive definite phenotype covariance. -/
theorem pearsonRatio_linear_eq_zero_of_crossCovariance_eq_zero
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → Fin n → ℝ} {H : Ω → ℝ} (_hX : ∀ i, MemLp (fun ω => X ω i) 2 μ)
    (_hH : MemLp H 2 μ) (_hHpos : 0 < Var[H; μ])
    (_hP : Matrix.PosDef (fun i j => cov[fun ω => X ω i, fun ω => X ω j; μ] :
      Matrix (Fin n) (Fin n) ℝ))
    (_hc : ∀ i, cov[fun ω => X ω i, H; μ] = 0) {b : Fin n → ℝ} (_hb : b ≠ 0) :
    pearsonRatio μ (fun ω => b ⬝ᵥ X ω) H = 0 := by
  have hcov := covariance_linear_left _hX _hH b
  simp only [_hc] at hcov
  simp [pearsonRatio, hcov]

/-- K2. The unstandardized normal equations uniquely characterize the canonical weights. -/
theorem normalEquations_iff {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) (b : Fin n → ℝ) :
    M.phenotypicCov *ᵥ b = M.objectiveCov ↔ b = M.regressionWeights := by
  classical
  let : Invertible M.phenotypicCov := M.phenotypicCov_posDef.isUnit.invertible
  constructor
  · intro h
    exact (Matrix.inv_mulVec_eq_vec h.symm).symm
  · rintro rfl
    rw [Model.regressionWeights, Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible,
      Matrix.one_mulVec]

private lemma Model.normal_weights {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) : M.phenotypicCov *ᵥ M.regressionWeights = M.objectiveCov :=
  (normalEquations_iff M M.regressionWeights).mpr rfl

private lemma Model.pair_comm {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) (b d : Fin n → ℝ) :
    b ⬝ᵥ (M.phenotypicCov *ᵥ d) = d ⬝ᵥ (M.phenotypicCov *ᵥ b) := by
  simpa using M.phenotypicCov_posDef.isHermitian.star_dotProduct_mulVec_comm b d

private lemma Model.weights_ne_zero {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) (hc : M.objectiveCov ≠ 0) : M.regressionWeights ≠ 0 := by
  intro h
  have := M.normal_weights
  simp only [h, mulVec_zero] at this
  exact hc this.symm

private lemma Model.objective_pair_pos {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) (hc : M.objectiveCov ≠ 0) :
    0 < M.objectiveCov ⬝ᵥ M.regressionWeights := by
  have h := M.phenotypicCov_posDef.dotProduct_mulVec_pos (M.weights_ne_zero hc)
  simpa only [star_trivial, M.normal_weights, dotProduct_comm] using h

private lemma Model.quadratic_sub_weights {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (M : Model n Ω μ) (b : Fin n → ℝ) (k : ℝ) :
    (b - k • M.regressionWeights) ⬝ᵥ
        (M.phenotypicCov *ᵥ (b - k • M.regressionWeights)) =
      b ⬝ᵥ (M.phenotypicCov *ᵥ b) - 2 * k * (b ⬝ᵥ M.objectiveCov) +
        k ^ 2 * (M.objectiveCov ⬝ᵥ M.regressionWeights) := by
  have hcross : M.regressionWeights ⬝ᵥ (M.phenotypicCov *ᵥ b) =
      b ⬝ᵥ M.objectiveCov := by rw [← M.pair_comm b, M.normal_weights]
  simp only [mulVec_sub, mulVec_smul, dotProduct_sub, sub_dotProduct,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, M.normal_weights, hcross]
  rw [dotProduct_comm M.regressionWeights M.objectiveCov]
  ring

private lemma Model.error_variance {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) (b : Fin n → ℝ) :
    Var[fun ω => M.aggregate ω - M.index b ω; μ] =
      Var[M.aggregate; μ] - 2 * (b ⬝ᵥ M.objectiveCov) +
        b ⬝ᵥ (M.phenotypicCov *ᵥ b) := by
  rw [variance_fun_sub M.memLp_aggregate (M.memLp_index b),
    covariance_comm, covariance_index_aggregate, variance_index]

private lemma Model.error_variance_decomposition {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (M : Model n Ω μ) (b : Fin n → ℝ) :
    Var[fun ω => M.aggregate ω - M.index b ω; μ] =
      Var[fun ω => M.aggregate ω - M.index M.regressionWeights ω; μ] +
        (b - M.regressionWeights) ⬝ᵥ (M.phenotypicCov *ᵥ (b - M.regressionWeights)) := by
  have hq := M.quadratic_sub_weights b 1
  simp only [one_smul, one_pow, mul_one, one_mul] at hq
  rw [M.error_variance b, M.error_variance M.regressionWeights, hq, M.normal_weights,
    dotProduct_comm M.regressionWeights M.objectiveCov]
  ring

private lemma Model.sd_phenotype_pos {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (M : Model n Ω μ) (i : Fin n) :
    0 < populationSD μ (fun ω => M.phenotype ω i) :=
  Real.sqrt_pos.mpr (M.variance_phenotype_pos i)

/-- K2. Hazel's printed normal equations, in correlation coordinates. -/
theorem standardized_normalEquations {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) (_hH : 0 < Var[M.aggregate; μ]) (i : Fin n) :
    (∑ j, pearsonRatio μ (fun ω => M.phenotype ω i) (fun ω => M.phenotype ω j) *
      M.beta j) = pearsonRatio μ (fun ω => M.phenotype ω i) M.aggregate := by
  have h : (∑ j, M.phenotypicCov i j * M.regressionWeights j) = M.objectiveCov i :=
    congrFun M.normal_weights i
  unfold pearsonRatio Model.beta
  have heach : ∀ j, M.phenotypicCov i j /
      (populationSD μ (fun ω => M.phenotype ω i) *
        populationSD μ (fun ω => M.phenotype ω j)) *
      (M.regressionWeights j * populationSD μ (fun ω => M.phenotype ω j) /
        populationSD μ M.aggregate) =
      (M.phenotypicCov i j * M.regressionWeights j) /
        (populationSD μ (fun ω => M.phenotype ω i) * populationSD μ M.aggregate) := by
    intro j
    field_simp [(M.sd_phenotype_pos i).ne', (M.sd_phenotype_pos j).ne',
      (Real.sqrt_pos.mpr _hH).ne']
  change (∑ j, M.phenotypicCov i j / _ * _) = M.objectiveCov i / _
  simp_rw [heach]
  rw [← Finset.sum_div, h]

/-- K2. The canonical weights uniquely minimize mean-centered squared prediction error. -/
theorem regressionWeights_iff_min_variance {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (M : Model n Ω μ) (b : Fin n → ℝ) :
    (∀ d, Var[fun ω => M.aggregate ω - M.index b ω; μ] ≤
      Var[fun ω => M.aggregate ω - M.index d ω; μ]) ↔ b = M.regressionWeights := by
  constructor
  · intro h
    have hmin := h M.regressionWeights
    rw [M.error_variance_decomposition b] at hmin
    have hq : (b - M.regressionWeights) ⬝ᵥ
        (M.phenotypicCov *ᵥ (b - M.regressionWeights)) = 0 := by
      have hn := M.phenotypicCov_posDef.posSemidef.dotProduct_mulVec_nonneg
        (b - M.regressionWeights)
      simp only [star_trivial] at hn
      linarith
    have hz := M.phenotypicCov_posDef.posSemidef.dotProduct_mulVec_zero_iff.mp
      (show star (b - M.regressionWeights) ⬝ᵥ
        (M.phenotypicCov *ᵥ (b - M.regressionWeights)) = 0 by simpa using hq)
    have hb := M.phenotypicCov_posDef.mulVec_injective
      (show M.phenotypicCov *ᵥ (b - M.regressionWeights) = M.phenotypicCov *ᵥ 0 by
        simpa using hz)
    exact sub_eq_zero.mp hb
  · rintro rfl d
    rw [M.error_variance_decomposition d]
    have h := M.phenotypicCov_posDef.posSemidef.dotProduct_mulVec_nonneg
      (d - M.regressionWeights)
    simp only [star_trivial] at h
    linarith

private lemma Model.pearson_form {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) (b : Fin n → ℝ) :
    pearsonRatio μ (M.index b) M.aggregate =
      ((b ⬝ᵥ M.objectiveCov) / √(b ⬝ᵥ (M.phenotypicCov *ᵥ b))) /
        populationSD μ M.aggregate := by
  rw [pearsonRatio, covariance_index_aggregate]
  simp only [populationSD, variance_index, div_div]

private lemma Model.pearson_regression {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) (hc : M.objectiveCov ≠ 0) :
    pearsonRatio μ (M.index M.regressionWeights) M.aggregate =
      √(M.objectiveCov ⬝ᵥ M.regressionWeights) / populationSD μ M.aggregate := by
  rw [M.pearson_form, M.normal_weights, dotProduct_comm M.regressionWeights M.objectiveCov]
  have h := M.objective_pair_pos hc
  congr 1
  apply (div_eq_iff (Real.sqrt_pos.mpr h).ne').mpr
  exact (Real.mul_self_sqrt h.le).symm

private lemma Model.pearson_smul_pos {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) (b : Fin n → ℝ) {k : ℝ} (hk : 0 < k) :
    pearsonRatio μ (M.index (k • b)) M.aggregate =
      pearsonRatio μ (M.index b) M.aggregate := by
  have hi : M.index (k • b) = fun ω => k * M.index b ω := by
    funext ω
    exact smul_dotProduct k b (M.phenotype ω)
  rw [hi, pearsonRatio, pearsonRatio, covariance_const_mul_left]
  have hs : populationSD μ (fun ω => k * M.index b ω) =
      k * populationSD μ (M.index b) := by
    rw [populationSD, variance_const_mul, Real.sqrt_mul (sq_nonneg k), Real.sqrt_sq hk.le]
    rfl
  rw [hs]
  field_simp

private lemma Model.pearson_neg {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) (b : Fin n → ℝ) :
    pearsonRatio μ (M.index (-b)) M.aggregate = -pearsonRatio μ (M.index b) M.aggregate := by
  have hi : M.index (-b) = fun ω => -M.index b ω := by
    funext ω
    exact neg_dotProduct b (M.phenotype ω)
  rw [hi, pearsonRatio, pearsonRatio, covariance_fun_neg_left]
  simp only [populationSD, variance_fun_neg, neg_div]

/-- K1. Sharp upper bound for signed correlation. -/
theorem pearsonRatio_le {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) {b : Fin n → ℝ} (_hb : b ≠ 0)
    (_hH : 0 < Var[M.aggregate; μ]) (_hc : M.objectiveCov ≠ 0) :
    pearsonRatio μ (M.index b) M.aggregate ≤
      √(M.objectiveCov ⬝ᵥ M.regressionWeights) / populationSD μ M.aggregate := by
  have hq : 0 < b ⬝ᵥ (M.phenotypicCov *ᵥ b) := by
    simpa using M.phenotypicCov_posDef.dotProduct_mulVec_pos _hb
  have hQ := M.objective_pair_pos _hc
  have hcs := M.phenotypicCov_posDef.star_dotProduct_mulVec_mul_le b M.regressionWeights
  simp only [star_trivial, M.normal_weights,
    dotProduct_comm M.regressionWeights M.objectiveCov, ← pow_two] at hcs
  have hn : b ⬝ᵥ M.objectiveCov ≤
      √(b ⬝ᵥ (M.phenotypicCov *ᵥ b)) * √(M.objectiveCov ⬝ᵥ M.regressionWeights) := by
    apply le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    simpa only [mul_pow, Real.sq_sqrt hq.le, Real.sq_sqrt hQ.le] using hcs
  rw [M.pearson_form]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact (div_le_iff₀ (Real.sqrt_pos.mpr hq)).mpr (by simpa only [mul_comm] using hn)

/-- K1. Equality in the signed upper bound holds exactly on the positive regression ray. -/
theorem pearsonRatio_eq_upper_iff {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) {b : Fin n → ℝ} (_hb : b ≠ 0)
    (_hH : 0 < Var[M.aggregate; μ]) (_hc : M.objectiveCov ≠ 0) :
    pearsonRatio μ (M.index b) M.aggregate =
      √(M.objectiveCov ⬝ᵥ M.regressionWeights) / populationSD μ M.aggregate ↔
      ∃ k : ℝ, 0 < k ∧ b = k • M.regressionWeights := by
  have hq : 0 < b ⬝ᵥ (M.phenotypicCov *ᵥ b) := by
    simpa using M.phenotypicCov_posDef.dotProduct_mulVec_pos _hb
  have hQ := M.objective_pair_pos _hc
  have hsQ := Real.sqrt_pos.mpr hQ
  have hsq := Real.sqrt_pos.mpr hq
  constructor
  · intro h
    rw [M.pearson_form] at h
    have ht : b ⬝ᵥ M.objectiveCov =
        √(b ⬝ᵥ (M.phenotypicCov *ᵥ b)) * √(M.objectiveCov ⬝ᵥ M.regressionWeights) := by
      have hn := (div_left_inj' (Real.sqrt_pos.mpr _hH).ne').mp h
      have := (div_eq_iff hsq.ne').mp hn
      simpa only [mul_comm] using this
    let k := √(b ⬝ᵥ (M.phenotypicCov *ᵥ b)) / √(M.objectiveCov ⬝ᵥ M.regressionWeights)
    have hk : 0 < k := div_pos hsq hsQ
    have hkQ : k ^ 2 * (M.objectiveCov ⬝ᵥ M.regressionWeights) =
        b ⬝ᵥ (M.phenotypicCov *ᵥ b) := by
      dsimp [k]
      rw [div_pow, Real.sq_sqrt hq.le, Real.sq_sqrt hQ.le,
        div_mul_cancel₀ _ hQ.ne']
    have hkt : k * (b ⬝ᵥ M.objectiveCov) = b ⬝ᵥ (M.phenotypicCov *ᵥ b) := by
      dsimp [k]
      rw [ht]
      field_simp
      nlinarith [Real.sq_sqrt hq.le]
    have hz : (b - k • M.regressionWeights) ⬝ᵥ
        (M.phenotypicCov *ᵥ (b - k • M.regressionWeights)) = 0 := by
      rw [M.quadratic_sub_weights, hkQ]
      nlinarith [hkt]
    have heq : b - k • M.regressionWeights = 0 := by
      apply M.phenotypicCov_posDef.mulVec_injective
      have hz' := M.phenotypicCov_posDef.posSemidef.dotProduct_mulVec_zero_iff.mp
        (show star (b - k • M.regressionWeights) ⬝ᵥ
          (M.phenotypicCov *ᵥ (b - k • M.regressionWeights)) = 0 by simpa using hz)
      simpa using hz'
    exact ⟨k, hk, sub_eq_zero.mp heq⟩
  · rintro ⟨k, hk, rfl⟩
    rw [M.pearson_smul_pos _ hk, M.pearson_regression _hc]

/-- K1. Sharp lower bound for signed correlation. -/
theorem lower_le_pearsonRatio {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) {b : Fin n → ℝ} (_hb : b ≠ 0)
    (_hH : 0 < Var[M.aggregate; μ]) (_hc : M.objectiveCov ≠ 0) :
    -(√(M.objectiveCov ⬝ᵥ M.regressionWeights) / populationSD μ M.aggregate) ≤
      pearsonRatio μ (M.index b) M.aggregate := by
  have h := pearsonRatio_le M (neg_ne_zero.mpr _hb) _hH _hc
  rw [M.pearson_neg] at h
  linarith

/-- K1. Equality in the signed lower bound holds exactly on the negative regression ray. -/
theorem pearsonRatio_eq_lower_iff {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) {b : Fin n → ℝ} (_hb : b ≠ 0)
    (_hH : 0 < Var[M.aggregate; μ]) (_hc : M.objectiveCov ≠ 0) :
    pearsonRatio μ (M.index b) M.aggregate =
      -(√(M.objectiveCov ⬝ᵥ M.regressionWeights) / populationSD μ M.aggregate) ↔
      ∃ k : ℝ, k < 0 ∧ b = k • M.regressionWeights := by
  have h := pearsonRatio_eq_upper_iff M (neg_ne_zero.mpr _hb) _hH _hc
  rw [M.pearson_neg] at h
  constructor
  · intro heq
    obtain ⟨k, hk, hb⟩ := h.mp (by linarith)
    refine ⟨-k, by linarith, ?_⟩
    simpa using congrArg Neg.neg hb
  · rintro ⟨k, hk, hb⟩
    have hn : -b = (-k) • M.regressionWeights := by simp [hb]
    have heq := h.mpr ⟨-k, by linarith, hn⟩
    linarith

/-- K1. Sharp upper bound for squared correlation. -/
theorem pearsonRatio_sq_le {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) {b : Fin n → ℝ} (_hb : b ≠ 0)
    (_hH : 0 < Var[M.aggregate; μ]) (_hc : M.objectiveCov ≠ 0) :
    pearsonRatio μ (M.index b) M.aggregate ^ 2 ≤
      (M.objectiveCov ⬝ᵥ M.regressionWeights) / Var[M.aggregate; μ] := by
  have hu := pearsonRatio_le M _hb _hH _hc
  have hl := lower_le_pearsonRatio M _hb _hH _hc
  have hQ := M.objective_pair_pos _hc
  have hbound : (√(M.objectiveCov ⬝ᵥ M.regressionWeights) /
      populationSD μ M.aggregate) ^ 2 =
      (M.objectiveCov ⬝ᵥ M.regressionWeights) / Var[M.aggregate; μ] := by
    rw [div_pow, Real.sq_sqrt hQ.le, populationSD, Real.sq_sqrt _hH.le]
  rw [← hbound]
  nlinarith

/-- K1. Squared correlation attains its bound on both nonzero regression rays. -/
theorem pearsonRatio_sq_eq_upper_iff {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) {b : Fin n → ℝ} (_hb : b ≠ 0)
    (_hH : 0 < Var[M.aggregate; μ]) (_hc : M.objectiveCov ≠ 0) :
    pearsonRatio μ (M.index b) M.aggregate ^ 2 =
      (M.objectiveCov ⬝ᵥ M.regressionWeights) / Var[M.aggregate; μ] ↔
      ∃ k : ℝ, k ≠ 0 ∧ b = k • M.regressionWeights := by
  have hQ := M.objective_pair_pos _hc
  have hbound : (√(M.objectiveCov ⬝ᵥ M.regressionWeights) /
      populationSD μ M.aggregate) ^ 2 =
      (M.objectiveCov ⬝ᵥ M.regressionWeights) / Var[M.aggregate; μ] := by
    rw [div_pow, Real.sq_sqrt hQ.le, populationSD, Real.sq_sqrt _hH.le]
  rw [← hbound, sq_eq_sq_iff_eq_or_eq_neg,
    pearsonRatio_eq_upper_iff M _hb _hH _hc, pearsonRatio_eq_lower_iff M _hb _hH _hc]
  constructor
  · rintro (⟨k, hk, hb⟩ | ⟨k, hk, hb⟩)
    · exact ⟨k, hk.ne', hb⟩
    · exact ⟨k, hk.ne, hb⟩
  · rintro ⟨k, hk, hb⟩
    rcases lt_or_gt_of_ne hk with h | h
    · exact Or.inr ⟨k, h, hb⟩
    · exact Or.inl ⟨k, h, hb⟩

private lemma Model.canonical_sum {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) (hH : 0 < Var[M.aggregate; μ]) :
    (∑ i, M.beta i * pearsonRatio μ (fun ω => M.phenotype ω i) M.aggregate) =
      (M.objectiveCov ⬝ᵥ M.regressionWeights) / Var[M.aggregate; μ] := by
  calc
    _ = ∑ i, (M.objectiveCov i * M.regressionWeights i) /
        populationSD μ M.aggregate ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      unfold Model.beta pearsonRatio
      change M.regressionWeights i * populationSD μ (fun ω => M.phenotype ω i) /
          populationSD μ M.aggregate *
        (M.objectiveCov i / (populationSD μ (fun ω => M.phenotype ω i) *
          populationSD μ M.aggregate)) = _
      field_simp [(M.sd_phenotype_pos i).ne', (Real.sqrt_pos.mpr hH).ne']
    _ = (M.objectiveCov ⬝ᵥ M.regressionWeights) / populationSD μ M.aggregate ^ 2 := by
      rw [← Finset.sum_div]
      rfl
    _ = _ := by rw [populationSD, Real.sq_sqrt hH.le]

/-- K2. Hazel's p. 486 identity for the canonical regression index. -/
theorem pearsonRatio_sq_regressionWeights_eq_sum {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (M : Model n Ω μ)
    (_hH : 0 < Var[M.aggregate; μ]) (_hc : M.objectiveCov ≠ 0) :
    pearsonRatio μ (M.index M.regressionWeights) M.aggregate ^ 2 =
      ∑ i, M.beta i * pearsonRatio μ (fun ω => M.phenotype ω i) M.aggregate := by
  rw [M.pearson_regression _hc, M.canonical_sum _hH, div_pow,
    Real.sq_sqrt (M.objective_pair_pos _hc).le, populationSD, Real.sq_sqrt _hH.le]

/-- K2. The signed canonical correlation is the positive square root of Hazel's p. 486 sum. -/
theorem pearsonRatio_regressionWeights_eq_sqrt_sum {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (M : Model n Ω μ)
    (_hH : 0 < Var[M.aggregate; μ]) (_hc : M.objectiveCov ≠ 0) :
    pearsonRatio μ (M.index M.regressionWeights) M.aggregate =
      √(∑ i, M.beta i * pearsonRatio μ (fun ω => M.phenotype ω i) M.aggregate) := by
  rw [← pearsonRatio_sq_regressionWeights_eq_sum M _hH _hc]
  symm
  apply Real.sqrt_sq
  rw [M.pearson_regression _hc]
  exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- K2. The canonical sum in finite matrix form. -/
theorem sum_beta_mul_pearsonRatio {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ) (_hH : 0 < Var[M.aggregate; μ]) :
    (∑ i, M.beta i * pearsonRatio μ (fun ω => M.phenotype ω i) M.aggregate) =
      (M.objectiveCov ⬝ᵥ M.regressionWeights) / Var[M.aggregate; μ] := by
  exact M.canonical_sum _hH

/-- K4. With both covariance matrices diagonal, the canonical coefficient is aᵢhᵢ². -/
theorem regressionWeights_eq_economic_mul_heritability {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (M : Model n Ω μ)
    (_hP : ∀ i j, i ≠ j → M.phenotypicCov i j = 0)
    (_hG : ∀ i j, i ≠ j → M.geneticCov i j = 0) (i : Fin n) :
    M.regressionWeights i = M.economic i * M.heritability i := by
  classical
  have hPsum : (∑ j, M.phenotypicCov i j * M.regressionWeights j) =
      M.phenotypicCov i i * M.regressionWeights i := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [_hP i j hji.symm, zero_mul]
    · simp
  have hGsum : (∑ j, M.geneticCov i j * M.economic j) =
      M.geneticCov i i * M.economic i := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [_hG i j hji.symm, zero_mul]
    · simp
  have h := congrFun M.normal_weights i
  rw [objectiveCov_eq_geneticCov_mulVec M] at h
  change (∑ j, M.phenotypicCov i j * M.regressionWeights j) =
    ∑ j, M.geneticCov i j * M.economic j at h
  rw [hPsum, hGsum] at h
  unfold Model.heritability
  field_simp [M.phenotypicCov_posDef.diag_pos.ne']
  nlinarith [h]

/-- K4. In the diagonal case all signed maximizers are positive multiples of aᵢhᵢ². -/
theorem diagonal_pearsonRatio_max_iff {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (M : Model n Ω μ)
    (_hP : ∀ i j, i ≠ j → M.phenotypicCov i j = 0)
    (_hG : ∀ i j, i ≠ j → M.geneticCov i j = 0) {b : Fin n → ℝ} (_hb : b ≠ 0)
    (_hH : 0 < Var[M.aggregate; μ]) (_hc : M.objectiveCov ≠ 0) :
    (∀ d : Fin n → ℝ, d ≠ 0 →
      pearsonRatio μ (M.index d) M.aggregate ≤ pearsonRatio μ (M.index b) M.aggregate) ↔
      ∃ k : ℝ, 0 < k ∧ b = k • (fun i => M.economic i * M.heritability i) := by
  have hw : M.regressionWeights = (fun i => M.economic i * M.heritability i) := by
    funext i
    exact regressionWeights_eq_economic_mul_heritability M _hP _hG i
  rw [← hw, ← pearsonRatio_eq_upper_iff M _hb _hH _hc]
  constructor
  · intro h
    have hmax := h M.regressionWeights (M.weights_ne_zero _hc)
    rw [M.pearson_regression _hc] at hmax
    exact le_antisymm (pearsonRatio_le M _hb _hH _hc) hmax
  · intro h d hd
    rw [h]
    exact pearsonRatio_le M hd _hH _hc

/-- B4. The aggregate and index are a linear image of the joint Gaussian breeding values
and residuals. -/
theorem hasGaussianLaw_aggregate_index {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (M : Model n Ω μ)
    (_hAE : HasGaussianLaw (fun ω => (M.additive ω, M.residual ω)) μ) (b : Fin n → ℝ) :
    HasGaussianLaw (fun ω => (M.aggregate ω, M.index b ω)) μ := by
  let a : (Fin n → ℝ) →L[ℝ] ℝ :=
    ∑ i, M.economic i • ContinuousLinearMap.proj i
  let c : (Fin n → ℝ) →L[ℝ] ℝ :=
    ∑ i, b i • ContinuousLinearMap.proj i
  let p := ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ)
  let q := ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ)
  simpa [a, c, p, q, Model.aggregate, Model.index, Model.phenotype,
    dotProduct, _root_.sum_apply, mul_add, Finset.sum_add_distrib] using
    _hAE.map_fun ((a.comp p).prod (c.comp (p + q)))

/-- K5. Standardizing a nonconstant Gaussian score gives the standard normal law. -/
theorem hasLaw_standardizedValue {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (_hf : HasGaussianLaw f μ) (_hvar : 0 < Var[f; μ]) :
    HasLaw (standardizedValue μ f) (gaussianReal 0 1) μ := by
  have hv : (Var[f; μ].toNNReal : ℝ) = Var[f; μ] :=
    Real.coe_toNNReal _ _hvar.le
  have hne : Var[f; μ].toNNReal ≠ 0 := by
    intro h
    have hzero := congrArg (fun x : NNReal => (x : ℝ)) h
    rw [hv] at hzero
    exact _hvar.ne' hzero
  have hsq : ∀ h : 0 ≤ populationSD μ f ^ 2,
      NNReal.mk (populationSD μ f ^ 2) h = Var[f; μ].toNNReal := by
    intro h
    apply Subtype.ext
    exact (Real.sq_sqrt _hvar.le).trans hv.symm
  have hsub : Measurable (fun y : ℝ => y - μ[f]) := measurable_id.sub_const _
  have hdiv : Measurable (fun y : ℝ => y / populationSD μ f) :=
    measurable_id.div_const _
  have hg : HasLaw (fun y : ℝ => (y - μ[f]) / populationSD μ f)
      (gaussianReal 0 1) (gaussianReal μ[f] Var[f; μ].toNNReal) := by
    refine ⟨((measurable_id.sub_const _).div_const _).aemeasurable, ?_⟩
    rw [show (fun y : ℝ => (y - μ[f]) / populationSD μ f) =
        (fun y : ℝ => y / populationSD μ f) ∘ (fun y : ℝ => y - μ[f]) from rfl,
      ← Measure.map_map hdiv hsub,
      gaussianReal_map_sub_const, gaussianReal_map_div_const,
      sub_self, zero_div, hsq _, div_self hne]
  exact hg.fun_comp ⟨_hf.aemeasurable, _hf.map_eq_gaussianReal⟩

/-- K5. The selected proportion is the standard-normal upper tail at z, for every index. -/
theorem measureReal_standardizedUpperEvent {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (_hf : HasGaussianLaw f μ)
    (_hvar : 0 < Var[f; μ]) (z : ℝ) :
    μ.real (standardizedUpperEvent μ f z) = cdf (gaussianReal 0 1) (-z) := by
  have hsd : 0 < populationSD μ f := Real.sqrt_pos.mpr _hvar
  have hevent : standardizedUpperEvent μ f z =
      {ω | -(-z) ≤ standardizedValue μ f ω} := by
    ext ω
    simp only [standardizedUpperEvent, Set.mem_ofPred_eq, standardizedValue, neg_neg]
    rw [le_div_iff₀ hsd]
    constructor <;> intro h <;> linarith
  rw [hevent]
  exact MathlibExt.Probability.Causality.MissingData.measureReal_selection_eq_cdf
    (hasLaw_standardizedValue _hf _hvar)

/-- K5. Every finite standardized threshold selects a strictly intermediate proportion. -/
theorem gaussianUpperTail_mem_Ioo (z : ℝ) :
    cdf (gaussianReal 0 1) (-z) ∈ Set.Ioo (0 : ℝ) 1 := by
  have hpos : ∀ x : ℝ, 0 < cdf (gaussianReal 0 1) x := by
    intro x
    exact (cdf_nonneg (gaussianReal 0 1) (x - 1)).trans_lt
      (strictMono_cdf_gaussianReal 0 one_ne_zero (by linarith : x - 1 < x))
  refine ⟨hpos (-z), ?_⟩
  rw [cdf_gaussianReal_neg]
  linarith [hpos z]

/-- K5. The standardized selection differential is the actual selected mean of the
standardized index. -/
theorem integral_cond_standardizedValue {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (_hfmeas : Measurable f)
    (_hf : HasGaussianLaw f μ) (_hvar : 0 < Var[f; μ]) (z : ℝ) :
    (∫ ω, standardizedValue μ f ω ∂μ[|standardizedUpperEvent μ f z]) =
      inverseMillsRatio (-z) := by
  have hsd : 0 < populationSD μ f := Real.sqrt_pos.mpr _hvar
  have hevent : standardizedUpperEvent μ f z =
      {ω | -(-z) ≤ standardizedValue μ f ω} := by
    ext ω
    simp only [standardizedUpperEvent, Set.mem_ofPred_eq, standardizedValue, neg_neg]
    rw [le_div_iff₀ hsd]
    constructor <;> intro h <;> linarith
  rw [hevent]
  exact MathlibExt.Probability.Causality.MissingData.integral_cond_selectionError_eq
    (hasLaw_standardizedValue _hf _hvar) ((_hfmeas.sub_const _).div_const _)

/-- K5. In upper-tail notation the intensity is φ(z)/Q(z). -/
theorem inverseMillsRatio_neg_eq_pdf_div_upperTail (z : ℝ) :
    inverseMillsRatio (-z) = gaussianPDFReal 0 1 z / cdf (gaussianReal 0 1) (-z) := by
  simp [inverseMillsRatio, gaussianPDFReal_def]

/-- K5. The scalar Gaussian response, with its left side an actual conditional mean shift. -/
theorem conditionalMeanShift_standardizedUpperEvent_gaussian {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {H I : Ω → ℝ} (_hI : Measurable I)
    (_hHI : HasGaussianLaw (fun ω => (H ω, I ω)) μ) (_hvar : 0 < Var[I; μ]) (z : ℝ) :
    conditionalMeanShift μ H (standardizedUpperEvent μ I z) =
      inverseMillsRatio (-z) * (cov[I, H; μ] / populationSD μ I) := by
  classical
  let β : ℝ := cov[I, H; μ] / Var[I; μ]
  let R : Ω → ℝ := fun ω => H ω - β * I ω
  let s := standardizedUpperEvent μ I z
  have hIR : HasGaussianLaw (fun ω => (I ω, R ω)) μ := by
    let p := ContinuousLinearMap.fst ℝ ℝ ℝ
    let q := ContinuousLinearMap.snd ℝ ℝ ℝ
    exact _hHI.map_fun (q.prod (p - β • q))
  have hcov : cov[I, R; μ] = 0 := by
    dsimp [R]
    rw [covariance_fun_sub_right _hHI.snd.memLp_two _hHI.fst.memLp_two
      (_hHI.snd.memLp_two.const_mul β), covariance_const_mul_right,
      covariance_self _hHI.snd.aemeasurable]
    dsimp [β]
    field_simp
    ring
  have hind : IndepFun I R μ := by
    rw [indepFun_iff_map_prod_eq_prod_map_map hIR.fst.aemeasurable hIR.snd.aemeasurable]
    apply Measure.ext_of_charFunDual
    funext L
    rw [charFunDual_prod]
    have hlinear : ∀ (l : ℝ →L[ℝ] ℝ) (x : ℝ), l x = l 1 * x := by
      intro l x
      have h := l.map_smul x (1 : ℝ)
      simpa only [smul_eq_mul, mul_one, mul_comm] using h
    have hz : ∀ (l₁ l₂ : ℝ →L[ℝ] ℝ),
        cov[l₁ ∘ I, l₂ ∘ R; μ] = 0 := by
      intro l₁ l₂
      have h₁ : l₁ ∘ I = fun ω => l₁ 1 * I ω := by
        funext ω
        exact hlinear l₁ (I ω)
      have h₂ : l₂ ∘ R = fun ω => l₂ 1 * R ω := by
        funext ω
        exact hlinear l₂ (R ω)
      rw [h₁, h₂, covariance_const_mul_left, covariance_const_mul_right,
        hcov, mul_zero, mul_zero]
    have heq : L ∘ (fun ω => (I ω, R ω)) =
        (L.comp (.inl ℝ ℝ ℝ)) ∘ I + (L.comp (.inr ℝ ℝ ℝ)) ∘ R := by
      ext ω
      change L (I ω, R ω) = L (I ω, 0) + L (0, R ω)
      rw [← map_add]
      simp
    rw [hIR.charFunDual_map_eq, hIR.fst.charFunDual_map_eq,
      hIR.snd.charFunDual_map_eq, ← Complex.exp_add, sub_add_sub_comm,
      ← add_mul, ← Complex.ofReal_add, ← integral_add, ← add_div,
      ← Complex.ofReal_add, heq, variance_add, hz, mul_zero, add_zero]
    · simp
    · exact (hIR.fst.map _).memLp_two
    · exact (hIR.snd.map _).memLp_two
    · exact (hIR.fst.map _).integrable
    · exact (hIR.snd.map _).integrable
  have hs : MeasurableSet s := measurableSet_le measurable_const _hI
  have hpos : 0 < μ.real s := by
    rw [measureReal_standardizedUpperEvent _hHI.snd _hvar]
    exact (gaussianUpperTail_mem_Ioo z).1
  have hμpos : 0 < μ s := (ENNReal.toReal_pos_iff.mp hpos).1
  have hne : μ s ≠ 0 := hμpos.ne'
  have : IsProbabilityMeasure μ[|s] := cond_isProbabilityMeasure hne
  have hH : Integrable H μ[|s] :=
    _hHI.fst.integrable.restrict.smul_measure (ENNReal.inv_ne_top.mpr hne)
  have hI : Integrable I μ[|s] :=
    _hHI.snd.integrable.restrict.smul_measure (ENNReal.inv_ne_top.mpr hne)
  have hR : conditionalMeanShift μ R s = 0 := by
    let t := Set.Ici (μ[I] + z * populationSD μ I)
    have ht : MeasurableSet t := measurableSet_Ici
    have hf : AEStronglyMeasurable (t.indicator (fun _ : ℝ => (1 : ℝ)))
        (μ.map I) := (measurable_const.indicator ht).aestronglyMeasurable
    have hg : AEStronglyMeasurable (id : ℝ → ℝ) (μ.map R) :=
      measurable_id.aestronglyMeasurable
    have hfac := hind.integral_fun_comp_mul_comp hIR.fst.aemeasurable
      hIR.snd.aemeasurable hf hg
    have hfun : (fun ω => t.indicator (fun _ => (1 : ℝ)) (I ω)) =
        s.indicator (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases h : ω ∈ s <;> simp [t, s, standardizedUpperEvent] at h ⊢ <;> simp [h]
    change (∫ ω, t.indicator (fun _ => (1 : ℝ)) (I ω) * R ω ∂μ) =
      (∫ ω, t.indicator (fun _ => (1 : ℝ)) (I ω) ∂μ) * μ[R] at hfac
    have hmul : (fun ω => t.indicator (fun _ => (1 : ℝ)) (I ω) * R ω) =
        fun ω => s.indicator (fun _ => (1 : ℝ)) ω * R ω := by
      funext ω
      rw [← hfun]
    rw [hmul, hfun] at hfac
    rw [conditionalMeanShift_eq_indicator_quotient hs hμpos, hfac]
    have hden : (∫ ω, s.indicator (fun _ => (1 : ℝ)) ω ∂μ) ≠ 0 := by
      simpa [integral_indicator hs, setIntegral_const] using hpos.ne'
    field_simp
    ring
  have hstd := integral_cond_standardizedValue _hI _hHI.snd _hvar z
  change (∫ ω, (I ω - μ[I]) / populationSD μ I ∂μ[|s]) =
    inverseMillsRatio (-z) at hstd
  rw [integral_div, integral_sub hI (integrable_const _)] at hstd
  simp only [integral_const] at hstd
  simp only [Measure.real_def, measure_univ, ENNReal.toReal_one, one_smul] at hstd
  change (∫ ω, H ω - β * I ω ∂μ[|s]) -
    (∫ ω, H ω - β * I ω ∂μ) = 0 at hR
  rw [integral_sub hH (hI.const_mul β), integral_const_mul,
    integral_sub _hHI.fst.integrable (_hHI.snd.integrable.const_mul β),
    integral_const_mul] at hR
  have hsd : populationSD μ I ≠ 0 := (Real.sqrt_pos.mpr _hvar).ne'
  have hsq : populationSD μ I ^ 2 = Var[I; μ] := Real.sq_sqrt _hvar.le
  unfold conditionalMeanShift
  change (∫ ω, H ω ∂μ[|s]) - μ[H] = _
  have hshift : (∫ ω, I ω ∂μ[|s]) - μ[I] =
      inverseMillsRatio (-z) * populationSD μ I := (div_eq_iff hsd).mp hstd
  calc
    _ = β * ((∫ ω, I ω ∂μ[|s]) - μ[I]) := by linarith
    _ = inverseMillsRatio (-z) * (cov[I, H; μ] / populationSD μ I) := by
      rw [hshift]
      dsimp [β]
      rw [← hsq]
      field_simp

/-- K5. Actual selected-group genetic gain in covariance form, including constant objectives. -/
theorem gain_eq_covariance {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ)
    (_hAE : HasGaussianLaw (fun ω => (M.additive ω, M.residual ω)) μ)
    {b : Fin n → ℝ} (_hb : b ≠ 0) (z : ℝ) :
    M.gain b z = inverseMillsRatio (-z) * (cov[M.index b, M.aggregate; μ] /
      populationSD μ (M.index b)) := by
  apply conditionalMeanShift_standardizedUpperEvent_gaussian
  · change Measurable (fun ω => ∑ i, b i * (M.additive ω i + M.residual ω i))
    exact Finset.measurable_sum _ fun i _ => measurable_const.mul
      (((measurable_pi_apply i).comp M.measurable_additive).add
        ((measurable_pi_apply i).comp M.measurable_residual))
  · exact hasGaussianLaw_aggregate_index M _hAE b
  · exact (variance_index_pos_iff M b).mpr _hb

/-- K5. Hazel's equation (3) on the domain of defined correlation. -/
theorem gain_eq_pearsonRatio {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ)
    (_hAE : HasGaussianLaw (fun ω => (M.additive ω, M.residual ω)) μ)
    {b : Fin n → ℝ} (_hb : b ≠ 0) (_hH : 0 < Var[M.aggregate; μ]) (z : ℝ) :
    M.gain b z = inverseMillsRatio (-z) * pearsonRatio μ (M.index b) M.aggregate *
      populationSD μ M.aggregate := by
  rw [gain_eq_covariance M _hAE _hb]
  unfold pearsonRatio
  have hsd : populationSD μ M.aggregate ≠ 0 := (Real.sqrt_pos.mpr _hH).ne'
  field_simp

/-- K0. A constant objective has zero actual gain for every nonzero Gaussian index. -/
theorem gain_eq_zero_of_variance_aggregate_eq_zero {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (M : Model n Ω μ)
    (_hAE : HasGaussianLaw (fun ω => (M.additive ω, M.residual ω)) μ)
    {b : Fin n → ℝ} (_hb : b ≠ 0) (_hH : Var[M.aggregate; μ] = 0) (z : ℝ) :
    M.gain b z = 0 := by
  rw [gain_eq_covariance M _hAE _hb, covariance_index_aggregate,
    (variance_aggregate_eq_zero_iff M).mp _hH]
  simp

/-- K6. Even without the additive decomposition, zero cross-covariance gives zero gain
for a jointly Gaussian objective and score. -/
theorem conditionalMeanShift_eq_zero_of_covariance_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {H I : Ω → ℝ} (_hI : Measurable I)
    (_hHI : HasGaussianLaw (fun ω => (H ω, I ω)) μ) (_hvar : 0 < Var[I; μ])
    (_hcov : cov[I, H; μ] = 0) (z : ℝ) :
    conditionalMeanShift μ H (standardizedUpperEvent μ I z) = 0 := by
  rw [conditionalMeanShift_standardizedUpperEvent_gaussian _hI _hHI _hvar]
  simp [_hcov]

/-- K6. A zero phenotype–objective covariance vector gives zero actual gain for all nonzero
Gaussian indices, including populations without the additive decomposition. -/
theorem conditionalMeanShift_linear_eq_zero_of_crossCovariance_eq_zero
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → Fin n → ℝ} {H : Ω → ℝ} (_hX : Measurable X)
    (_hXH : HasGaussianLaw (fun ω => (X ω, H ω)) μ)
    (_hP : Matrix.PosDef (fun i j => cov[fun ω => X ω i, fun ω => X ω j; μ] :
      Matrix (Fin n) (Fin n) ℝ))
    (_hc : ∀ i, cov[fun ω => X ω i, H; μ] = 0) {b : Fin n → ℝ} (_hb : b ≠ 0) (z : ℝ) :
    conditionalMeanShift μ H (standardizedUpperEvent μ (fun ω => b ⬝ᵥ X ω) z) = 0 := by
  let c : (Fin n → ℝ) →L[ℝ] ℝ :=
    ∑ i, b i • ContinuousLinearMap.proj i
  let p := ContinuousLinearMap.fst ℝ (Fin n → ℝ) ℝ
  let q := ContinuousLinearMap.snd ℝ (Fin n → ℝ) ℝ
  have hHI : HasGaussianLaw (fun ω => (H ω, b ⬝ᵥ X ω)) μ := by
    simpa [c, p, q, dotProduct, _root_.sum_apply] using
      _hXH.map_fun (q.prod (c.comp p))
  have hXm : ∀ i, MemLp (fun ω => X ω i) 2 μ := fun i =>
    (_hXH.fst.eval i).memLp_two
  apply conditionalMeanShift_eq_zero_of_covariance_eq_zero
  · change Measurable (fun ω => ∑ i, b i * X ω i)
    exact Finset.measurable_sum _ fun i _ =>
      measurable_const.mul ((measurable_pi_apply i).comp _hX)
  · exact hHI
  · rw [← covariance_self hHI.snd.aemeasurable,
      covariance_linear_linear hXm hXm]
    exact _hP.dotProduct_mulVec_pos _hb
  · rw [covariance_linear_left hXm _hXH.snd.memLp_two]
    simp [_hc]

/-- K6. The actual upper-tail gain at fixed z is maximized exactly by the positive ray. -/
theorem gain_max_iff {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ)
    (_hAE : HasGaussianLaw (fun ω => (M.additive ω, M.residual ω)) μ)
    {b : Fin n → ℝ} (_hb : b ≠ 0) (_hH : 0 < Var[M.aggregate; μ])
    (_hc : M.objectiveCov ≠ 0) (z : ℝ) :
    (∀ d : Fin n → ℝ, d ≠ 0 → M.gain d z ≤ M.gain b z) ↔
      ∃ k : ℝ, 0 < k ∧ b = k • M.regressionWeights := by
  have hi := MathlibExt.Probability.Causality.MissingData.inverseMillsRatio_pos (-z)
  have hs : 0 < populationSD μ M.aggregate := Real.sqrt_pos.mpr _hH
  have horder : ∀ d, d ≠ 0 → (M.gain d z ≤ M.gain b z ↔
      pearsonRatio μ (M.index d) M.aggregate ≤ pearsonRatio μ (M.index b) M.aggregate) := by
    intro d hd
    rw [gain_eq_pearsonRatio M _hAE hd _hH, gain_eq_pearsonRatio M _hAE _hb _hH,
      mul_le_mul_iff_left₀ hs, mul_le_mul_iff_right₀ hi]
  rw [← pearsonRatio_eq_upper_iff M _hb _hH _hc]
  constructor
  · intro h
    have hmax := (horder M.regressionWeights (M.weights_ne_zero _hc)).mp
      (h M.regressionWeights (M.weights_ne_zero _hc))
    rw [M.pearson_regression _hc] at hmax
    exact le_antisymm (pearsonRatio_le M _hb _hH _hc) hmax
  · intro h d hd
    apply (horder d hd).mpr
    rw [h]
    exact pearsonRatio_le M hd _hH _hc

/-- K6. The actual upper-tail gain at fixed z is minimized exactly by the negative ray. -/
theorem gain_min_iff {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (M : Model n Ω μ)
    (_hAE : HasGaussianLaw (fun ω => (M.additive ω, M.residual ω)) μ)
    {b : Fin n → ℝ} (_hb : b ≠ 0) (_hH : 0 < Var[M.aggregate; μ])
    (_hc : M.objectiveCov ≠ 0) (z : ℝ) :
    (∀ d : Fin n → ℝ, d ≠ 0 → M.gain b z ≤ M.gain d z) ↔
      ∃ k : ℝ, k < 0 ∧ b = k • M.regressionWeights := by
  have hi := MathlibExt.Probability.Causality.MissingData.inverseMillsRatio_pos (-z)
  have hs : 0 < populationSD μ M.aggregate := Real.sqrt_pos.mpr _hH
  have horder : ∀ d, d ≠ 0 → (M.gain b z ≤ M.gain d z ↔
      pearsonRatio μ (M.index b) M.aggregate ≤ pearsonRatio μ (M.index d) M.aggregate) := by
    intro d hd
    rw [gain_eq_pearsonRatio M _hAE _hb _hH, gain_eq_pearsonRatio M _hAE hd _hH,
      mul_le_mul_iff_left₀ hs, mul_le_mul_iff_right₀ hi]
  rw [← pearsonRatio_eq_lower_iff M _hb _hH _hc]
  constructor
  · intro h
    have hn : -M.regressionWeights ≠ 0 := neg_ne_zero.mpr (M.weights_ne_zero _hc)
    have hmin := (horder (-M.regressionWeights) hn).mp (h (-M.regressionWeights) hn)
    rw [M.pearson_neg, M.pearson_regression _hc] at hmin
    exact le_antisymm hmin (lower_le_pearsonRatio M _hb _hH _hc)
  · intro h d hd
    apply (horder d hd).mpr
    rw [h]
    exact lower_le_pearsonRatio M hd _hH _hc

end SmithHazel
