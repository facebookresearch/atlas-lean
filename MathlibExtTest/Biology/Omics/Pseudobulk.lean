/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Omics.Pseudobulk

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open MathlibExt.Biology.Omics.Pseudobulk

namespace MathlibExtTest.Biology.Omics.Pseudobulk

/-! ### API-00 smoke test: the public surface elaborates -/

#check @riCov
#check @IsRandomIntercept
#check @cellMean
#check @pseudobulk
#check @pseudobulkMean
#check @trueVar
#check @naiveVar
#check @riModel
#check @stdGaussianPi
#check @dataLaw

example : riCov (δ := Fin 1) (κ := Fin 1) 2 3 (0, 0) (0, 0) = 5 := by norm_num [riCov]

/-! ### Kernel entries, from the definition -/

/-- Same donor, distinct cells: covariance `σ_b²`. -/
example : riCov (δ := Fin 2) (κ := Fin 3) (1 : ℝ) 1 (0, 0) (0, 1) = 1 := by simp [riCov]

/-- Different donors: uncorrelated. -/
example : riCov (δ := Fin 2) (κ := Fin 3) (1 : ℝ) 1 (0, 0) (1, 0) = 0 := by simp [riCov]

/-- Same cell: `σ_b² + σ_e²`. -/
example : riCov (δ := Fin 2) (κ := Fin 3) (1 : ℝ) 1 (1, 2) (1, 2) = 2 := by
  norm_num [riCov]

/-! ### `D = 2`, `m = 3`, `σ_b² = σ_e² = 1`: the variance decomposition by brute force

The double sum of the kernel over all `6 × 6` cell pairs is computed directly from `riCov`, not
through `sum_riCov_right` or `variance_cellMean`. -/

theorem sum_sum_riCov_two_three :
    ∑ i : Fin 2 × Fin 3, ∑ j : Fin 2 × Fin 3, riCov (1 : ℝ) 1 i j = 24 := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_succ, Fin.sum_univ_zero, riCov]
  norm_num

/-- `Var[Ȳ] = (∑ᵢⱼ Σᵢⱼ) / (D m)² = 24 / 36 = 2 / 3`, which is `trueVar 1 1 2 3`. -/
example : (24 : ℝ) / (2 * 3) ^ 2 = trueVar 1 1 2 3 := by norm_num [trueVar]

theorem trueVar_one_one_two_three : trueVar 1 1 2 3 = 2 / 3 := by norm_num [trueVar]

/-- Naive independent-cell variance `2 / 6 = 1 / 3`: half the true value. -/
theorem naiveVar_one_one_two_three : naiveVar 1 1 2 3 = 1 / 3 := by norm_num [naiveVar]

example : naiveVar 1 1 2 3 < trueVar 1 1 2 3 := by
  rw [naiveVar_one_one_two_three, trueVar_one_one_two_three]; norm_num

/-- Shortfall `σ_b² (m - 1) / (D m) = 2 / 6`, computed directly. -/
example : trueVar 1 1 2 3 - naiveVar 1 1 2 3 = 1 * ((3 : ℕ) - 1 : ℝ) / ((2 : ℕ) * (3 : ℕ)) := by
  norm_num [trueVar, naiveVar]

/-- Intraclass correlation `1 / 2` and design effect `1 + 2 · (1 / 2) = 2`. -/
example : icc 1 1 = 1 / 2 := by norm_num [icc]

example : (1 + ((3 : ℕ) - 1 : ℝ) * icc 1 1) * naiveVar 1 1 2 3 = trueVar 1 1 2 3 := by
  norm_num [icc, naiveVar, trueVar]

/-- The library statement agrees with the brute-force numbers. -/
example : trueVar 1 1 2 3 = (1 + ((3 : ℕ) - 1 : ℝ) * icc 1 1) * naiveVar 1 1 2 3 :=
  trueVar_eq_designEffect_mul_naiveVar (by norm_num) (by norm_num) (by norm_num)

/-! ### Pseudobulk second moments by brute force -/

/-- One donor's pseudobulk variance: `(∑_{c c'} Σ) / m² = 12 / 9 = σ_b² + σ_e² / m = 4 / 3`. -/
example : (∑ c : Fin 3, ∑ c' : Fin 3, riCov (δ := Fin 2) (1 : ℝ) 1 (0, c) (0, c')) / 3 ^ 2
    = 1 + 1 / 3 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, riCov]
  norm_num

/-- Distinct donors' pseudobulk values are uncorrelated. -/
example : (∑ c : Fin 3, ∑ c' : Fin 3, riCov (δ := Fin 2) (1 : ℝ) 1 (0, c) (1, c')) / 3 ^ 2 = 0 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, riCov]
  norm_num

/-- The replicate formula `(σ_b² + σ_e² / m) / D` gives the true cell-mean variance. -/
example : (1 + 1 / 3 : ℝ) / 2 = trueVar 1 1 2 3 := by norm_num [trueVar]

/-- `pseudobulkMean = cellMean` on a concrete deterministic table `Y (d, c) = 10 d + c`. -/
example :
    pseudobulkMean (fun (i : Fin 2 × Fin 3) (_ : Unit) ↦ (10 * (i.1 : ℕ) + (i.2 : ℕ) : ℝ)) ()
      = 6 ∧
    cellMean (fun (i : Fin 2 × Fin 3) (_ : Unit) ↦ (10 * (i.1 : ℕ) + (i.2 : ℕ) : ℝ)) () = 6 := by
  constructor <;>
  · simp only [pseudobulkMean, pseudobulk, cellMean, Fintype.sum_prod_type, Fin.sum_univ_succ,
      Fin.sum_univ_zero, Fintype.card_fin]
    norm_num

/-! ### Boundary cases of the naive formula, from the definitions -/

/-- One cell per donor (`m = 1`): naive and true agree. -/
example : naiveVar 1 1 2 1 = trueVar 1 1 2 1 := by norm_num [naiveVar, trueVar]

/-- No donor variance: naive and true agree. -/
example : naiveVar 0 1 2 3 = trueVar 0 1 2 3 := by norm_num [naiveVar, trueVar]

/-- Off the boundary they differ, matching `naiveVar_eq_trueVar_iff`. -/
example : naiveVar 1 1 2 3 ≠ trueVar 1 1 2 3 := by norm_num [naiveVar, trueVar]

example : ¬ (naiveVar 1 1 2 3 = trueVar 1 1 2 3) := by
  rw [naiveVar_eq_trueVar_iff 1 1 (by norm_num) (by norm_num)]; norm_num

/-- Same per-cell variance `2`, different donor splits `(1, 1)` versus `(0, 2)`: different
cell-mean variances. -/
example : trueVar 1 1 2 3 ≠ trueVar 0 2 2 3 := by norm_num [trueVar]

/-! ### Variance components must be nonnegative -/

/-- `Y₀ = Z`, `Y₁ = -Z` fits the kernel with coefficients `(-1, 2)`, but that is not a
random-intercept model: a donor variance of `-1` is rejected by the definition. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Y : Fin 1 × Fin 2 → Ω → ℝ) :
    ¬ IsRandomIntercept μ Y (-1) 2 :=
  fun h ↦ absurd h.donorVar_nonneg (by norm_num)

/-! ### The explicit Gaussian model, checked directly -/

/-- With `σ_e² = 0` two cells of donor `0` are the same coordinate `Z₀`; their covariance is
`Var[Z₀] = 1`, computed from `riModel` and the Gaussian law, not through
`isRandomIntercept_riModel`. -/
example :
    cov[riModel (δ := Fin 2) (κ := Fin 3) 1 0 (0, 0), riModel 1 0 (0, 1); stdGaussianPi _ _]
      = 1 := by
  have hf : ∀ c : Fin 3, riModel (δ := Fin 2) (κ := Fin 3) 1 0 (0, c)
      = fun ω ↦ ω (Sum.inl 0) := by
    intro c; funext ω; simp [riModel]
  rw [hf, hf, covariance_self (measurable_pi_apply _).aemeasurable]
  have := (measurePreserving_eval (fun _ : Fin 2 ⊕ Fin 2 × Fin 3 ↦ gaussianReal 0 1)
    (Sum.inl 0)).variance_fun_comp (f := id) aemeasurable_id
  simpa [stdGaussianPi, variance_id_gaussianReal] using this

/-- The library model, specialised: `Var[Ȳ] = 2 / 3 > 1 / 3`. -/
example :
    Var[cellMean (riModel (δ := Fin 2) (κ := Fin 3) 1 1); stdGaussianPi _ _] = 2 / 3 ∧
      naiveVar 1 1 2 3
        < Var[cellMean (riModel (δ := Fin 2) (κ := Fin 3) 1 1); stdGaussianPi _ _] := by
  obtain ⟨-, hv, hlt⟩ :=
    pseudoreplication_counterexample (δ := Fin 2) (κ := Fin 3) (by simp) one_pos zero_le_one
  simp only [Fintype.card_fin] at hv hlt
  rw [hv, trueVar_one_one_two_three] at *
  exact ⟨rfl, hlt⟩

/-- Two distinct cells of donor `0` are not independent in the explicit model. -/
example :
    ¬ IndepFun (riModel (δ := Fin 2) (κ := Fin 3) 1 1 (0, 0)) (riModel 1 1 (0, 1))
      (stdGaussianPi _ _) :=
  not_indepFun_sameDonor (isRandomIntercept_riModel zero_le_one zero_le_one) one_ne_zero 0
    (by decide)

/-! ### Batch confounded with condition -/

/-- Two donors; condition and batch indicators both `![0, 1]`. -/
def condC : Fin 2 → ℝ := ![0, 1]

/-- Directly from the definitions: `(μ₀, τ, β) = (0, 1, 0)` and `(0, 0, 1)` give identical
observations for any noise. -/
example (U : Fin 2 × Fin 3 → Unit → ℝ) :
    obs condC condC 0 1 0 U = obs condC condC 0 0 1 U := by
  funext i ω
  simp [obs, meanFn]

/-- On the one-point space every noise vector is measurable. -/
theorem aemeasurable_unit (μ : Measure Unit) (U : Fin 2 × Fin 3 → Unit → ℝ) :
    AEMeasurable (fun ω i ↦ U i ω) μ :=
  Measurable.of_discrete.aemeasurable

example (μ : Measure Unit) [IsProbabilityMeasure μ] (U : Fin 2 × Fin 3 → Unit → ℝ) :
    ¬ ∃ F : Measure (Fin 2 × Fin 3 → ℝ) → ℝ,
      ∀ μ₀ τ β, F (dataLaw condC condC μ μ₀ τ β U (aemeasurable_unit μ U)) = τ :=
  not_identifiable_of_confounded (a := 0) (b := 1) (by funext d; simp) one_ne_zero μ U _

/-- The data law is a probability measure. -/
example (U : Fin 2 × Fin 3 → Unit → ℝ) :
    IsProbabilityMeasure
      (dataLaw condC condC (Measure.dirac ()) 0 1 0 U (aemeasurable_unit _ U)) :=
  inferInstance

/-- It is the actual law of the observations, not the zero fallback of `Measure.map`: with zero
noise on a point mass it is the point mass at the donor-mean vector, computed from the
definitions. -/
example :
    dataLaw condC condC (Measure.dirac ()) 0 1 0 (fun _ _ ↦ 0) (aemeasurable_unit _ _)
      = Measure.dirac (fun i : Fin 2 × Fin 3 ↦ condC i.1) := by
  rw [dataLaw, Measure.map_dirac' Measurable.of_discrete]
  congr 1
  funext i
  simp [obs, meanFn]

/-- The reverse coding: all condition-`1` donors in batch `0`, `batch = 1 - cond`. -/
def batchR : Fin 2 → ℝ := ![1, 0]

/-- Directly from the definitions: `(0, 1, 0)` and `(-1, 2, 1)` give identical observations. -/
example (U : Fin 2 × Fin 3 → Unit → ℝ) :
    obs condC batchR 0 1 0 U = obs condC batchR (-1) 2 1 U := by
  funext i ω
  fin_cases i <;> norm_num [obs, meanFn, condC, batchR]

example (μ : Measure Unit) [IsProbabilityMeasure μ] (U : Fin 2 × Fin 3 → Unit → ℝ) :
    ¬ ∃ F : Measure (Fin 2 × Fin 3 → ℝ) → ℝ,
      ∀ μ₀ τ β, F (dataLaw condC batchR μ μ₀ τ β U (aemeasurable_unit μ U)) = τ :=
  not_identifiable_of_confounded (a := 1) (b := -1)
    (by funext d; fin_cases d <;> simp [condC, batchR]) (by norm_num) μ U _

/-- Off the boundary: in a crossed `2 × 2` design (four donors) the same two parameter values give
different donor means, so the confounding hypothesis is not vacuous. -/
def condX : Fin 4 → ℝ := ![0, 0, 1, 1]

/-- Batch indicators of the crossed design. -/
def batchX : Fin 4 → ℝ := ![0, 1, 0, 1]

example : meanFn condX batchX 0 1 0 2 ≠ meanFn condX batchX 0 0 1 2 := by
  norm_num [meanFn, condX, batchX]

/-- In the crossed design donors `0` and `2` share batch `0` and differ in condition; with zero
noise the contrast is `τ`, computed from the integrals directly. -/
example (μ₀ τ β : ℝ) :
    ∫ ω, obs condX batchX μ₀ τ β (fun (_ : Fin 4 × Fin 3) (_ : Unit) ↦ (0 : ℝ)) (2, 0) ω
        ∂(Measure.dirac ())
      - ∫ ω, obs condX batchX μ₀ τ β (fun _ _ ↦ (0 : ℝ)) (0, 0) ω ∂(Measure.dirac ()) = τ := by
  simp [obs, meanFn, condX, batchX]

example (μ₀ τ β : ℝ) :
    ∫ ω, obs condX batchX μ₀ τ β (fun (_ : Fin 4 × Fin 3) (_ : Unit) ↦ (0 : ℝ)) (2, 0) ω
        ∂(Measure.dirac ())
      - ∫ ω, obs condX batchX μ₀ τ β (fun _ _ ↦ (0 : ℝ)) (0, 0) ω ∂(Measure.dirac ()) = τ :=
  contrast_of_sameBatch (by simp) (by simp) (by simp [batchX]) (by norm_num [condX]) μ₀ τ β 0 0

/-- A same-batch pair is not necessary: with a linear batch covariate `![0, 1, 2]` and
`cond = ![0, 1, 1]`, no two donors share a batch, yet the donor means identify `τ`. -/
example (μ₀ τ β : ℝ) :
    let m := meanFn (![0, 1, 1] : Fin 3 → ℝ) ![0, 1, 2] μ₀ τ β
    (m 1 - m 0) - (m 2 - m 1) = τ := by
  simp [meanFn]
  ring

/-- With `batch = cond` (`b = 1`), the contrast is `τ + β`, computed directly. -/
example (μ₀ τ β : ℝ) :
    ∫ ω, obs condC condC μ₀ τ β (fun (_ : Fin 2 × Fin 3) (_ : Unit) ↦ (0 : ℝ)) (1, 0) ω
        ∂(Measure.dirac ())
      - ∫ ω, obs condC condC μ₀ τ β (fun _ _ ↦ (0 : ℝ)) (0, 0) ω ∂(Measure.dirac ())
      = τ + β := by
  simp [obs, meanFn, condC]
  ring

/-- With `batch = 1 - cond` (`a = 1`, `b = -1`), the contrast is `τ - β`, computed directly. -/
example (μ₀ τ β : ℝ) :
    ∫ ω, obs condC batchR μ₀ τ β (fun (_ : Fin 2 × Fin 3) (_ : Unit) ↦ (0 : ℝ)) (1, 0) ω
        ∂(Measure.dirac ())
      - ∫ ω, obs condC batchR μ₀ τ β (fun _ _ ↦ (0 : ℝ)) (0, 0) ω ∂(Measure.dirac ())
      = τ - β := by
  simp [obs, meanFn, condC, batchR]

/-- The library contrast at `b = -1` pins the sign of the `b * β` term: `τ - β`. -/
example (μ₀ τ β : ℝ) :
    ∫ ω, obs condC batchR μ₀ τ β (fun (_ : Fin 2 × Fin 3) (_ : Unit) ↦ (0 : ℝ)) (1, 0) ω
        ∂(Measure.dirac ())
      - ∫ ω, obs condC batchR μ₀ τ β (fun _ _ ↦ (0 : ℝ)) (0, 0) ω ∂(Measure.dirac ())
      = τ - β := by
  refine (contrast_of_confounded (μ := Measure.dirac ()) (U := fun _ _ ↦ (0 : ℝ)) (a := 1)
    (b := -1) (d₀ := 0) (d₁ := 1) (by funext d; fin_cases d <;> simp [condC, batchR])
    (by simp) (by simp) (by simp [condC]) (by simp [condC]) μ₀ τ β 0 0).trans ?_
  ring

/-! ### Axioms -/

#print axioms variance_cellMean
#print axioms naiveVar_eq_trueVar_iff
#print axioms variance_cellMean_eq_iff
#print axioms variance_pseudobulkMean
#print axioms pseudoreplication_counterexample
#print axioms not_indepFun_sameDonor
#print axioms not_identifiable_of_confounded
#print axioms no_unbiased_estimator_of_confounded
#print axioms contrast_of_confounded
#print axioms contrast_of_sameBatch

end MathlibExtTest.Biology.Omics.Pseudobulk
