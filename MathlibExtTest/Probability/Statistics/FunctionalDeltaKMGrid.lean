/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.FunctionalDeltaKMGrid

/-!
# Tests for the fixed-grid Kaplan–Meier weak limit and Wald bands

* Clause fixtures: Hadamard differentiability of the survival map, the fixed-grid scope, and the
  zero-at-risk exclusion.
* The two-point grid recovers the bivariate delta-method limit and its band coverage.
* Gaussian limit coordinates discharge the face-null input, and the Gaussian case reuses
  `ProcessInference.tendsto_coverage_gridBand`; Greenwood standard errors fit the binder.
* The earlier band predicate, variance-consistency input and boundary cases restated on
  `ProcessInference.gridBand`.
-/

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.FunctionalDeltaKMGrid

open MeasureTheory ProbabilityTheory Filter Topology Finset
open MathlibExt.Probability.Statistics.FunctionalDelta MathlibExt.Probability.Statistics.KaplanMeier
open MathlibExt.Probability.Statistics.ProcessInference (gridBand)
open scoped ENNReal NNReal

/-! #### Registry validation and clause fixtures -/

/-- Differentiability clause, discharged (not assumed): the cumulative-hazard-to-survival map on
the grid, `L ↦ prodIntegral (-ΔL)`, is Hadamard differentiable at every `Λ`, tangentially to
every set, with derivative `h ↦ -duhamelDeriv (-ΔΛ) (Δh)`. -/
theorem kmGrid_survivalMap_hasHadamardDeriv {k : ℕ} (Λ : Fin k → ℝ) (D E₀ : Set (Fin k → ℝ)) :
    HasHadamardDerivWithinAt (fun L : Fin k → ℝ ↦ prodIntegral (-gridIncrements L))
      (fun h ↦ -duhamelDeriv (-gridIncrements Λ) (gridIncrements h)) D E₀ Λ := by
  have hF := ((hasFDerivAt_prodIntegral (-gridIncrements Λ)).comp Λ
    (gridIncrements.hasFDerivAt.neg)).hasHadamardDerivWithinAt D E₀
  have h1 : (fun L : Fin k → ℝ ↦ prodIntegral (-gridIncrements L)) =
      prodIntegral ∘ (fun L : Fin k → ℝ ↦ -(gridIncrements L)) := rfl
  have h2 : (fun h : Fin k → ℝ ↦ -duhamelDeriv (-gridIncrements Λ) (gridIncrements h)) =
      ⇑((duhamelDeriv (-gridIncrements Λ)).comp (-gridIncrements)) := by
    funext h
    simp
  rw [h1, h2]
  exact hF

/-- Positive (two-point grid): the Kaplan–Meier limit is the bivariate delta-method image
`(-g₀, (Λ₁ - 2Λ₀) g₀ - (1 - Λ₀) g₁)`, i.e. the gradient of
`Λ ↦ (1 - Λ₀, (1 - Λ₀)(1 - (Λ₁ - Λ₀)))` applied to `g`. -/
theorem kmGrid_twoPoint_limit (Λ g : Fin 2 → ℝ) :
    -duhamelDeriv (-gridIncrements Λ) (gridIncrements g) =
      ![-g 0, (Λ 1 - 2 * Λ 0) * g 0 - (1 - Λ 0) * g 1] := by
  funext j
  fin_cases j
  · have hIic : Iic (0 : Fin 2) = {0} := by decide
    have hIio : Iio (0 : Fin 2) = ∅ := by decide
    simp [duhamelDeriv_apply, gridIncrements_apply, hIic, hIio,
      Matrix.cons_val_zero]
  · have hIic : Iic (1 : Fin 2) = {0, 1} := by decide
    have hIio0 : Iio (0 : Fin 2) = ∅ := by decide
    have hIoc01 : Ioc (0 : Fin 2) 1 = {1} := by decide
    have hIio1 : Iio (1 : Fin 2) = {0} := by decide
    simp [duhamelDeriv_apply, gridIncrements_apply, hIic, hIio0, hIoc01, hIio1,
      Matrix.cons_val_one]
    ring

/-- Positive (two-point grid): Wald-band coverage with the explicit bivariate delta-method
limit, from `tendsto_kmSurvival_fixedGrid_waldCoverage` and `kmGrid_twoPoint_limit`. -/
theorem kmGrid_twoPoint_waldCoverage {Ω Ω' : Type*}
    {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω} {μ' : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (t : Fin 2 → ℝ) (A : StieltjesFunction ℝ) {Dn : ℕ → Ω → CensoredData 2}
    (htime : ∀ n ω, (Dn n ω).time = t) {G : Ω' → Fin 2 → ℝ}
    (hCLT : TendstoInDistribution
      (fun (n : ℕ) ω ↦ √(n : ℝ) • ((fun j ↦ (Dn n ω).nelsonAalen (t j)) - fun j ↦ A (t j)))
      atTop G (fun _ ↦ μ) μ')
    {se : Fin 2 → ℝ} {sehat : ℕ → Ω → Fin 2 → ℝ}
    (hsehat : TendstoInMeasure μ sehat atTop (fun _ ↦ se))
    (hsehat_meas : ∀ n, AEMeasurable (sehat n) μ) (z : ℝ)
    (hnull : ∀ j, μ' {ω | |(![-G ω 0, (A (t 1) - 2 * A (t 0)) * G ω 0 -
      (1 - A (t 0)) * G ω 1] : Fin 2 → ℝ) j| = z * se j} = 0) :
    Tendsto (fun n : ℕ ↦ μ.real {ω | prodIntegral (-gridIncrements fun i ↦ A (t i)) ∈
        gridBand (fun j ↦ (Dn n ω).kmSurvival (t j)) (fun j ↦ sehat n ω j / √(n : ℝ)) z})
      atTop (𝓝 (μ'.real {ω | ∀ j, |(![-G ω 0, (A (t 1) - 2 * A (t 0)) * G ω 0 -
        (1 - A (t 0)) * G ω 1] : Fin 2 → ℝ) j| ≤ z * se j})) := by
  have hH : ∀ ω : Ω', -duhamelDeriv (-gridIncrements fun i ↦ A (t i))
      (gridIncrements (G ω)) =
      (![-G ω 0, (A (t 1) - 2 * A (t 0)) * G ω 0 -
        (1 - A (t 0)) * G ω 1] : Fin 2 → ℝ) :=
    fun ω ↦ kmGrid_twoPoint_limit _ _
  have hnull' : ∀ j, μ' {ω | |(-duhamelDeriv (-gridIncrements fun i ↦ A (t i))
      (gridIncrements (G ω))) j| = z * se j} = 0 := by
    intro j
    simpa only [hH] using hnull j
  have hcov := tendsto_kmSurvival_fixedGrid_waldCoverage t A htime hCLT hsehat hsehat_meas
    z hnull'
  simpa only [hH] using hcov

/-- Boundary (fixed-grid scope): under `htime` the grid does not depend on the sample size or
the outcome, so a grid growing with `n` is outside every statement above. -/
theorem kmGrid_fixedGrid_time_eq {k : ℕ} {Ω : Type*} {t : Fin k → ℝ}
    {Dn : ℕ → Ω → CensoredData k} (htime : ∀ n ω, (Dn n ω).time = t) (n m : ℕ) (ω ω' : Ω) :
    (Dn n ω).time = (Dn m ω').time := by
  exact (htime n ω).trans (htime m ω').symm

/-- Boundary (fixed-grid scope): under `htime` the Atlas evaluation at `(Dn n ω).time j` is the
evaluation at the fixed grid point `t j`. -/
theorem kmGrid_fixedGrid_kmSurvival_eq {k : ℕ} {Ω : Type*} {t : Fin k → ℝ}
    {Dn : ℕ → Ω → CensoredData k} (htime : ∀ n ω, (Dn n ω).time = t) (n : ℕ) (ω : Ω) :
    (fun j ↦ (Dn n ω).kmSurvival ((Dn n ω).time j)) = fun j ↦ (Dn n ω).kmSurvival (t j) := by
  rw [htime n ω]

/-- Degenerate (zero at risk, excluded): at a grid point with nobody at risk there are no
deaths, the Kaplan–Meier factor is the convention `1`, and Greenwood's sum skips the point
(`¬ dⱼ < Yⱼ`); the estimator carries no information there. -/
theorem kmGrid_zero_atRisk_excluded {k : ℕ} (D : CensoredData k) (j : Fin k)
    (h0 : D.atRisk j = 0) :
    D.deaths j = 0 ∧ D.kmFactor j = 1 ∧ ¬ D.deaths j < D.atRisk j := by
  have hd : D.deaths j = 0 := by
    have hle := D.deaths_le_atRisk j
    omega
  refine ⟨hd, by simp [CensoredData.kmFactor, hd, h0], by omega⟩

/-! #### Boundary-null input and reuse of the existing grid-band API -/

/-- Positive (boundary-null input): a nondegenerate centered Gaussian coordinate puts no mass on
`{|Y| = c}` (any real `c`), so Gaussian limit coordinates discharge `hnull`. -/
theorem kmGrid_boundaryNull_of_gaussian {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {μ' : Measure Ω'} {Y : Ω' → ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hY : HasLaw Y (gaussianReal 0 v) μ') (c : ℝ) :
    μ' {ω | |Y ω| = c} = 0 := by
  have h : gaussianReal 0 v {x | |x| = c} = 0 := by
    have := nullSingletonClass_gaussianReal (μ := (0 : ℝ)) hv
    refine measure_mono_null (t := {c, -c}) ?_ ((Set.toFinite _).measure_zero _)
    intro x (hx : |x| = c)
    rcases abs_choice x with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by simp only [Set.mem_singleton_iff]; linarith)
  rw [← hY.map_eq, Measure.map_apply_of_aemeasurable hY.aemeasurable
    (measurableSet_eq_fun (by fun_prop) (by fun_prop))] at h
  exact h

/-- Reuse (Gaussian case): when the Kaplan–Meier limit coordinates are nondegenerate centered
Gaussians and `sehat n → √v` in probability, the coverage limit is exactly
`ProcessInference.tendsto_coverage_gridBand` applied to the Kaplan–Meier limit from
`tendstoInDistribution_kmSurvival_fixedGrid`. -/
theorem kmGrid_gridBand_coverage_of_gaussian {k : ℕ} {Ω Ω' : Type*}
    {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω} {μ' : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (t : Fin k → ℝ) (A : StieltjesFunction ℝ) {Dn : ℕ → Ω → CensoredData k}
    (htime : ∀ n ω, (Dn n ω).time = t) {G : Ω' → Fin k → ℝ}
    (hCLT : TendstoInDistribution
      (fun (n : ℕ) ω ↦ √(n : ℝ) • ((fun j ↦ (Dn n ω).nelsonAalen (t j)) - fun j ↦ A (t j)))
      atTop G (fun _ ↦ μ) μ')
    {v : Fin k → ℝ≥0} (hv : ∀ j, v j ≠ 0)
    (hH : ∀ j, HasLaw (fun ω ↦ (-duhamelDeriv (-gridIncrements fun i ↦ A (t i))
      (gridIncrements (G ω))) j) (gaussianReal 0 (v j)) μ')
    {sehat : ℕ → Ω → Fin k → ℝ}
    (hsehat : TendstoInMeasure μ sehat atTop (fun _ j ↦ √(v j : ℝ)))
    (hsehat_meas : ∀ n, AEMeasurable (sehat n) μ) (z : ℝ) :
    Tendsto (fun n : ℕ ↦ μ.real {ω | prodIntegral (-gridIncrements fun i ↦ A (t i)) ∈
        gridBand (fun j ↦ (Dn n ω).kmSurvival (t j)) (fun j ↦ sehat n ω j / √(n : ℝ)) z})
      atTop (𝓝 (μ'.real {ω | ∀ j, |(-duhamelDeriv (-gridIncrements fun i ↦ A (t i))
        (gridIncrements (G ω))) j| ≤ z * √(v j : ℝ)})) := by
  have hKM : TendstoInDistribution
      (fun (n : ℕ) ω j ↦ √(n : ℝ) *
        ((Dn n ω).kmSurvival (t j) - prodIntegral (-gridIncrements fun i ↦ A (t i)) j))
      atTop (fun ω ↦ -duhamelDeriv (-gridIncrements fun i ↦ A (t i)) (gridIncrements (G ω)))
      (fun _ ↦ μ) μ' := by
    refine (tendstoInDistribution_kmSurvival_fixedGrid t A htime hCLT).congr
      (fun n ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun ω ↦ rfl)
    funext j
    simp [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  exact MathlibExt.Probability.Statistics.ProcessInference.tendsto_coverage_gridBand hv z
    hKM hH hsehat hsehat_meas

/-- Use (Atlas variance estimator fits the binder): Greenwood standard errors
`sehat n ω j = √(n * V̂ₙ(t j))` instantiate the coverage theorem. Their consistency (`hgw`) is
an assumption here; Atlas has `greenwoodVariance` but no consistency theorem. -/
theorem kmGrid_greenwood_waldCoverage {k : ℕ} {Ω Ω' : Type*}
    {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω} {μ' : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (t : Fin k → ℝ) (A : StieltjesFunction ℝ) {Dn : ℕ → Ω → CensoredData k}
    (htime : ∀ n ω, (Dn n ω).time = t) {G : Ω' → Fin k → ℝ}
    (hCLT : TendstoInDistribution
      (fun (n : ℕ) ω ↦ √(n : ℝ) • ((fun j ↦ (Dn n ω).nelsonAalen (t j)) - fun j ↦ A (t j)))
      atTop G (fun _ ↦ μ) μ')
    {se : Fin k → ℝ}
    (hgw : TendstoInMeasure μ
      (fun (n : ℕ) ω j ↦ √((n : ℝ) * (Dn n ω).greenwoodVariance (t j))) atTop (fun _ ↦ se))
    (hgw_meas : ∀ n : ℕ, AEMeasurable
      (fun ω j ↦ √((n : ℝ) * (Dn n ω).greenwoodVariance (t j))) μ) (z : ℝ)
    (hnull : ∀ j, μ' {ω | |(-duhamelDeriv (-gridIncrements fun i ↦ A (t i))
      (gridIncrements (G ω))) j| = z * se j} = 0) :
    Tendsto (fun n : ℕ ↦ μ.real {ω | prodIntegral (-gridIncrements fun i ↦ A (t i)) ∈
        gridBand (fun j ↦ (Dn n ω).kmSurvival (t j))
          (fun j ↦ √((n : ℝ) * (Dn n ω).greenwoodVariance (t j)) / √(n : ℝ)) z})
      atTop (𝓝 (μ'.real {ω | ∀ j, |(-duhamelDeriv (-gridIncrements fun i ↦ A (t i))
        (gridIncrements (G ω))) j| ≤ z * se j})) := by
  exact tendsto_kmSurvival_fixedGrid_waldCoverage t A htime hCLT hgw hgw_meas z hnull

/-! #### Restored frozen forms of the earlier FD.01 contract -/

/-- Old band predicate `kmGridBandCovered` (`∀ j, |Ŝ j - S j| ≤ z √(σ̂² j / n)`) is exactly
membership in the existing Atlas `gridBand` with standard errors `√(σ̂² j) / √n`. -/
theorem kmGrid_oldBand_iff_gridBand {k : ℕ} (S Shat sig2hat : Fin k → ℝ) (n : ℕ) (z : ℝ) :
    (∀ j, |Shat j - S j| ≤ z * Real.sqrt (sig2hat j / n)) ↔
      S ∈ gridBand Shat (fun j ↦ Real.sqrt (sig2hat j) / √(n : ℝ)) z := by
  constructor
  · intro h j
    simp only [MathlibExt.Probability.Statistics.ProcessInference.mem_waldInterval_iff,
      ← Real.sqrt_div' _ (Nat.cast_nonneg n)]
    exact h j
  · intro h j
    have hj := h j
    simp only [MathlibExt.Probability.Statistics.ProcessInference.mem_waldInterval_iff,
      ← Real.sqrt_div' _ (Nat.cast_nonneg n)] at hj
    exact hj

/-- Old variance-consistency input `hVar` (coordinatewise convergence in distribution of the
variance estimates to constants) implies the new standard-error binders `hsehat`,
`hsehat_meas` for `sehat n ω j = √(σ̂² n ω j)` and `se j = √(σ² j)`. -/
theorem kmGrid_sehat_of_varianceConsistency {k : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {sig2hat : ℕ → Ω → Fin k → ℝ}
    {sig2 : Fin k → ℝ≥0∞}
    (hVar : ∀ j, TendstoInDistribution (fun (n : ℕ) (ω : Ω) => sig2hat n ω j) atTop
      (fun _ : Unit => (sig2 j).toReal) (fun _ => μ) (Measure.dirac ())) :
    TendstoInMeasure μ (fun n ω j ↦ Real.sqrt (sig2hat n ω j)) atTop
        (fun _ j ↦ Real.sqrt (sig2 j).toReal) ∧
      ∀ n, AEMeasurable (fun ω j ↦ Real.sqrt (sig2hat n ω j)) μ := by
  have hcoord : ∀ j, TendstoInMeasure μ (fun (n : ℕ) ω ↦ Real.sqrt (sig2hat n ω j)) atTop
      (fun _ ↦ Real.sqrt (sig2 j).toReal) := fun j ↦
    TendstoInMeasure.comp_const_of_continuousAt Real.continuous_sqrt.continuousAt
      (tendstoInMeasure_of_tendstoInDistribution_const (hVar j))
  refine ⟨?_, fun n ↦ AEMeasurable.of_eval fun j ↦
    Real.continuous_sqrt.measurable.comp_aemeasurable ((hVar j).forall_aemeasurable n)⟩
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hY : ∀ j, Tendsto (fun n ↦ μ {ω | ε ≤ dist (Real.sqrt (sig2hat n ω j))
      (Real.sqrt (sig2 j).toReal)}) atTop (𝓝 0) :=
    fun j ↦ tendstoInMeasure_iff_dist.1 (hcoord j) ε hε
  have hlim : Tendsto (fun n ↦ ∑ j, μ {ω | ε ≤ dist (Real.sqrt (sig2hat n ω j))
      (Real.sqrt (sig2 j).toReal)}) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum _ fun j _ ↦ hY j
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ zero_le) fun n ↦ ?_
  have hsub : {ω | ε ≤ dist (fun j ↦ Real.sqrt (sig2hat n ω j))
      (fun j ↦ Real.sqrt (sig2 j).toReal)} ⊆
      ⋃ j ∈ (Finset.univ : Finset (Fin k)), {ω | ε ≤ dist (Real.sqrt (sig2hat n ω j))
        (Real.sqrt (sig2 j).toReal)} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    by_cases hall : ∃ j, ε ≤ dist (Real.sqrt (sig2hat n ω j))
      (Real.sqrt (sig2 j).toReal)
    · obtain ⟨j, hj⟩ := hall
      exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨Finset.mem_univ j, hj⟩⟩
    · simp only [not_exists, not_le] at hall
      have hlt := (dist_pi_lt_iff hε).mpr hall
      exact absurd hlt (not_lt_of_ge hω)
  exact (measure_mono hsub).trans (measure_biUnion_finset_le _ _)

/-- Old variance hypothesis `hsig` (`σ² j ≠ 0, ≠ ⊤`) gives the new nonzero standard error. -/
theorem kmGrid_se_ne_zero_of_hsig {k : ℕ} {sig2 : Fin k → ℝ≥0∞}
    (hsig : ∀ j, sig2 j ≠ 0 ∧ sig2 j ≠ ⊤) (j : Fin k) :
    Real.sqrt (sig2 j).toReal ≠ 0 := by
  have hpos : 0 < (sig2 j).toReal := ENNReal.toReal_pos (hsig j).1 (hsig j).2
  exact (Real.sqrt_pos.2 hpos).ne'

/-- Old studentized target, restored with the Kaplan–Meier limit derived (not assumed): under
the old `hsig`/`hVar` inputs, `√n (Ŝₙ j - S j) / √(σ̂² n j) ⇒ H j / √(σ² j)`. -/
theorem kmGrid_studentized_of_varianceConsistency {k : ℕ} {Ω Ω' : Type*}
    {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω} {μ' : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (t : Fin k → ℝ) (A : StieltjesFunction ℝ) {Dn : ℕ → Ω → CensoredData k}
    (htime : ∀ n ω, (Dn n ω).time = t) {G : Ω' → Fin k → ℝ}
    (hCLT : TendstoInDistribution
      (fun (n : ℕ) ω ↦ √(n : ℝ) • ((fun j ↦ (Dn n ω).nelsonAalen (t j)) - fun j ↦ A (t j)))
      atTop G (fun _ ↦ μ) μ')
    {sig2hat : ℕ → Ω → Fin k → ℝ} {sig2 : Fin k → ℝ≥0∞}
    (hsig : ∀ j, sig2 j ≠ 0 ∧ sig2 j ≠ ⊤)
    (hVar : ∀ j, TendstoInDistribution (fun (n : ℕ) (ω : Ω) => sig2hat n ω j) atTop
      (fun _ : Unit => (sig2 j).toReal) (fun _ => μ) (Measure.dirac ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω j ↦ √(n : ℝ) *
        ((Dn n ω).kmSurvival (t j) - prodIntegral (-gridIncrements fun i ↦ A (t i)) j) /
          Real.sqrt (sig2hat n ω j))
      atTop
      (fun ω j ↦ -duhamelDeriv (-gridIncrements fun i ↦ A (t i)) (gridIncrements (G ω)) j /
        Real.sqrt (sig2 j).toReal)
      (fun _ ↦ μ) μ' := by
  obtain ⟨hsehat, hsehat_meas⟩ := kmGrid_sehat_of_varianceConsistency hVar
  exact tendstoInDistribution_kmSurvival_fixedGrid_studentized t A htime hCLT
    (fun j ↦ kmGrid_se_ne_zero_of_hsig hsig j) hsehat hsehat_meas

/-- Old coverage target, restored in its old band form (`kmGridBandCovered` inlined, `toReal`
probabilities) under the old `hVar`/face-null inputs, with the Kaplan–Meier limit derived. The
old `hsig` binder is not needed for coverage. -/
theorem kmGrid_waldCoverage_of_varianceConsistency {k : ℕ} {Ω Ω' : Type*}
    {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω} {μ' : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (t : Fin k → ℝ) (A : StieltjesFunction ℝ) {Dn : ℕ → Ω → CensoredData k}
    (htime : ∀ n ω, (Dn n ω).time = t) {G : Ω' → Fin k → ℝ}
    (hCLT : TendstoInDistribution
      (fun (n : ℕ) ω ↦ √(n : ℝ) • ((fun j ↦ (Dn n ω).nelsonAalen (t j)) - fun j ↦ A (t j)))
      atTop G (fun _ ↦ μ) μ')
    {sig2hat : ℕ → Ω → Fin k → ℝ} {sig2 : Fin k → ℝ≥0∞}
    (hVar : ∀ j, TendstoInDistribution (fun (n : ℕ) (ω : Ω) => sig2hat n ω j) atTop
      (fun _ : Unit => (sig2 j).toReal) (fun _ => μ) (Measure.dirac ())) (z : ℝ)
    (hct : ∀ j, μ' {ω | |(-duhamelDeriv (-gridIncrements fun i ↦ A (t i))
      (gridIncrements (G ω))) j| = z * Real.sqrt (sig2 j).toReal} = 0) :
    Tendsto (fun (n : ℕ) => (μ {ω | ∀ j, |(Dn n ω).kmSurvival (t j) -
        prodIntegral (-gridIncrements fun i ↦ A (t i)) j| ≤
          z * Real.sqrt (sig2hat n ω j / n)}).toReal)
      atTop (𝓝 (μ' {ω | ∀ j, |(-duhamelDeriv (-gridIncrements fun i ↦ A (t i))
        (gridIncrements (G ω))) j| ≤ z * Real.sqrt (sig2 j).toReal}).toReal) := by
  obtain ⟨hsehat, hsehat_meas⟩ := kmGrid_sehat_of_varianceConsistency hVar
  have hcov := tendsto_kmSurvival_fixedGrid_waldCoverage t A htime hCLT hsehat hsehat_meas
    z hct
  refine hcov.congr (fun n ↦ ?_)
  rw [measureReal_def]
  congr 1
  congr 1
  ext ω
  exact (kmGrid_oldBand_iff_gridBand _ _ _ n z).symm

/-- Old boundary fixture (nonpositive half-width), restored on `gridBand`: with `z ≤ 0` and
nonnegative standard errors the band pins the target to the estimate. -/
theorem kmGrid_gridBand_nonpos_halfWidth {k : ℕ} {S Shat se : Fin k → ℝ} {z : ℝ} (hz : z ≤ 0)
    (hse : ∀ j, 0 ≤ se j) (hband : S ∈ gridBand Shat se z) : S = Shat := by
  funext j
  have hj := hband j
  rw [MathlibExt.Probability.Statistics.ProcessInference.mem_waldInterval_iff] at hj
  have hle : z * se j ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hz (hse j)
  have habs : |Shat j - S j| = 0 := le_antisymm (hj.trans hle) (abs_nonneg _)
  have hsub : Shat j - S j = 0 := abs_eq_zero.1 habs
  exact (sub_eq_zero.1 hsub).symm

/-- Old degenerate fixture (zero estimated variance), restored on `gridBand`: a zero standard
error at `j` forces equality there. -/
theorem kmGrid_gridBand_zero_se {k : ℕ} {S Shat se : Fin k → ℝ} {z : ℝ}
    (hband : S ∈ gridBand Shat se z) (j : Fin k) (h0 : se j = 0) : S j = Shat j := by
  have hj := hband j
  rw [MathlibExt.Probability.Statistics.ProcessInference.mem_waldInterval_iff, h0,
    mul_zero] at hj
  have habs : |Shat j - S j| = 0 := le_antisymm hj (abs_nonneg _)
  have hsub : Shat j - S j = 0 := abs_eq_zero.1 habs
  exact (sub_eq_zero.1 hsub).symm

end MathlibExtTest.Probability.Statistics.FunctionalDeltaKMGrid
