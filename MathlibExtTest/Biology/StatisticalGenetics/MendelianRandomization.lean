/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.MendelianRandomization

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Biology.StatisticalGenetics.MendelianRandomization
open scoped ENNReal NNReal

namespace MathlibExtTest.Biology.StatisticalGenetics.MendelianRandomization

/-! ### The linear moment model: a non-vacuous observational witness

A standard normal instrument that is also the exposure, zero residual, and outcome
`Y = 1 + 2 X`; the covariance ratio returns the observational coefficient `β = 2`. -/

/-- The witness linear moment model on `(ℝ, N(0, 1))`. -/
noncomputable def ivWitness : LinearMomentModel (gaussianReal 0 1) where
  instrument := id
  exposure := id
  outcome := fun x => 1 + 2 * x
  residual := 0
  intercept := 1
  coefficient := 2
  memLp_instrument := memLp_id_gaussianReal 2
  memLp_exposure := memLp_id_gaussianReal 2
  memLp_residual := MemLp.zero
  outcome_eq := fun x => by simp

theorem covariance_id_id : cov[id, id; gaussianReal 0 1] = 1 := by
  rw [covariance_self aemeasurable_id, variance_id_gaussianReal]
  simp

/-- The Wald ratio on the witness: `Cov(Z, Y) / Cov(Z, X) = 2`. -/
example : cov[ivWitness.instrument, ivWitness.outcome; gaussianReal 0 1] /
    cov[ivWitness.instrument, ivWitness.exposure; gaussianReal 0 1] = 2 :=
  ivWitness.covariance_div_covariance (by simp [ivWitness])
    (by simp [ivWitness, covariance_id_id])

/-- A structural response with the same observed values as `ivWitness` but a direct effect of
the instrument: it ignores the intervened exposure argument. The observational moment model
cannot distinguish this response from one mediated by the exposure because `X = Z`. -/
def directInstrumentResponse (z _x : ℝ) : ℝ := 1 + 2 * z

example (z x x' : ℝ) : directInstrumentResponse z x = directInstrumentResponse z x' := rfl

example (z : ℝ) : directInstrumentResponse z z = ivWitness.outcome z := rfl

/-- A correlated-residual model: the residual equals the exposure (`U = X`), so
`Y = 1 + 2 X + X`. The OLS coefficient is `2 + Cov(X, U) / Var(X) = 3`, not the decomposition
coefficient `2`. -/
noncomputable def confounded : LinearMomentModel (gaussianReal 0 1) where
  instrument := id
  exposure := id
  outcome := fun x => 1 + 2 * x + x
  residual := id
  intercept := 1
  coefficient := 2
  memLp_instrument := memLp_id_gaussianReal 2
  memLp_exposure := memLp_id_gaussianReal 2
  memLp_residual := memLp_id_gaussianReal 2
  outcome_eq := fun _ => rfl

example : cov[confounded.exposure, confounded.outcome; gaussianReal 0 1] /
    Var[confounded.exposure; gaussianReal 0 1] = 3 := by
  rw [confounded.covariance_div_variance (by simp [confounded, variance_id_gaussianReal])]
  simp [confounded, covariance_id_id, variance_id_gaussianReal]
  norm_num

/-! ### Inverse-variance weighting -/

/-- Two SNPs with ratio estimates `1` and `3` and weights `1` and `1`: IVW is their mean `2`. -/
example : ivw ![1, 2] ![1, 6] ![1, 2] = 2 := by
  simp [ivw, ivwWeight, Fin.sum_univ_two]
  norm_num

example : ivw ![1, 2] ![1, 6] ![1, 2] =
    (∑ j, ivwWeight ![1, 2] ![1, 2] j * ratioEstimate ![1, 2] ![1, 6] j) /
      ∑ j, ivwWeight ![1, 2] ![1, 2] j :=
  ivw_eq_weightedMean _ _ _

/-- Without error IVW recovers `β`. -/
example : ivw ![1, 2] ![3 * 1, 3 * 2] ![1, 2] = 3 := by
  have := ivw_of_proportional (bX := ![(1 : ℝ), 2]) (se := ![1, 2])
    (fun j => by fin_cases j <;> norm_num) ⟨0, by norm_num⟩ 3
  convert this using 2
  ext j
  fin_cases j <;> simp

/-- Boundary: if no SNP is associated with the exposure, `ivw` is the junk value `0`. -/
example : ivw ![0, 0] ![1, 6] ![1, 2] = 0 := by
  simp [ivw, ivwWeight]

/-- The variance formula is non-vacuous: one SNP with `β̂_X = 2`, standard error `1` and a
standard normal error has IVW variance `1 / 4`. -/
example : Var[fun ω => ivw (fun _ : Fin 1 => (2 : ℝ)) (fun _ => 5 * 2 + id ω) (fun _ => 1);
    gaussianReal 0 1] = 1 / 4 := by
  have := variance_ivw (μ := gaussianReal 0 1) (bX := fun _ : Fin 1 => (2 : ℝ))
    (se := fun _ => 1) (fun _ => one_pos) ⟨0, two_ne_zero⟩ 5 (ε := fun _ => id)
    (fun _ => memLp_id_gaussianReal 2) (fun i j h => absurd (Subsingleton.elim i j) h)
    (fun _ => by simp [variance_id_gaussianReal])
  rw [this]
  simp [ivwWeight]
  norm_num

/-! ### MR-Egger under directional pleiotropy

Three SNPs with unit weights, strengths `γ = (1, 2, 3)` and a common pleiotropic term `α = 1`.
InSIDE holds (a constant is uncorrelated with anything), so the Egger slope is `β` and the
intercept is `1`; IVW is biased upwards by `∑ γ / ∑ γ² = 6 / 14`. -/

theorem weightedCov_γ : weightedCov (fun _ : Fin 3 => (1 : ℝ)) ![1, 2, 3] ![1, 2, 3] = 2 / 3 := by
  simp [weightedCov, weightedMean, Fin.sum_univ_three]
  norm_num

theorem inside_const : weightedCov (fun _ : Fin 3 => (1 : ℝ)) (fun _ => 1) ![1, 2, 3] = 0 := by
  simp [weightedCov, weightedMean]

example (β : ℝ) :
    eggerSlope (fun _ : Fin 3 => (1 : ℝ)) ![1, 2, 3] (fun j => 1 + β * ![1, 2, 3] j) = β ∧
      eggerIntercept (fun _ : Fin 3 => (1 : ℝ)) ![1, 2, 3] (fun j => 1 + β * ![1, 2, 3] j) =
        1 := by
  have h := eggerSlope_eq_of_inside (v := fun _ : Fin 3 => (1 : ℝ)) (γ := ![1, 2, 3])
    (α := fun _ => 1) (by rw [weightedCov_γ]; norm_num) inside_const β
  refine ⟨h.1, h.2.trans ?_⟩
  simp [weightedMean]

example (β : ℝ) :
    ivw ![1, 2, 3] (fun j => 1 + β * ![1, 2, 3] j) (fun _ => 1) = β + 6 / 14 := by
  rw [ivw_of_pleiotropy (fun _ => one_pos) ⟨0, by simp⟩]
  simp [ivwWeight, Fin.sum_univ_three]
  norm_num

/-- The Egger line minimizes the weighted residual sum of squares (here against the line
`a = 0`, `b = 1`). -/
example : eggerSSR (fun _ : Fin 3 => (1 : ℝ)) ![1, 2, 3] ![2, 1, 5]
      (eggerIntercept (fun _ => 1) ![1, 2, 3] ![2, 1, 5])
      (eggerSlope (fun _ => 1) ![1, 2, 3] ![2, 1, 5]) ≤
    eggerSSR (fun _ : Fin 3 => (1 : ℝ)) ![1, 2, 3] ![2, 1, 5] 0 1 :=
  eggerSSR_le _ (fun _ => zero_le_one) (by rw [weightedCov_γ]; norm_num) 0 1

/-! ### Weak instruments: two independent standard normals -/

/-- The product of two standard normal laws. -/
noncomputable abbrev μN : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)

theorem hasLaw_fst : HasLaw Prod.fst (gaussianReal 0 1) μN :=
  ⟨by fun_prop, by simp⟩

theorem hasLaw_snd : HasLaw Prod.snd (gaussianReal 0 1) μN :=
  ⟨by fun_prop, by simp⟩

theorem indep_fst_snd : IndepFun Prod.fst Prod.snd μN :=
  indepFun_prod (X := id) (Y := id) measurable_id measurable_id

/-- The ratio of two independent standard normals (a standard Cauchy variable) has no mean. -/
example : ∫⁻ ω, ‖ω.1 / ω.2‖ₑ ∂μN = ∞ :=
  lintegral_enorm_div_eq_top one_ne_zero hasLaw_snd hasLaw_fst.aemeasurable indep_fst_snd
    (by
      intro h
      have := hasLaw_fst.map_eq
      rw [Measure.map_congr h] at this
      change Measure.map (fun _ : ℝ × ℝ => (0 : ℝ)) μN = _ at this
      have h0 : (Measure.map (fun _ : ℝ × ℝ => (0 : ℝ)) μN) {0} = 1 := by
        simp [Measure.map_const]
      rw [this, gaussianReal_apply 0 one_ne_zero] at h0
      simp at h0)

example : ¬ Integrable (fun ω : ℝ × ℝ => ω.1 / ω.2) μN :=
  not_integrable_div_gaussian one_ne_zero hasLaw_fst hasLaw_snd indep_fst_snd
    (Or.inr one_ne_zero)

/-! ### Potential outcomes: a non-vacuous witness for the LATE theorem

Units `ω = (z, c)` drawn uniformly from `Bool × Bool`: the instrument is `z`, and `c` says
whether the unit is a complier (`D(z) = z`) or a never-taker (`D(z) = 0`). The outcome is the
treatment indicator, so every complier has effect `1`, and the Wald estimand is `1`. -/

/-- The uniform law on `Bool`. -/
noncomputable def μ2 : Measure Bool := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac true + Measure.dirac false)

theorem μ2_singleton (b : Bool) : μ2 {b} = 2⁻¹ := by
  cases b <;> simp [μ2]

instance : IsProbabilityMeasure μ2 := ⟨by
  simp [μ2]
  rw [← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]⟩

/-- The witness model. -/
def lateWitness : PotentialOutcomes (Bool × Bool) where
  instrument := Prod.fst
  treatment := fun z ω => z && ω.2
  outcome := fun _ d _ => if d then 1 else 0
  measurable_instrument := measurable_fst
  measurable_treatment := fun _ => measurable_of_countable _
  measurable_outcome := fun _ _ => measurable_const

theorem lateWitness_compliers : lateWitness.compliers = Set.univ ×ˢ {true} := by
  ext ⟨a, b⟩
  cases b <;> simp [PotentialOutcomes.compliers, PotentialOutcomes.type, complianceType,
    lateWitness]

theorem lateWitness_independence : lateWitness.Independence (μ2.prod μ2) :=
  indepFun_prod (X := id)
    (Y := fun b : Bool => ((fun z => z && b), fun (_ : Bool) (d : Bool) => if d then (1 : ℝ)
      else 0))
    measurable_id (measurable_of_countable _)

/-- Generic source-shaped client: relevance is an explicit premise of LATE identification. -/
example {Ω : Type*} [MeasurableSpace Ω] (P : PotentialOutcomes Ω) {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hind : P.Independence μ) (hexcl : P.Exclusion)
    (hmono : P.Monotonicity) (hY : ∀ z d, Integrable (P.outcome z d) μ)
    (hZ : ∀ z, μ (P.instrument ⁻¹' {z}) ≠ 0) (hC : μ P.compliers ≠ 0) (z : Bool) :
    P.waldEstimand μ = ∫ ω, P.outcome z true ω - P.outcome z false ω ∂μ[|P.compliers] :=
  P.waldEstimand_eq_late hind hexcl hmono hY hZ hC z

example : lateWitness.waldEstimand (μ2.prod μ2) = 1 := by
  have hC : (μ2.prod μ2) lateWitness.compliers ≠ 0 := by
    rw [lateWitness_compliers, Measure.prod_prod, measure_univ]
    simp [μ2_singleton]
  have hZ : ∀ z, (μ2.prod μ2) (lateWitness.instrument ⁻¹' {z}) ≠ 0 := by
    intro z
    rw [show lateWitness.instrument ⁻¹' {z} = {z} ×ˢ Set.univ by ext; simp [lateWitness],
      Measure.prod_prod, measure_univ]
    simp [μ2_singleton]
  rw [lateWitness.waldEstimand_eq_late lateWitness_independence (fun _ _ => rfl)
    (fun ω => by cases ω.2 <;> simp [lateWitness]) (fun _ _ => Integrable.of_finite) hZ hC
    true]
  have := cond_isProbabilityMeasure (μ := μ2.prod μ2) hC
  rw [show (fun ω : Bool × Bool => lateWitness.outcome true true ω -
      lateWitness.outcome true false ω) = fun _ => 1 by funext; simp [lateWitness]]
  simp

/-- Positive complier mass gives a genuinely nonzero first stage. -/
example : lateWitness.armMean (μ2.prod μ2) lateWitness.treated true -
    lateWitness.armMean (μ2.prod μ2) lateWitness.treated false ≠ 0 := by
  have hC : (μ2.prod μ2) lateWitness.compliers ≠ 0 := by
    rw [lateWitness_compliers, Measure.prod_prod, measure_univ]
    simp [μ2_singleton]
  have hZ : ∀ z, (μ2.prod μ2) (lateWitness.instrument ⁻¹' {z}) ≠ 0 := by
    intro z
    rw [show lateWitness.instrument ⁻¹' {z} = {z} ×ˢ Set.univ by ext; simp [lateWitness],
      Measure.prod_prod, measure_univ]
    simp [μ2_singleton]
  rw [lateWitness.armMean_treated_sub lateWitness_independence
    (fun ω => by cases ω.2 <;> simp [lateWitness]) hZ]
  exact (measureReal_ne_zero_iff (by simp)).2 hC

/-! ### Zero-complier boundary: only the totalized algebraic identity remains -/

/-- A randomized instrument with no compliers: every unit is a never-taker and every potential
outcome is zero. The structural independence, exclusion and monotonicity assumptions all hold,
but relevance does not. -/
def zeroComplierWitness : PotentialOutcomes (Bool × Bool) where
  instrument := Prod.fst
  treatment := fun _ _ => false
  outcome := fun _ _ _ => 0
  measurable_instrument := measurable_fst
  measurable_treatment := fun _ => measurable_const
  measurable_outcome := fun _ _ => measurable_const

theorem zeroComplierWitness_compliers : zeroComplierWitness.compliers = ∅ := by
  ext ⟨z, u⟩
  simp [PotentialOutcomes.compliers, PotentialOutcomes.type, complianceType,
    zeroComplierWitness]

theorem zeroComplierWitness_independence : zeroComplierWitness.Independence (μ2.prod μ2) :=
  indepFun_prod (X := id)
    (Y := fun _ : Bool => ((fun _ => false), fun (_ : Bool) (_ : Bool) => (0 : ℝ)))
    measurable_id (measurable_of_countable _)

/-- At the zero-complier boundary, the old unrestricted identity is only the totalized `0 = 0`. -/
example : zeroComplierWitness.waldEstimand (μ2.prod μ2) =
    ∫ ω, zeroComplierWitness.outcome true true ω -
      zeroComplierWitness.outcome true false ω ∂(μ2.prod μ2)[|zeroComplierWitness.compliers] := by
  have hZ : ∀ z, (μ2.prod μ2) (zeroComplierWitness.instrument ⁻¹' {z}) ≠ 0 := by
    intro z
    rw [show zeroComplierWitness.instrument ⁻¹' {z} = {z} ×ˢ Set.univ by
      ext
      simp [zeroComplierWitness], Measure.prod_prod, measure_univ]
    simp [μ2_singleton]
  exact zeroComplierWitness.waldEstimand_eq_late_totalized zeroComplierWitness_independence
    (fun _ _ => rfl) (fun _ => by simp [zeroComplierWitness])
    (fun _ _ => Integrable.of_finite) hZ true

example : zeroComplierWitness.waldEstimand (μ2.prod μ2) = 0 ∧
    (∫ ω, zeroComplierWitness.outcome true true ω -
      zeroComplierWitness.outcome true false ω
        ∂(μ2.prod μ2)[|zeroComplierWitness.compliers]) = 0 := by
  simp [PotentialOutcomes.waldEstimand, PotentialOutcomes.armMean,
    PotentialOutcomes.observedOutcome, zeroComplierWitness]

end MathlibExtTest.Biology.StatisticalGenetics.MendelianRandomization
