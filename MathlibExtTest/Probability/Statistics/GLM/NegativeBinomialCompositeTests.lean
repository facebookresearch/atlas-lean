/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GLM.NegativeBinomialCompositeTests

@[expose] public section

open Finset Real Matrix ProbabilityTheory MeasureTheory Filter Topology
open scoped RealInnerProductSpace ENNReal
open MathlibExt.Probability.Statistics.GLM.NegativeBinomial
open MathlibExt.Probability.Statistics.FisherInformation (lawOf)

namespace MathlibExtTest.Probability.Statistics.GLM.NegativeBinomialCompositeTests

/-! ### The composite null, computed from the definition -/

/-- `(β, θ) = (0, 1)` lies in the composite null `β = 0`: coefficient `0`, shape `1 > 0`. -/
example : nbNullParam (0 : Fin 1 → ℝ) 1 ∈ nbCompositeNull 0 := ⟨rfl, one_pos⟩

/-- A nonpositive shape is outside the null even with the right coefficient. -/
example : nbNullParam (0 : Fin 1 → ℝ) (-1) ∉ nbCompositeNull 0 := fun h => by
  have : (0 : ℝ) < -1 := h.2
  norm_num at this

/-- A wrong coefficient is outside the null. -/
example : nbNullParam (fun _ : Fin 1 => (1 : ℝ)) 1 ∉ nbCompositeNull 0 := fun h => by
  have : (1 : ℝ) = 0 := congrFun h.1 0
  norm_num at this

/-! ### A concrete negative binomial model: one coefficient, `β₀ = 0`

One observation with covariate `x` and count `y = 0`. With `β₀ = 0` the mean is `e^0 = 1`, so
`NB(0; θ, 1) = (θ / (θ + 1))^θ`. -/

/-- `NB(0; 1, 1) = 1 / 2`, from the definition. -/
theorem nbRegDensity_one : nbRegDensity (nbNullParam (0 : Fin 1 → ℝ) 1) (0, 0) = 1 / 2 := by
  simp only [nbRegDensity, nbParamShape_nbNullParam, nbParamCoef_nbNullParam, zero_dotProduct,
    exp_zero, negBinomialReal, ascPochhammer_zero, Polynomial.eval_one, Nat.factorial_zero,
    Nat.cast_one, div_one, one_mul, pow_zero, mul_one, Real.rpow_one]
  norm_num

/-- `NB(0; 2, 1) = (2 / 3)² = 4 / 9`, from the definition. -/
theorem nbRegDensity_two : nbRegDensity (nbNullParam (0 : Fin 1 → ℝ) 2) (0, 0) = 4 / 9 := by
  simp only [nbRegDensity, nbParamShape_nbNullParam, nbParamCoef_nbNullParam, zero_dotProduct,
    exp_zero, negBinomialReal, ascPochhammer_zero, Polynomial.eval_one, Nat.factorial_zero,
    Nat.cast_one, div_one, one_mul, pow_zero, mul_one, Real.rpow_two]
  norm_num

/-- **The composite likelihood-ratio statistic, computed from the definition.** Joint estimate
`p̂ = (0, 2)`, restricted estimate `θ̃ = 1`, one observation `(0, 0)`:
`2 (log (4 / 9) - log (1 / 2))`. -/
example : nbRegCompositeLRStat 1 (fun _ => (0, 0)) (nbNullParam (0 : Fin 1 → ℝ) 2) 0 1 =
    2 * (log (4 / 9) - log (1 / 2)) := by
  rw [nbRegCompositeLRStat, Finset.sum_range_one, nbRegDensity_two, nbRegDensity_one]

/-- The statistic vanishes when the joint estimate lies in the null at the restricted shape. -/
example (n : ℕ) (zs : ℕ → (Fin 1 → ℝ) × ℕ) (β₀ : Fin 1 → ℝ) (θ : ℝ) :
    nbRegCompositeLRStat n zs (nbNullParam β₀ θ) β₀ θ = 0 := by
  simp [nbRegCompositeLRStat]

/-- **The composite score, computed from the definition.** Covariate `x = 1`, count `y = 0`,
`β₀ = 0`, shape `θ = 1`: the score is `nbScore 1 0 0 · x = 1 · (0 - 1) / (1 + 1) = -1 / 2`. -/
example : nbRegCoefScore (0 : Fin 1 → ℝ) 1 1 (fun _ => (fun _ => 1, 0)) =
    WithLp.toLp 2 (fun _ => -1 / 2) := by
  ext j
  simp only [nbRegCoefScore, Nat.cast_one, Real.sqrt_one, inv_one, one_smul,
    Finset.sum_range_one, nbCoefProj_apply, nbRegScore, nbParamShape_nbNullParam,
    nbParamCoef_nbNullParam, dotProduct_zero, nbScore, exp_zero, Sum.elim_inl]
  norm_num

/-- A zero covariate carries no information about `β`: the coefficient score is `0`. -/
example (θ : ℝ) : nbRegCoefScore (0 : Fin 1 → ℝ) θ 1 (fun _ => (0, 0)) = 0 := by
  ext j
  simp [nbRegCoefScore, nbRegScore]

/-- The coefficient score is `nbCoefScoreSum` of `NegativeBinomialRestrictedMLE` (offset `0`). -/
example (X : ℕ → Unit → (Fin 1 → ℝ) × ℕ) (θ : ℝ) (n : ℕ) :
    nbCoefProj (∑ i ∈ range n, nbRegScore (nbNullParam 0 θ) (X i ())) =
      nbCoefScoreSum (fun i ω => (X i ω).1) (fun _ _ => 0) (fun i ω => (X i ω).2) 0 n () θ :=
  nbCoefProj_sum_nbRegScore_nbNullParam X 0 θ n ()

/-! ### Null distributions instantiated: two coefficients, `χ²₂` -/

section NullDistributions

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- The composite likelihood-ratio limit for two coefficients is `χ²₂`, not the `χ²₃` of the
simple joint null: the free shape costs no degree of freedom. -/
example {μX : Measure (Fin 2 → ℝ)} [SFinite μX] {β₀ : Fin 2 → ℝ} {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    {X : ℕ → Ω → (Fin 2 → ℝ) × ℕ}
    (hX_law : ∀ i, HasLaw (X i)
      (lawOf (μX.prod Measure.count) nbRegDensity (nbNullParam β₀ θ₀)) P)
    (hX_indep : iIndepFun X P)
    (hs_sq : Integrable (fun z => ‖nbRegScore (nbNullParam β₀ θ₀) z‖ ^ 2)
      (lawOf (μX.prod Measure.count) nbRegDensity (nbNullParam β₀ θ₀)))
    (hs_mean : ∫ z, nbRegScore (nbNullParam β₀ θ₀) z
      ∂(lawOf (μX.prod Measure.count) nbRegDensity (nbNullParam β₀ θ₀)) = 0)
    (hJ_int : Integrable (nbRegObsInfo (nbNullParam β₀ θ₀))
      (lawOf (μX.prod Measure.count) nbRegDensity (nbNullParam β₀ θ₀)))
    (h_info : ∫ z, nbRegObsInfo (nbNullParam β₀ θ₀) z
        ∂(lawOf (μX.prod Measure.count) nbRegDensity (nbNullParam β₀ θ₀)) =
      nbRegFisherInfo (μX.prod Measure.count) (nbNullParam β₀ θ₀))
    (hI_pos : ∀ u, u ≠ 0 →
      0 < ⟪nbRegFisherInfo (μX.prod Measure.count) (nbNullParam β₀ θ₀) u, u⟫)
    {phat : ℕ → Ω → NBParam (Fin 2)} {θtil : ℕ → Ω → ℝ}
    (hfull : TendstoInMeasure P (fun (n : ℕ) ω =>
      2 * ∑ i ∈ range n, (Real.log (nbRegDensity (phat n ω) (X i ω)) -
        Real.log (nbRegDensity (nbNullParam β₀ θ₀) (X i ω))) -
      ⟪Ring.inverse (nbRegFisherInfo (μX.prod Measure.count) (nbNullParam β₀ θ₀))
          ((√(n : ℝ))⁻¹ • ∑ i ∈ range n, nbRegScore (nbNullParam β₀ θ₀) (X i ω)),
        (√(n : ℝ))⁻¹ • ∑ i ∈ range n, nbRegScore (nbNullParam β₀ θ₀) (X i ω)⟫) atTop 0)
    (hres : TendstoInMeasure P (fun (n : ℕ) ω =>
      2 * ∑ i ∈ range n, (Real.log (nbRegDensity (nbNullParam β₀ (θtil n ω)) (X i ω)) -
        Real.log (nbRegDensity (nbNullParam β₀ θ₀) (X i ω))) -
      ((√(n : ℝ))⁻¹ • ∑ i ∈ range n, nbRegScore (nbNullParam β₀ θ₀) (X i ω)) (Sum.inr ()) ^ 2 /
        ⟪nbRegFisherInfo (μX.prod Measure.count) (nbNullParam β₀ θ₀) nbShapeVec, nbShapeVec⟫)
      atTop 0)
    (hLR_meas : ∀ n : ℕ, AEMeasurable
      (fun ω => nbRegCompositeLRStat n (fun i => X i ω) (phat n ω) β₀ (θtil n ω)) P)
    {Q : Ω' → ℝ} (hQ : HasLaw Q (chiSquareMeasure 2) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => nbRegCompositeLRStat n (fun i => X i ω) (phat n ω) β₀ (θtil n ω))
      atTop Q (fun _ => P) P' :=
  tendstoInDistribution_nbRegCompositeLRStat hθ₀ hX_law hX_indep hs_sq hs_mean hJ_int h_info
    hI_pos hfull hres hLR_meas (by rwa [Fintype.card_fin])

/-- The composite score limit for two coefficients is `χ²₂`. -/
example {μX : Measure (Fin 2 → ℝ)} {β₀ : Fin 2 → ℝ} {θ₀ δ : ℝ} (hδ : 0 < δ) (hδθ : δ < θ₀)
    {X : ℕ → Ω → (Fin 2 → ℝ) × ℕ}
    (hX_law : ∀ i, HasLaw (X i)
      (lawOf (μX.prod Measure.count) nbRegDensity (nbNullParam β₀ θ₀)) P)
    (hX_indep : iIndepFun X P)
    (hs_sq : Integrable (fun z => ‖nbRegScore (nbNullParam β₀ θ₀) z‖ ^ 2)
      (lawOf (μX.prod Measure.count) nbRegDensity (nbNullParam β₀ θ₀)))
    (hs_mean : ∫ z, nbRegScore (nbNullParam β₀ θ₀) z
      ∂(lawOf (μX.prod Measure.count) nbRegDensity (nbNullParam β₀ θ₀)) = 0)
    (hI_pos : ∀ u, u ≠ 0 →
      0 < ⟪nbRegFisherInfo (μX.prod Measure.count) (nbNullParam β₀ θ₀) u, u⟫)
    {θtil : ℕ → Ω → ℝ} (hcons : TendstoInMeasure P θtil atTop (fun _ => θ₀))
    (htight : ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, P {ω | C < √(n : ℝ) * |θtil n ω - θ₀|} ≤ ε)
    (hcross : ∀ ε > 0, Tendsto (fun n : ℕ => P {ω | ∃ c ∈ Metric.closedBall θ₀ δ,
      ε ≤ ‖nbCrossAvg (fun i ω => (X i ω).1) (fun _ _ => 0) (fun i ω => (X i ω).2) β₀ n ω c‖})
      atTop (𝓝 0))
    (hTtil_meas : ∀ n : ℕ,
      AEMeasurable (fun ω => nbRegCoefScore β₀ (θtil n ω) n fun i => X i ω) P)
    {Bhat : ℕ → Ω → EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)}
    (hBhat_meas : ∀ n, AEMeasurable (Bhat n) P)
    (hBhat : TendstoInMeasure P Bhat atTop
      (fun _ => nbCoefBlock (nbRegFisherInfo (μX.prod Measure.count) (nbNullParam β₀ θ₀))))
    {Q : Ω' → ℝ} (hQ : HasLaw Q (chiSquareMeasure 2) P') :
    TendstoInDistribution (fun (n : ℕ) ω =>
        ⟪Ring.inverse (Bhat n ω) (nbRegCoefScore β₀ (θtil n ω) n fun i => X i ω),
          nbRegCoefScore β₀ (θtil n ω) n fun i => X i ω⟫)
      atTop Q (fun _ => P) P' :=
  tendstoInDistribution_nbRegCompositeScoreStatistic hδ hδθ hX_law hX_indep hs_sq hs_mean hI_pos
    hcons htight hcross hTtil_meas hBhat_meas hBhat (by rwa [Fintype.card_fin])

end NullDistributions

/-! ### The simple joint null (T131's setting) as a special case

When the restricted shape equals the true shape, `θ̃ = θ₀`, the composite statistic is the
simple-joint-null statistic of `NegativeBinomialAN`, `2 ∑ (log f(p̂) - log f(p₀))`, and the
coefficient score is the coefficient block of T131's scaled joint score at `p₀`. -/

/-- With `θ̃ = θ₀` the composite statistic is T131's simple-null statistic (definitional). -/
example (n : ℕ) (zs : ℕ → (Fin 1 → ℝ) × ℕ) (phat : NBParam (Fin 1)) (β₀ : Fin 1 → ℝ)
    (θ₀ : ℝ) :
    nbRegCompositeLRStat n zs phat β₀ θ₀ = 2 * ∑ i ∈ range n,
      (Real.log (nbRegDensity phat (zs i)) -
        Real.log (nbRegDensity (nbNullParam β₀ θ₀) (zs i))) := rfl

/-- In the decomposition `nbRegCompositeLRStat_eq_sub` relative to `p₀ = (β₀, θ₀)`, the
restricted term vanishes at `θ̃ = θ₀`, computed from the definition. -/
example (n : ℕ) (zs : ℕ → (Fin 1 → ℝ) × ℕ) (β₀ : Fin 1 → ℝ) (θ₀ : ℝ) :
    2 * ∑ i ∈ range n, (Real.log (nbRegDensity (nbNullParam β₀ θ₀) (zs i)) -
      Real.log (nbRegDensity (nbNullParam β₀ θ₀) (zs i))) = 0 := by
  simp

/-- Concretely: `p̂ = (0, 2)`, `θ̃ = θ₀ = 1`; the composite statistic equals the simple-null
statistic `2 (log (4 / 9) - log (1 / 2))` and the decomposition agrees. -/
example : nbRegCompositeLRStat 1 (fun _ => (0, 0)) (nbNullParam (0 : Fin 1 → ℝ) 2) 0 1 =
    2 * ∑ _i ∈ range 1, (Real.log (nbRegDensity (nbNullParam (0 : Fin 1 → ℝ) 2) (0, 0)) -
        Real.log (nbRegDensity (nbNullParam (0 : Fin 1 → ℝ) 1) (0, 0))) -
      2 * ∑ _i ∈ range 1, (Real.log (nbRegDensity (nbNullParam (0 : Fin 1 → ℝ) 1) (0, 0)) -
        Real.log (nbRegDensity (nbNullParam (0 : Fin 1 → ℝ) 1) (0, 0))) := by
  rw [nbRegCompositeLRStat_eq_sub _ _ _ (nbNullParam 0 1)]

/-- With `θ̃ = θ₀` the coefficient score is the coefficient block of T131's scaled joint score. -/
example (n : ℕ) (zs : ℕ → (Fin 1 → ℝ) × ℕ) (β₀ : Fin 1 → ℝ) (θ₀ : ℝ) :
    nbRegCoefScore β₀ θ₀ n zs =
      nbCoefProj ((√(n : ℝ))⁻¹ • ∑ i ∈ range n, nbRegScore (nbNullParam β₀ θ₀) (zs i)) := by
  rw [nbRegCoefScore, map_smul]

/-! ### Fixed shape: no nuisance parameter, no composite claim

If `k = θ₀` is known, the "restricted estimate" is the constant `θ₀`. Its hypotheses in the
composite theorems hold by computation (below), and the statistic is the known-shape coefficient
score statistic, whose limit is the plain central limit theorem
`tendstoInDistribution_nbRegCoefScore`. Nothing composite is claimed in this case. -/

section FixedShape

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The constant estimate is consistent, computed from the definition. -/
example (θ₀ : ℝ) : TendstoInMeasure P (fun (_ : ℕ) (_ : Ω) => θ₀) atTop (fun _ => θ₀) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have h : {ω : Ω | ε ≤ ‖θ₀ - θ₀‖} = ∅ := by
    ext ω
    simp only [sub_self, norm_zero, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
      not_le]
    exact hε
  simp only [h, measure_empty]
  exact tendsto_const_nhds

/-- `√n (θ₀ - θ₀) = 0` is bounded in probability, computed from the definition. -/
example (θ₀ : ℝ) (ε : ℝ≥0∞) : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
    P {ω : Ω | C < √(n : ℝ) * |(fun (_ : ℕ) (_ : Ω) => θ₀) n ω - θ₀|} ≤ ε := by
  refine ⟨0, Eventually.of_forall fun n => ?_⟩
  have h : {ω : Ω | (0 : ℝ) < √(n : ℝ) * |θ₀ - θ₀|} = ∅ := by
    ext ω
    simp
  simp only [h, measure_empty, zero_le]

/-- With a fixed shape the statistic is the known-shape score at `θ₀` (definitional). -/
example (β₀ : Fin 1 → ℝ) (θ₀ : ℝ) (n : ℕ) (X : ℕ → Ω → (Fin 1 → ℝ) × ℕ) (ω : Ω) :
    (nbRegCoefScore β₀ ((fun (_ : ℕ) (_ : Ω) => θ₀) n ω) n fun i => X i ω) =
      nbRegCoefScore β₀ θ₀ n fun i => X i ω := rfl

end FixedShape

end MathlibExtTest.Probability.Statistics.GLM.NegativeBinomialCompositeTests
