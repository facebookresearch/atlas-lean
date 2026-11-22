/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Matrix.MeasurableSpace
public import MathlibExt.Probability.Statistics.HC0Sandwich
public import MathlibExt.Probability.Statistics.LinearModel.OLSConsistency
public import MathlibExt.Probability.Statistics.Survival.ProcessInference

/-!
# Heteroskedasticity-robust (HC0) inference for OLS under random design

`HC0Sandwich` proves a.s. consistency of the HC0 meat and sandwich conditionally on three
hypotheses: a.s. consistency of the coefficient estimator (`hβ`), a.s. convergence of the bread
(`hQ`) and of its inverse (`hQinv`). This file discharges all three for OLS in the i.i.d.
random-design linear model `yᵢ = xᵢ ⬝ᵥ β + uᵢ` and uses the result for robust Wald intervals.
It does not reprove the meat or sandwich consistency; it imports `HC0Sandwich` and
`OLSConsistency` (Atlas ST05.T01) and composes them.

Model: the pairs `(xᵢ, uᵢ)` are i.i.d., `𝔼‖x₀‖⁴ < ∞`, `𝔼[‖x₀‖² u₀²] < ∞`, the moment
exogeneity `𝔼[u₀ x₀] = 0` holds, and the population Gram `Q = 𝔼[x₀ x₀ᵀ]` (`popGram`) is
nonsingular. No conditional homoskedasticity is assumed: `𝔼[u₀² | x₀]` may depend on `x₀`.

## Discharge obligations: what this file covers and what it leaves

Covered here (Atlas T132/T202):
* `hβ`: `β̂ₙ → β` a.s., from `tendsto_olsSeqEstimator_ae` (ST05.T01), with the Gram and score
  integrability derived from the two moment conditions above
  (`integrable_gram_of_integrable_norm_pow_four`, `integrable_score_of_integrable_norm_sq_mul_sq`).
* `hQ`: `Q̂ₙ → Q` a.s., which is `tendsto_sampleGram_ae` (ST05.T01).
* `hQinv`: `Q̂ₙ⁻¹ → Q⁻¹` a.s. (`tendsto_olsSampleGram_inv_ae`).
* The composition: the HC0 sandwich built from the observable OLS residuals `yᵢ - xᵢ ⬝ᵥ β̂ₙ`
  converges a.s. to `Q⁻¹ Ω Q⁻ᵀ` with `Ω = 𝔼[u₀² x₀ x₀ᵀ]` (`hc0OLSSandwich_tendsto_ae`).
* Robust Wald inference for a linear contrast `c ⬝ᵥ β`: the interval
  `c ⬝ᵥ β̂ₙ ± z √(cᵀ V̂ₙ c / n)` with the HC0 sandwich `V̂ₙ` has asymptotic coverage equal to the
  standard-normal mass of `[-z, z]` (`tendsto_coverage_hc0Wald`), given asymptotic normality of
  the contrast.

Left to the econ program (not attempted here, so nothing below duplicates it):
* Asymptotic normality of OLS, `√n (β̂ₙ - β) ⟶ N(0, Q⁻¹ Ω Q⁻ᵀ)`, is the hypothesis `hAN` of
  `tendsto_coverage_hc0Wald`; its general discharge from the multivariate CLT is not proved here.
* Structural identification (exogeneity `𝔼[u | x] = 0`, instruments) identifying `β` with the
  population projection coefficient; this file works with the moment condition `𝔼[u₀ x₀] = 0`.
* Finite-sample corrections (HC1-HC3), clustered or serially correlated errors, and
  non-identically distributed (fixed or triangular) designs.

## Main results

- `tendsto_olsSampleGram_inv_ae`: the bread inverse converges a.s. (`hQinv`).
- `hc0OLSSandwich_tendsto_ae`: unconditional a.s. consistency of the OLS HC0 sandwich.
- `measurable_hc0OLSSandwich`: the HC0 sandwich at each sample size is measurable.
- `tendsto_coverage_hc0Wald`: asymptotic coverage of the robust Wald interval.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open MathlibExt.Probability.Statistics.HC0Sandwich
open MathlibExt.Probability.Statistics.ProcessInference
open scoped Function

namespace MathlibExt.Probability.Statistics.LinearModel

variable {k : Type*} [Fintype k] {Ω : Type*}

/-- The normalized sample Gram matrix (the OLS bread) `Q̂ₙ = n⁻¹ ∑_{i<n} xᵢ xᵢᵀ`; it is the
matrix inverted in `olsSeqEstimator_eq`. -/
noncomputable def olsSampleGram (X : ℕ → Ω → (k → ℝ)) (n : ℕ) (ω : Ω) : Matrix k k ℝ :=
  (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)

/-- The HC0 sandwich of OLS at sample size `n`: `Q̂ₙ⁻¹ Ω̂ₙ Q̂ₙ⁻ᵀ`, where the meat `Ω̂ₙ` is
`hc0Meat` evaluated at the observable OLS residuals `yᵢ - xᵢ ⬝ᵥ β̂ₙ`. -/
noncomputable def hc0OLSSandwich [DecidableEq k] (X : ℕ → Ω → (k → ℝ)) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : Matrix k k ℝ :=
  (olsSampleGram X n ω)⁻¹ *
    hc0Meat (fun i => X i ω) (fun i => Y i ω - X i ω ⬝ᵥ olsSeqEstimator X Y n ω) n *
    ((olsSampleGram X n ω)⁻¹)ᵀ

/-- The population HC0 meat `Ω = 𝔼[u₀² x₀ x₀ᵀ]`, entrywise. -/
noncomputable def hc0PopMeat [MeasurableSpace Ω] (X0 : Ω → (k → ℝ)) (U0 : Ω → ℝ)
    (μ : Measure Ω) : Matrix k k ℝ :=
  Matrix.of fun a b => ∫ ω, (U0 ω) ^ 2 * X0 ω a * X0 ω b ∂μ

/-- The population HC0 sandwich `Q⁻¹ Ω Q⁻ᵀ`, the asymptotic covariance of `√n (β̂ₙ - β)`. -/
noncomputable def hc0PopSandwich [DecidableEq k] [MeasurableSpace Ω] (X0 : Ω → (k → ℝ))
    (U0 : Ω → ℝ) (μ : Measure Ω) : Matrix k k ℝ :=
  (popGram X0 μ)⁻¹ * hc0PopMeat X0 U0 μ * ((popGram X0 μ)⁻¹)ᵀ

section Moments

variable [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- A finite fourth moment `𝔼‖x₀‖⁴ < ∞` makes every Gram entry `x₀ a * x₀ b` integrable,
since `|x_a x_b| ≤ ‖x‖² ≤ 1 + ‖x‖⁴`. -/
theorem integrable_gram_of_integrable_norm_pow_four {X0 : Ω → (k → ℝ)} (hX : AEMeasurable X0 μ)
    (hMom4 : Integrable (fun ω => ‖X0 ω‖ ^ 4) μ) (a b : k) :
    Integrable (fun ω => X0 ω a * X0 ω b) μ := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add hMom4)
    (((measurable_pi_apply a).comp_aemeasurable hX).mul
      ((measurable_pi_apply b).comp_aemeasurable hX)).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  have ha : |X0 ω a| ≤ ‖X0 ω‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm (X0 ω) a
  have hb : |X0 ω b| ≤ ‖X0 ω‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm (X0 ω) b
  have hab : |X0 ω a| * |X0 ω b| ≤ ‖X0 ω‖ * ‖X0 ω‖ :=
    mul_le_mul ha hb (abs_nonneg _) (norm_nonneg _)
  rw [Real.norm_eq_abs, abs_mul]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (‖X0 ω‖ ^ 2 - 1)]

/-- The moment `𝔼[‖x₀‖² u₀²] < ∞` makes the score `u₀ • x₀` integrable,
since `|u| ‖x‖ ≤ 1 + ‖x‖² u²`. -/
theorem integrable_score_of_integrable_norm_sq_mul_sq {X0 : Ω → (k → ℝ)} {U0 : Ω → ℝ}
    (hXU : AEMeasurable (fun ω => (X0 ω, U0 ω)) μ)
    (hMom2 : Integrable (fun ω => ‖X0 ω‖ ^ 2 * (U0 ω) ^ 2) μ) :
    Integrable (fun ω => U0 ω • X0 ω) μ := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add hMom2)
    ((measurable_snd.smul measurable_fst).comp_aemeasurable hXU).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  simp only [Pi.add_apply]
  have h1 := abs_nonneg (U0 ω)
  have h2 := norm_nonneg (X0 ω)
  have h3 : (U0 ω) ^ 2 = |U0 ω| ^ 2 := (sq_abs _).symm
  nlinarith [sq_nonneg (|U0 ω| * ‖X0 ω‖ - 1), mul_nonneg h1 h2]

end Moments

/-- **Discharge of `hQinv`.** For pairwise independent, identically distributed regressors with
integrable Gram entries and a nonsingular population Gram, the inverse of the sample Gram
converges a.s. to the inverse of the population Gram. -/
theorem tendsto_olsSampleGram_inv_ae [DecidableEq k] [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → (k → ℝ)}
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hintGram : ∀ a b, Integrable (fun ω => X 0 ω a * X 0 ω b) μ)
    (hQ : IsUnit (popGram (X 0) μ)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (olsSampleGram X n ω)⁻¹) atTop
      (𝓝 (popGram (X 0) μ)⁻¹) := by
  filter_upwards [tendsto_sampleGram_ae hindep hident hintGram] with ω hω
  have hdet : (popGram (X 0) μ).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp hQ).ne_zero
  have hinv : ContinuousAt Inv.inv (popGram (X 0) μ) := by
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  exact hinv.tendsto.comp hω

/-- **Unconditional a.s. consistency of the OLS HC0 sandwich.** In the i.i.d. random-design model
`yᵢ = xᵢ ⬝ᵥ β + uᵢ` with `𝔼‖x₀‖⁴ < ∞`, `𝔼[‖x₀‖² u₀²] < ∞`, `𝔼[u₀ x₀] = 0` and a nonsingular
population Gram, the HC0 sandwich computed from the observable OLS residuals converges a.s. to
`Q⁻¹ Ω Q⁻ᵀ`. The three hypotheses `hβ`, `hQ`, `hQinv` of `HC0Sandwich` are discharged. -/
theorem hc0OLSSandwich_tendsto_ae [DecidableEq k] [Nonempty k] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → (k → ℝ)} {U : ℕ → Ω → ℝ}
    (β : k → ℝ)
    (hJoint : iIndepFun (fun i ω => (X i ω, U i ω)) μ)
    (hIdent : ∀ i, IdentDistrib (fun ω => (X i ω, U i ω)) (fun ω => (X 0 ω, U 0 ω)) μ μ)
    (hMom4 : Integrable (fun ω => ‖X 0 ω‖ ^ 4) μ)
    (hMom2 : Integrable (fun ω => ‖X 0 ω‖ ^ 2 * (U 0 ω) ^ 2) μ)
    (hmeanScore : ∫ ω, U 0 ω • X 0 ω ∂μ = 0)
    (hQ : IsUnit (popGram (X 0) μ)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => hc0OLSSandwich X (fun i ω => X i ω ⬝ᵥ β + U i ω) n ω)
      atTop (𝓝 (hc0PopSandwich (X 0) (U 0) μ)) := by
  have hpair : Pairwise ((· ⟂ᵢ[μ] ·) on fun i ω => (X i ω, U i ω)) :=
    fun i j hij => hJoint.indepFun hij
  have hindepX : Pairwise ((· ⟂ᵢ[μ] ·) on X) :=
    fun i j hij => (hpair hij).comp measurable_fst measurable_fst
  have hidentX : ∀ i, IdentDistrib (X i) (X 0) μ μ := fun i => (hIdent i).comp measurable_fst
  have hintGram := integrable_gram_of_integrable_norm_pow_four (hidentX 0).aemeasurable_fst hMom4
  have hintScore :=
    integrable_score_of_integrable_norm_sq_mul_sq (hIdent 0).aemeasurable_fst hMom2
  have hβ := tendsto_olsSeqEstimator_ae β hpair hIdent hintGram hintScore hmeanScore hQ
  have hmeat := hc0Meat_matrix_tendsto_ae hJoint hIdent hMom4 hMom2 hβ
  have hQinv := tendsto_olsSampleGram_inv_ae hindepX hidentX hintGram hQ
  have hs := hc0Sandwich_matrix_tendsto_ae hQinv hmeat
  filter_upwards [hs] with ω hω
  refine hω.congr fun n => ?_
  have hres : (fun i => X i ω ⬝ᵥ β + U i ω -
        X i ω ⬝ᵥ olsSeqEstimator X (fun i ω => X i ω ⬝ᵥ β + U i ω) n ω) =
      fun i => U i ω -
        X i ω ⬝ᵥ (olsSeqEstimator X (fun i ω => X i ω ⬝ᵥ β + U i ω) n ω - β) := by
    funext i
    rw [dotProduct_sub]
    ring
  simp only [hc0OLSSandwich, hres]

/-- Real matrix inversion is measurable (it is `det⁻¹ • adjugate`). -/
private theorem measurable_matrix_inv' [DecidableEq k] :
    Measurable (fun A : Matrix k k ℝ => A⁻¹) := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact continuous_id.matrix_det.measurable.inv.mul
    (continuous_id.matrix_adjugate.matrix_elem i j).measurable

section Measurability

variable [MeasurableSpace Ω] {X : ℕ → Ω → (k → ℝ)} {Y : ℕ → Ω → ℝ}

/-- Real matrices form a second-countable space, so products of matrix spaces carry their Borel
structure (needed to turn continuity into measurability on products). -/
local instance {n p : Type*} [Finite n] [Finite p] : SecondCountableTopology (Matrix n p ℝ) :=
  inferInstanceAs (SecondCountableTopology (n → p → ℝ))

omit [Fintype k] in
/-- The sample Gram matrix at each sample size is a measurable function of the sample. -/
theorem measurable_olsSampleGram (hX : ∀ i, Measurable (X i)) (n : ℕ) :
    Measurable (olsSampleGram X n) := by
  refine Measurable.of_eval_matrix _ fun a b => ?_
  simp only [olsSampleGram, Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
    smul_eq_mul]
  exact measurable_const.mul
    (Finset.measurable_sum _ fun i _ => (hX i).eval.mul (hX i).eval)

/-- The OLS estimator at each sample size is a measurable function of the sample. -/
theorem measurable_olsSeqEstimator [DecidableEq k] (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i)) (n : ℕ) :
    Measurable (fun ω => olsSeqEstimator X Y n ω) := by
  have hQ : Measurable (fun ω => (olsSampleGram X n ω)⁻¹) :=
    measurable_matrix_inv'.comp (measurable_olsSampleGram hX n)
  have hg : Measurable (fun ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Y i ω • X i ω) := by
    refine Measurable.of_eval fun a => ?_
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    exact measurable_const.mul (Finset.measurable_sum _ fun i _ => (hY i).mul (hX i).eval)
  have h : Measurable ((fun p : Matrix k k ℝ × (k → ℝ) => p.1 *ᵥ p.2) ∘
      fun ω => ((olsSampleGram X n ω)⁻¹,
        (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Y i ω • X i ω)) :=
    (continuous_fst.matrix_mulVec continuous_snd).measurable.comp (hQ.prodMk hg)
  have heq : (fun ω => olsSeqEstimator X Y n ω) = (fun p : Matrix k k ℝ × (k → ℝ) =>
      p.1 *ᵥ p.2) ∘ fun ω => ((olsSampleGram X n ω)⁻¹,
        (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Y i ω • X i ω) :=
    funext fun ω => olsSeqEstimator_eq X Y n ω
  rw [heq]
  exact h

/-- The OLS HC0 sandwich at each sample size is a measurable function of the sample. -/
theorem measurable_hc0OLSSandwich [DecidableEq k] (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i)) (n : ℕ) :
    Measurable (hc0OLSSandwich X Y n) := by
  have hQ : Measurable (fun ω => (olsSampleGram X n ω)⁻¹) :=
    measurable_matrix_inv'.comp (measurable_olsSampleGram hX n)
  have hb := measurable_olsSeqEstimator hX hY n
  have hdot : ∀ i, Measurable (fun ω => X i ω ⬝ᵥ olsSeqEstimator X Y n ω) := fun i =>
    (Continuous.dotProduct continuous_fst continuous_snd).measurable.comp ((hX i).prodMk hb)
  have hM : Measurable (fun ω => hc0Meat (fun i => X i ω)
      (fun i => Y i ω - X i ω ⬝ᵥ olsSeqEstimator X Y n ω) n) := by
    refine Measurable.of_eval_matrix _ fun a b => ?_
    simp only [hc0Meat, Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
      smul_eq_mul]
    exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      (((hY i).sub (hdot i)).pow_const 2).mul ((hX i).eval.mul (hX i).eval))
  have hcont : Continuous (fun p : Matrix k k ℝ × Matrix k k ℝ => p.1 * p.2 * p.1ᵀ) :=
    (continuous_fst.matrix_mul continuous_snd).matrix_mul continuous_fst.matrix_transpose
  have heq : hc0OLSSandwich X Y n = (fun p : Matrix k k ℝ × Matrix k k ℝ => p.1 * p.2 * p.1ᵀ) ∘
      fun ω => ((olsSampleGram X n ω)⁻¹, hc0Meat (fun i => X i ω)
        (fun i => Y i ω - X i ω ⬝ᵥ olsSeqEstimator X Y n ω) n) := by
    funext ω
    rfl
  rw [heq]
  exact hcont.measurable.comp (hQ.prodMk hM)

end Measurability

/-- **Asymptotic coverage of the heteroskedasticity-robust Wald interval.** In the i.i.d.
random-design model of `hc0OLSSandwich_tendsto_ae` with measurable regressors and errors, fix a
contrast `c` with nondegenerate robust variance `v = cᵀ Q⁻¹ Ω Q⁻ᵀ c ≠ 0`. If the contrast is
asymptotically normal, `√n (c ⬝ᵥ β̂ₙ - c ⬝ᵥ β) ⟶ N(0, v)` (hypothesis `hAN`, not discharged here),
then the Wald interval `c ⬝ᵥ β̂ₙ ± z √(cᵀ V̂ₙ c) / √n` built from the HC0 sandwich `V̂ₙ` covers
`c ⬝ᵥ β` with probability tending to the standard-normal mass of `[-z, z]`. The consistency of the
robust standard error is proved here from `hc0OLSSandwich_tendsto_ae`; it needs no
homoskedasticity. -/
theorem tendsto_coverage_hc0Wald [DecidableEq k] [Nonempty k] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : ℕ → Ω → (k → ℝ)} {U : ℕ → Ω → ℝ}
    (β : k → ℝ) (hXm : ∀ i, Measurable (X i)) (hUm : ∀ i, Measurable (U i))
    (hJoint : iIndepFun (fun i ω => (X i ω, U i ω)) μ)
    (hIdent : ∀ i, IdentDistrib (fun ω => (X i ω, U i ω)) (fun ω => (X 0 ω, U 0 ω)) μ μ)
    (hMom4 : Integrable (fun ω => ‖X 0 ω‖ ^ 4) μ)
    (hMom2 : Integrable (fun ω => ‖X 0 ω‖ ^ 2 * (U 0 ω) ^ 2) μ)
    (hmeanScore : ∫ ω, U 0 ω • X 0 ω ∂μ = 0)
    (hQ : IsUnit (popGram (X 0) μ))
    (c : k → ℝ) {v : NNReal} (hv : v ≠ 0)
    (hvc : (v : ℝ) = c ⬝ᵥ (hc0PopSandwich (X 0) (U 0) μ *ᵥ c))
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 v) P')
    (hAN : TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) *
        (c ⬝ᵥ olsSeqEstimator X (fun i ω => X i ω ⬝ᵥ β + U i ω) n ω - c ⬝ᵥ β))
      atTop Z (fun _ => μ) P')
    (z : ℝ) :
    Tendsto (fun n : ℕ => μ.real {ω | c ⬝ᵥ β ∈
        waldInterval (c ⬝ᵥ olsSeqEstimator X (fun i ω => X i ω ⬝ᵥ β + U i ω) n ω)
          (√(c ⬝ᵥ (hc0OLSSandwich X (fun i ω => X i ω ⬝ᵥ β + U i ω) n ω *ᵥ c)) / √(n : ℝ))
          z})
      atTop (𝓝 ((gaussianReal 0 1).real (Set.Icc (-z) z))) := by
  have hYm : ∀ i, Measurable (fun ω => X i ω ⬝ᵥ β + U i ω) := fun i =>
    ((Continuous.dotProduct continuous_id continuous_const).measurable.comp (hXm i)).add (hUm i)
  have hcont : Continuous (fun M : Matrix k k ℝ => √(c ⬝ᵥ (M *ᵥ c))) :=
    (Continuous.dotProduct continuous_const (continuous_id.matrix_mulVec continuous_const)).sqrt
  have hse_meas : ∀ n : ℕ, Measurable (fun ω =>
      √(c ⬝ᵥ (hc0OLSSandwich X (fun i ω => X i ω ⬝ᵥ β + U i ω) n ω *ᵥ c))) := fun n =>
    hcont.measurable.comp (measurable_hc0OLSSandwich hXm hYm n)
  have hse : TendstoInMeasure μ (fun (n : ℕ) ω =>
      √(c ⬝ᵥ (hc0OLSSandwich X (fun i ω => X i ω ⬝ᵥ β + U i ω) n ω *ᵥ c)))
      atTop (fun _ => √(v : ℝ)) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n => (hse_meas n).aestronglyMeasurable) ?_
    filter_upwards [hc0OLSSandwich_tendsto_ae β hJoint hIdent hMom4 hMom2 hmeanScore hQ]
      with ω hω
    rw [hvc]
    exact (hcont.tendsto _).comp hω
  exact tendsto_coverage_waldInterval hv z hAN hZ hse fun n => (hse_meas n).aemeasurable

end MathlibExt.Probability.Statistics.LinearModel
