/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.GaussianConditioning
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance

/-!
# Linear Gaussian joint law

For a linear Gaussian channel `Y = H X + Z` with independent
noise, the joint law of input and output is the composition of
the input law with the canonical noise kernel from
`MathlibExt.Probability.Distributions.GaussianConditioning`
(imported, not copied); its covariance is the usual
`H Sigma H^T + R` form, and the output moments follow.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix
namespace MathlibExt.InformationTheory.LinearGaussianJointLaw

/-! ### The shared finite-power input model -/

/-- The finite-power input model: `P ≥ 0` and the lower integral of `‖X‖²` is at most `P`,
i.e. `E‖X‖² ≤ P` as an `ℝ≥0∞` lower integral (no integrability is assumed). -/
def PowerConstraint {Ω E : Type*} {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E]
    (μ : Measure Ω) (X : Ω → E) (P : ℝ) : Prop :=
  0 ≤ P ∧ ∫⁻ ω, ENNReal.ofReal (‖X ω‖ ^ 2) ∂μ ≤ ENNReal.ofReal P

/-- A power-constrained (a.e. strongly measurable) input has a finite second moment. -/
theorem PowerConstraint.memLp_two {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [NormedAddCommGroup E] {X : Ω → E} {P : ℝ} (h : PowerConstraint μ X P)
    (hX : AEStronglyMeasurable X μ) : MemLp X 2 μ := by
  refine (memLp_two_iff_integrable_sq_norm hX).2 ⟨hX.norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun _ => by positivity)]
  exact h.2.trans_lt ENNReal.ofReal_lt_top

/-- A power-constrained input has integrable instantaneous power `‖X‖²`. -/
theorem PowerConstraint.integrable_norm_sq {Ω E : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [NormedAddCommGroup E] {X : Ω → E} {P : ℝ} (h : PowerConstraint μ X P)
    (hX : AEStronglyMeasurable X μ) : Integrable (fun ω => ‖X ω‖ ^ 2) μ := by
  refine ⟨hX.norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun _ => by positivity)]
  exact h.2.trans_lt ENNReal.ofReal_lt_top

/-- The power constraint in Bochner form for an a.e. strongly measurable input: `E‖X‖² ≤ P`
(here `‖X‖²` is integrable, so the Bochner integral is the second moment). -/
theorem PowerConstraint.integral_norm_sq_le {Ω E : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [NormedAddCommGroup E] {X : Ω → E} {P : ℝ} (h : PowerConstraint μ X P)
    (hX : AEStronglyMeasurable X μ) : ∫ ω, ‖X ω‖ ^ 2 ∂μ ≤ P := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => by positivity)
    (PowerConstraint.integrable_norm_sq h hX).aestronglyMeasurable]
  calc (∫⁻ ω, ENNReal.ofReal (‖X ω‖ ^ 2) ∂μ).toReal ≤ (ENNReal.ofReal P).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h.2
    _ = P := ENNReal.toReal_ofReal h.1

/-- On a finite measure, a power-constrained input is integrable, so its mean exists. -/
theorem PowerConstraint.integrable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] [NormedAddCommGroup E] {X : Ω → E} {P : ℝ}
    (h : PowerConstraint μ X P) (hX : AEStronglyMeasurable X μ) : Integrable X μ := by
  exact (PowerConstraint.memLp_two h hX).integrable one_le_two

/-- The power model is a property of the input law: `X` satisfies it under `μ` iff the identity
satisfies it under the law `μ.map X` (the form used by law-level consumers). -/
theorem powerConstraint_map_iff {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [NormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E] {X : Ω → E} {P : ℝ}
    (hX : AEMeasurable X μ) : PowerConstraint (μ.map X) id P ↔ PowerConstraint μ X P := by
  have hf : Measurable fun x : E => ENNReal.ofReal (‖id x‖ ^ 2) :=
    ((continuous_norm.pow 2).measurable).ennreal_ofReal
  unfold PowerConstraint
  rw [lintegral_map' hf.aemeasurable hX]
  exact Iff.rfl

/-! ### Canonical joint law of `(X, H X + Z)` -/

/-- **Conditional law of the channel output.** For `Z` independent of `X`, the conditional
distribution of `Y = H X + Z` given `X = x` is `noiseKernel` at `x`, i.e. the law of
`H x + Z`. -/
theorem condDistrib_eq_noiseKernel {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (H : Matrix ι κ ℝ) {R : Matrix ι ι ℝ} {X : Ω → EuclideanSpace ℝ κ}
    {Z : Ω → EuclideanSpace ℝ ι} (hX : Measurable X) (hZ : Measurable Z)
    (hind : IndepFun X Z μ) (hZlaw : μ.map Z = multivariateGaussian 0 R) :
    condDistrib (fun ω => toEuclideanLin H (X ω) + Z ω) X μ =ᵐ[μ.map X]
      MetaMathlibExt.noiseKernel (toEuclideanLin H)
        (MetaMathlibExt.continuous_toEuclideanLin H).measurable (multivariateGaussian 0 R) := by
  have h := MetaMathlibExt.condDistrib_add_of_indepFun hX hZ hind
    (MetaMathlibExt.continuous_toEuclideanLin H).measurable
  rwa [hZlaw] at h

/-- **Canonical joint law of `(X, H X + Z)`**: the input law composed with the additive-noise
kernel of `N(0, R)`. -/
theorem map_prod_eq_compProd_noiseKernel {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (H : Matrix ι κ ℝ) {R : Matrix ι ι ℝ}
    {X : Ω → EuclideanSpace ℝ κ} {Z : Ω → EuclideanSpace ℝ ι} (hX : Measurable X)
    (hZ : Measurable Z) (hind : IndepFun X Z μ)
    (hZlaw : μ.map Z = multivariateGaussian 0 R) :
    μ.map (fun ω => (X ω, toEuclideanLin H (X ω) + Z ω)) =
      μ.map X ⊗ₘ MetaMathlibExt.noiseKernel (toEuclideanLin H)
        (MetaMathlibExt.continuous_toEuclideanLin H).measurable (multivariateGaussian 0 R) := by
  have hY : Measurable fun ω => toEuclideanLin H (X ω) + Z ω :=
    ((MetaMathlibExt.continuous_toEuclideanLin H).measurable.comp hX).add hZ
  rw [← compProd_map_condDistrib hX.aemeasurable hY.aemeasurable]
  exact Measure.compProd_congr (condDistrib_eq_noiseKernel H hX hZ hind hZlaw)

/-! ### Private helpers -/

private lemma coord_toEuclideanLin {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (H : Matrix ι κ ℝ) (x : EuclideanSpace ℝ κ) (i : ι) :
    toEuclideanLin H x i = ∑ a, H i a * x a := by
  simp [toEuclideanLin, mulVec, dotProduct]

private lemma memLp_coord {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {κ : Type*}
    [Fintype κ] {X : Ω → EuclideanSpace ℝ κ} (hX2 : MemLp X 2 μ) (a : κ) :
    MemLp (fun ω => X ω a) 2 μ :=
  (EuclideanSpace.proj (𝕜 := ℝ) a).comp_memLp' hX2

private lemma memLp_toEuclideanLin {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (H : Matrix ι κ ℝ)
    {X : Ω → EuclideanSpace ℝ κ} (hX2 : MemLp X 2 μ) :
    MemLp (fun ω => toEuclideanLin H (X ω)) 2 μ := by
  have := (LinearMap.toContinuousLinearMap (toEuclideanLin H)).comp_memLp' hX2
  simpa [Function.comp_def] using this

private lemma memLp_two_of_gaussian {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Matrix ι ι ℝ} {Z : Ω → EuclideanSpace ℝ ι}
    (hZ : Measurable Z) (hZlaw : μ.map Z = multivariateGaussian 0 R) : MemLp Z 2 μ := by
  have h : MemLp id 2 (μ.map Z) := hZlaw ▸ IsGaussian.memLp_two_id
  exact (memLp_map_measure_iff aestronglyMeasurable_id hZ.aemeasurable).1 h

private lemma integral_of_gaussian {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Matrix ι ι ℝ} {Z : Ω → EuclideanSpace ℝ ι}
    (hZ : Measurable Z) (hZlaw : μ.map Z = multivariateGaussian 0 R) : ∫ ω, Z ω ∂μ = 0 := by
  calc ∫ ω, Z ω ∂μ = ∫ y, y ∂(μ.map Z) :=
        (integral_map hZ.aemeasurable aestronglyMeasurable_id).symm
    _ = 0 := by rw [hZlaw, integral_id_multivariateGaussian]

private lemma covariance_of_gaussian {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Matrix ι ι ℝ} (hR : R.PosSemidef)
    {Z : Ω → EuclideanSpace ℝ ι} (hZ : Measurable Z)
    (hZlaw : μ.map Z = multivariateGaussian 0 R) (i j : ι) :
    cov[fun ω => Z ω i, fun ω => Z ω j; μ] = R i j := by
  have h := covariance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ ι)) hR i j
  rw [← hZlaw, covariance_map_fun (by fun_prop) (by fun_prop) hZ.aemeasurable] at h
  exact h

/-! ### First and second moments for an arbitrary finite-second-moment input -/

/-- The channel output of a finite-second-moment input has a finite second moment. -/
theorem memLp_two_output {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (H : Matrix ι κ ℝ) {R : Matrix ι ι ℝ} (hR : R.PosSemidef)
    {X : Ω → EuclideanSpace ℝ κ} {Z : Ω → EuclideanSpace ℝ ι} (hZ : Measurable Z)
    (hZlaw : μ.map Z = multivariateGaussian 0 R) (hX2 : MemLp X 2 μ) :
    MemLp (fun ω => toEuclideanLin H (X ω) + Z ω) 2 μ := by
  exact (memLp_toEuclideanLin H hX2).add (memLp_two_of_gaussian hZ hZlaw)

/-- **Output mean**: `E[H X + Z] = H m`. -/
theorem integral_output {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (H : Matrix ι κ ℝ) {R : Matrix ι ι ℝ} (hR : R.PosSemidef)
    {X : Ω → EuclideanSpace ℝ κ} {Z : Ω → EuclideanSpace ℝ ι} (hZ : Measurable Z)
    (hZlaw : μ.map Z = multivariateGaussian 0 R) (hX2 : MemLp X 2 μ)
    {m : EuclideanSpace ℝ κ} (hm : ∫ ω, X ω ∂μ = m) :
    ∫ ω, (toEuclideanLin H (X ω) + Z ω) ∂μ = toEuclideanLin H m := by
  have hint : Integrable X μ := hX2.integrable one_le_two
  rw [integral_add ((memLp_toEuclideanLin H hX2).integrable one_le_two)
    ((memLp_two_of_gaussian hZ hZlaw).integrable one_le_two), integral_of_gaussian hZ hZlaw,
    add_zero, ← hm]
  have := (LinearMap.toContinuousLinearMap (toEuclideanLin H)).integral_comp_comm hint
  simpa using this

/-- **Output covariance**: `Cov(H X + Z) = H K Hᵀ + R`, entrywise, for `Z ~ N(0, R)` independent
of an arbitrary finite-second-moment input with covariance `K`. -/
theorem covariance_output {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (H : Matrix ι κ ℝ) {R : Matrix ι ι ℝ} (hR : R.PosSemidef)
    {X : Ω → EuclideanSpace ℝ κ} {Z : Ω → EuclideanSpace ℝ ι} (hX : Measurable X)
    (hZ : Measurable Z) (hind : IndepFun X Z μ) (hZlaw : μ.map Z = multivariateGaussian 0 R)
    (hX2 : MemLp X 2 μ) {K : Matrix κ κ ℝ}
    (hK : ∀ a b, cov[fun ω => X ω a, fun ω => X ω b; μ] = K a b) (i j : ι) :
    cov[fun ω => (toEuclideanLin H (X ω) + Z ω) i,
        fun ω => (toEuclideanLin H (X ω) + Z ω) j; μ] = (H * K * Hᵀ + R) i j := by
  set U : ι → Ω → ℝ := fun i ω => ∑ a, H i a * X ω a with hUdef
  have hY : ∀ i, (fun ω => (toEuclideanLin H (X ω) + Z ω) i) = U i + fun ω => Z ω i := by
    intro i
    funext ω
    simp [U, coord_toEuclideanLin]
  have hXa : ∀ a, MemLp (fun ω => X ω a) 2 μ := fun a => memLp_coord hX2 a
  have hU : ∀ i, MemLp (U i) 2 μ := fun i =>
    memLp_finsetSum _ fun a _ => (hXa a).const_mul (H i a)
  have hZ2 := memLp_two_of_gaussian hZ hZlaw
  have hZi : ∀ i, MemLp (fun ω => Z ω i) 2 μ := fun i => memLp_coord hZ2 i
  have hind' : ∀ i j, IndepFun (U i) (fun ω => Z ω j) μ := fun i j =>
    hind.comp (φ := fun x : EuclideanSpace ℝ κ => ∑ a, H i a * x a)
      (ψ := fun z : EuclideanSpace ℝ ι => z j) (by fun_prop) (by fun_prop)
  rw [hY i, hY j, covariance_add_left (hU i) (hZi i) ((hU j).add (hZi j)),
    covariance_add_right (hU i) (hU j) (hZi j), covariance_add_right (hZi i) (hU j) (hZi j),
    (hind' i j).covariance_eq_zero (hU i) (hZi j),
    (hind' j i).symm.covariance_eq_zero (hZi i) (hU j), covariance_of_gaussian hR hZ hZlaw,
    add_zero, zero_add, Matrix.add_apply]
  congr 1
  simp only [U]
  rw [covariance_fun_sum_fun_sum (X := fun a ω => H i a * X ω a)
    (Y := fun b ω => H j b * X ω b) (fun a => (hXa a).const_mul _) (fun b => (hXa b).const_mul _)]
  simp only [covariance_const_mul_left, covariance_const_mul_right, hK]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  ring

/-- **Total second moment**: `trace K + ‖m‖² = E‖X‖²`. -/
theorem trace_add_norm_sq_eq_integral_norm_sq {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {κ : Type*} [Fintype κ]
    {X : Ω → EuclideanSpace ℝ κ} (hX2 : MemLp X 2 μ) {m : EuclideanSpace ℝ κ}
    (hm : ∫ ω, X ω ∂μ = m) {K : Matrix κ κ ℝ}
    (hK : ∀ a b, cov[fun ω => X ω a, fun ω => X ω b; μ] = K a b) :
    K.trace + ‖m‖ ^ 2 = ∫ ω, ‖X ω‖ ^ 2 ∂μ := by
  have hint : Integrable X μ := hX2.integrable one_le_two
  have hXa : ∀ a, MemLp (fun ω => X ω a) 2 μ := fun a => memLp_coord hX2 a
  have hma : ∀ a, m a = ∫ ω, X ω a ∂μ := by
    intro a
    rw [← hm]
    have := (EuclideanSpace.proj (𝕜 := ℝ) a).integral_comp_comm hint
    simpa using this.symm
  have hKa : ∀ a, K a a = ∫ ω, X ω a ^ 2 ∂μ - m a ^ 2 := by
    intro a
    rw [← hK, covariance_eq_sub (hXa a) (hXa a), hma]
    simp [pow_two]
  have hn : ∀ x : EuclideanSpace ℝ κ, ‖x‖ ^ 2 = ∑ a, x a ^ 2 := fun x => by
    simp [EuclideanSpace.norm_sq_eq]
  simp_rw [hn]
  rw [integral_finsetSum _ fun a _ => (hXa a).integrable_sq, Matrix.trace]
  simp only [Matrix.diag_apply, hKa, Finset.sum_sub_distrib]
  ring

/-- Under the power constraint, the second-moment budget reads `trace K + ‖m‖² ≤ P`. -/
theorem trace_add_norm_sq_le_of_powerConstraint {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {κ : Type*} [Fintype κ]
    {X : Ω → EuclideanSpace ℝ κ} (hX : Measurable X) {P : ℝ} (hpow : PowerConstraint μ X P)
    {m : EuclideanSpace ℝ κ} (hm : ∫ ω, X ω ∂μ = m) {K : Matrix κ κ ℝ}
    (hK : ∀ a b, cov[fun ω => X ω a, fun ω => X ω b; μ] = K a b) :
    K.trace + ‖m‖ ^ 2 ≤ P := by
  rw [trace_add_norm_sq_eq_integral_norm_sq
    (PowerConstraint.memLp_two hpow hX.aestronglyMeasurable) hm hK]
  exact PowerConstraint.integral_norm_sq_le hpow hX.aestronglyMeasurable

/-! ### Validation statements -/

/-- The covariance matrix of a finite-second-moment vector is positive semidefinite (it may be
singular). -/
theorem posSemidef_of_covariance {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {κ : Type*} [Fintype κ] {X : Ω → EuclideanSpace ℝ κ}
    (hX2 : MemLp X 2 μ) {K : Matrix κ κ ℝ}
    (hK : ∀ a b, cov[fun ω => X ω a, fun ω => X ω b; μ] = K a b) : K.PosSemidef := by
  have hXa : ∀ a, MemLp (fun ω => X ω a) 2 μ := fun a => memLp_coord hX2 a
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext a b
    simp only [conjTranspose_apply, star_trivial, ← hK]
    exact covariance_comm _ _
  · have hq : star x ⬝ᵥ K *ᵥ x = cov[fun ω => ∑ a, x a * X ω a, fun ω => ∑ b, x b * X ω b; μ] := by
      rw [covariance_fun_sum_fun_sum (X := fun a ω => x a * X ω a)
        (Y := fun b ω => x b * X ω b) (fun a => (hXa a).const_mul _)
        (fun b => (hXa b).const_mul _)]
      simp only [covariance_const_mul_left, covariance_const_mul_right, hK]
      simp only [dotProduct, mulVec, star_trivial, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [hq, covariance]
    exact integral_nonneg fun ω => mul_self_nonneg _

/-- Positive-definite noise keeps the output covariance positive definite for every channel
matrix, including rank-deficient `H` and singular `K`. -/
theorem posDef_output_covariance {ι κ : Type*} [Fintype ι] [Fintype κ] (H : Matrix ι κ ℝ)
    {K : Matrix κ κ ℝ} (hK : K.PosSemidef) {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    (H * K * Hᵀ + R).PosDef := by
  have h1 : (H * K * Hᵀ).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hK.mul_mul_conjTranspose_same H
  exact hR.posSemidef_add h1

/-- Nonzero-mean, singular-covariance fixture: a deterministic input `X ≡ c` has mean `c` and
covariance `0`, so the output has mean `H c` and covariance `R`. -/
theorem output_moments_of_const_input {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (H : Matrix ι κ ℝ) {R : Matrix ι ι ℝ} (hR : R.PosSemidef)
    {Z : Ω → EuclideanSpace ℝ ι} (hZ : Measurable Z)
    (hZlaw : μ.map Z = multivariateGaussian 0 R) (c : EuclideanSpace ℝ κ) :
    (∫ ω, (toEuclideanLin H c + Z ω) ∂μ = toEuclideanLin H c) ∧
      (∀ a b, cov[fun _ : Ω => c a, fun _ : Ω => c b; μ] = (0 : Matrix κ κ ℝ) a b) ∧
      ∀ i j, cov[fun ω => (toEuclideanLin H c + Z ω) i,
        fun ω => (toEuclideanLin H c + Z ω) j; μ] = R i j := by
  have hXc : MemLp (fun _ : Ω => c) 2 μ := memLp_const c
  have hK0 : ∀ a b, cov[fun ω => (fun _ : Ω => c) ω a, fun ω => (fun _ : Ω => c) ω b; μ] =
      (0 : Matrix κ κ ℝ) a b := fun a b => by
    simp
  refine ⟨integral_output H hR hZ hZlaw hXc (by simp), hK0, fun i j => ?_⟩
  have := covariance_output H hR measurable_const hZ (indepFun_const_left c Z) hZlaw hXc hK0 i j
  simpa using this

/-! ### The leaf bundle -/

/-- **Linear Gaussian channel: joint law and moments** (the leaf's `l2_correct` bundle), under
exactly the leaf hypotheses: finite dimensions `≥ 1`, real `H`, SPD `R`, `Z ~ N(0, R)` independent
of an arbitrary finite-second-moment input `X` with mean `m` and covariance `K`. Conclusions: the
joint law of `(X, H X + Z)` is `law X ⊗ noiseKernel`; the output has finite second moment, mean
`H m` and covariance `H K Hᵀ + R`; and `trace K + ‖m‖² = E‖X‖²`. -/
theorem linearGaussianChannel_law_and_moments {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] [Fintype κ] [DecidableEq κ] [Nonempty κ] (H : Matrix ι κ ℝ)
    {R : Matrix ι ι ℝ} (hR : R.PosDef) {X : Ω → EuclideanSpace ℝ κ}
    {Z : Ω → EuclideanSpace ℝ ι} (hX : Measurable X) (hZ : Measurable Z)
    (hind : IndepFun X Z μ) (hZlaw : μ.map Z = multivariateGaussian 0 R) (hX2 : MemLp X 2 μ)
    {m : EuclideanSpace ℝ κ} (hm : ∫ ω, X ω ∂μ = m) {K : Matrix κ κ ℝ}
    (hK : ∀ a b, cov[fun ω => X ω a, fun ω => X ω b; μ] = K a b) :
    μ.map (fun ω => (X ω, toEuclideanLin H (X ω) + Z ω)) =
        μ.map X ⊗ₘ MetaMathlibExt.noiseKernel (toEuclideanLin H)
          (MetaMathlibExt.continuous_toEuclideanLin H).measurable
          (multivariateGaussian 0 R) ∧
      MemLp (fun ω => toEuclideanLin H (X ω) + Z ω) 2 μ ∧
      ∫ ω, (toEuclideanLin H (X ω) + Z ω) ∂μ = toEuclideanLin H m ∧
      (∀ i j, cov[fun ω => (toEuclideanLin H (X ω) + Z ω) i,
        fun ω => (toEuclideanLin H (X ω) + Z ω) j; μ] = (H * K * Hᵀ + R) i j) ∧
      K.trace + ‖m‖ ^ 2 = ∫ ω, ‖X ω‖ ^ 2 ∂μ := by
  exact ⟨map_prod_eq_compProd_noiseKernel H hX hZ hind hZlaw,
    memLp_two_output H hR.posSemidef hZ hZlaw hX2,
    integral_output H hR.posSemidef hZ hZlaw hX2 hm,
    covariance_output H hR.posSemidef hX hZ hind hZlaw hX2 hK,
    trace_add_norm_sq_eq_integral_norm_sq hX2 hm hK⟩

end MathlibExt.InformationTheory.LinearGaussianJointLaw
