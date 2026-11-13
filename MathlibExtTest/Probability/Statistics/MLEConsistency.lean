/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MLEConsistency

/-!
# Tests for Wald consistency of the maximum-likelihood estimator

* **Gaussian mean, one parameter.** `ℓ θ x = -(x - θ)² / 2` on `K = [a, b]`. The uniform LLN is
  derived from the strong law (the log-likelihood has rank 3), the population criterion is
  computed, `-E X² / 2 + θ μ - θ² / 2`, and identifiability at the mean `μ ∈ [a, b]` is proved
  from it. The MLE is computed, the sample mean clamped to `[a, b]` (`clampMLE`), and shown to be
  an MLE from the definitions; its almost-sure convergence to `μ` is proved twice, once directly
  from the strong law and continuity of the clamp, once through the consistency theorem.
* **Non-vacuity**: a constant sample on a one-point probability space satisfies every sampling
  hypothesis, so the Gaussian consistency statement applies with no hypothesis left open. The
  instance is degenerate: for a constant sample, independence and identical distribution hold
  trivially. A non-degenerate i.i.d. instance on a product space (`Measure.infinitePi`) is not
  constructed here.
* **Gaussian mean, two parameters (the vector case).** `ℓ θ x = -‖x - θ‖² / 2` on a box in
  `Fin 2 → ℝ`: uniform LLN (rank 4), identifiability, existence of an MLE and its almost-sure
  consistency.
* **Non-identifiable model.** `ℓ θ x = -(x - θ²)² / 2` on `[-1, 1]`: compactness, continuity and
  the uniform LLN hold, identifiability fails (the population criterion is even in `θ`), and
  consistency at `θ₀ = 1/2` is false: with every MLE `est`, `-est` is an MLE too, so not every MLE
  converges to `1/2`.
* **Non-compact parameter set.** On `K = ℝ` (not compact), the criterion
  `Q θ = -θ² / (1 + θ⁴)` is continuous with unique maximizer `0`, the criteria `Qn n` (equal to
  `Q` except `Qn n n = 1 / (n + 1)`) converge to it uniformly, `est n = n` maximizes `Qn n`, and
  `est n` does not converge to `0`. Every hypothesis of Wald's argmax theorem except compactness
  holds and its conclusion fails.
-/

@[expose] public section

open Filter Finset Function MeasureTheory ProbabilityTheory Metric Topology Set

namespace MathlibExtTest.Probability.Statistics.MLEConsistency

open MathlibExt.Probability.Statistics.MLEConsistency

/-! ## Gaussian mean, one parameter -/

/-- The Gaussian log-likelihood of one observation with unit variance, up to an additive
constant: `-(x - θ)² / 2`. -/
noncomputable def gaussLL (θ x : ℝ) : ℝ := -(x - θ) ^ 2 / 2

/-- Coefficients of the rank-3 decomposition of `gaussLL`. -/
noncomputable def gaussA : Fin 3 → ℝ → ℝ := ![fun _ => -1 / 2, fun θ => θ, fun θ => -θ ^ 2 / 2]

/-- Statistics of the rank-3 decomposition of `gaussLL`. -/
noncomputable def gaussG : Fin 3 → ℝ → ℝ := ![fun x => x ^ 2, fun x => x, fun _ => 1]

theorem gaussLL_eq (θ x : ℝ) : gaussLL θ x = ∑ j, gaussA j θ * gaussG j x := by
  simp only [gaussLL, gaussA, gaussG, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem continuous_gaussA (j : Fin 3) : Continuous (gaussA j) := by
  fin_cases j <;> simp [gaussA] <;> fun_prop

theorem measurable_gaussG (j : Fin 3) : Measurable (gaussG j) := by
  fin_cases j <;> simp [gaussG] <;> fun_prop

theorem continuous_gaussLL (x : ℝ) : Continuous fun θ => gaussLL θ x := by
  unfold gaussLL; fun_prop

/-- The sum of the Gaussian log-likelihoods of `n` observations, expanded. -/
theorem sum_gaussLL (x : ℕ → ℝ) (θ : ℝ) (n : ℕ) :
    ∑ i ∈ range n, gaussLL θ (x i) =
      -(∑ i ∈ range n, x i ^ 2) / 2 + θ * ∑ i ∈ range n, x i - n * θ ^ 2 / 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, sum_range_succ, sum_range_succ, ih]
    push_cast
    unfold gaussLL
    ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ}

theorem integrable_gaussG [IsProbabilityMeasure P] (hint1 : Integrable (X 0) P)
    (hint2 : Integrable (fun ω => X 0 ω ^ 2) P) (j : Fin 3) :
    Integrable (fun ω => gaussG j (X 0 ω)) P := by
  fin_cases j
  · simpa [gaussG] using hint2
  · simpa [gaussG] using hint1
  · simp [gaussG]

/-- **Uniform LLN for the Gaussian mean model on `[a, b]`**, derived from the strong law. -/
theorem gauss_uniformLLNOn [IsProbabilityMeasure P] (a b : ℝ) (hint1 : Integrable (X 0) P)
    (hint2 : Integrable (fun ω => X 0 ω ^ 2) P) (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) : UniformLLNOn P (Icc a b) gaussLL X :=
  uniformLLNOn_of_finiteRank_of_continuousOn isCompact_Icc gaussA gaussG gaussLL_eq
    (fun j => (continuous_gaussA j).continuousOn) measurable_gaussG
    (integrable_gaussG hint1 hint2) hindep hident

/-- The Gaussian population criterion: `-E X² / 2 + θ μ - θ² / 2`. -/
theorem gauss_popCrit [IsProbabilityMeasure P] (hint1 : Integrable (X 0) P)
    (hint2 : Integrable (fun ω => X 0 ω ^ 2) P) (θ : ℝ) :
    popCrit P gaussLL X θ = -(∫ ω, X 0 ω ^ 2 ∂P) / 2 + θ * ∫ ω, X 0 ω ∂P - θ ^ 2 / 2 := by
  rw [popCrit_eq_sum_of_finiteRank gaussA gaussG gaussLL_eq (integrable_gaussG hint1 hint2)]
  simp only [gaussA, gaussG, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, integral_const, probReal_univ,
    smul_eq_mul]
  ring

/-- **Identifiability of the Gaussian mean**: the population criterion has the unique maximizer
`μ = E X` on `[a, b]` when `μ ∈ [a, b]`. -/
theorem gauss_isIdentifiedOn [IsProbabilityMeasure P] {a b : ℝ} (hint1 : Integrable (X 0) P)
    (hint2 : Integrable (fun ω => X 0 ω ^ 2) P) (hμ : ∫ ω, X 0 ω ∂P ∈ Icc a b) :
    IsIdentifiedOn (Icc a b) (popCrit P gaussLL X) (∫ ω, X 0 ω ∂P) := by
  refine ⟨hμ, fun θ _ hne => ?_⟩
  rw [gauss_popCrit hint1 hint2, gauss_popCrit hint1 hint2]
  nlinarith [sq_pos_of_ne_zero (sub_ne_zero.2 hne)]

/-- **Consistency of every MLE of the Gaussian mean on `[a, b]`**, through the theorem. -/
theorem gauss_ae_tendsto [IsProbabilityMeasure P] {a b : ℝ} (hint1 : Integrable (X 0) P)
    (hint2 : Integrable (fun ω => X 0 ω ^ 2) P) (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (hμ : ∫ ω, X 0 ω ∂P ∈ Icc a b)
    {est : ℕ → Ω → ℝ} (hest : IsMLEOn (Icc a b) gaussLL X est) :
    ∀ᵐ ω ∂P, Tendsto (fun n => est n ω) atTop (𝓝 (∫ ω, X 0 ω ∂P)) :=
  ae_tendsto_of_isMLEOn isCompact_Icc (fun x => (continuous_gaussLL x).continuousOn)
    (gauss_isIdentifiedOn hint1 hint2 hμ) (gauss_uniformLLNOn a b hint1 hint2 hindep hident) hest

/-- The sample mean of the first `n` observations. -/
noncomputable def sampleMean (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i ∈ range n, X i ω

/-- The **computed MLE** of the Gaussian mean on `[a, b]`: the sample mean clamped to `[a, b]`. -/
noncomputable def clampMLE (a b : ℝ) (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  max a (min b (sampleMean X n ω))

/-- Clamping to `[a, b]` is the nearest point of `[a, b]`. -/
theorem clamp_sub_sq_le {a b θ x : ℝ} (hab : a ≤ b) (hθ : θ ∈ Icc a b) :
    (max a (min b x) - x) ^ 2 ≤ (θ - x) ^ 2 := by
  obtain ⟨h1, h2⟩ := hθ
  rcases le_total x a with hxa | hax
  · rw [min_eq_right (hxa.trans hab), max_eq_left hxa]
    nlinarith
  · rcases le_total x b with hxb | hbx
    · rw [min_eq_right hxb, max_eq_right hax, sub_self]
      nlinarith [sq_nonneg (θ - x)]
    · rw [min_eq_left hbx, max_eq_right hab]
      nlinarith

omit [MeasurableSpace Ω] in
/-- **The clamped sample mean is an MLE** of the Gaussian mean on `[a, b]`, from the
definitions. -/
theorem isMLEOn_clampMLE {a b : ℝ} (hab : a ≤ b) (X : ℕ → Ω → ℝ) :
    IsMLEOn (Icc a b) gaussLL X (clampMLE a b X) := by
  intro n ω
  refine ⟨⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩, fun θ hθ => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [avgLogLik]
  set xbar := sampleMean X n ω
  set c := clampMLE a b X n ω
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have havg : ∀ t, avgLogLik gaussLL X n ω t =
      (n : ℝ)⁻¹ * (-(∑ i ∈ range n, X i ω ^ 2) / 2) + t * xbar - t ^ 2 / 2 := by
    intro t
    simp only [avgLogLik, sum_gaussLL (fun i => X i ω), xbar, sampleMean]
    field_simp
  have key : (c - xbar) ^ 2 ≤ (θ - xbar) ^ 2 := clamp_sub_sq_le hab hθ
  rw [havg, havg]
  nlinarith [key]

/-- **The computed MLE converges almost surely to the mean**, directly from the strong law and
continuity of the clamp (not through the consistency theorem). -/
theorem ae_tendsto_clampMLE {a b : ℝ} (hint1 : Integrable (X 0) P)
    (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hμ : ∫ ω, X 0 ω ∂P ∈ Icc a b) :
    ∀ᵐ ω ∂P, Tendsto (fun n => clampMLE a b X n ω) atTop (𝓝 (∫ ω, X 0 ω ∂P)) := by
  filter_upwards [strong_law_ae X hint1 hindep hident] with ω hω
  have hclamp : max a (min b (∫ ω, X 0 ω ∂P)) = ∫ ω, X 0 ω ∂P := by
    rw [min_eq_right hμ.2, max_eq_right hμ.1]
  have hcont : Continuous fun x : ℝ => max a (min b x) := by fun_prop
  have := (hcont.tendsto _).comp hω
  rw [hclamp] at this
  simpa [clampMLE, sampleMean, Function.comp_def, smul_eq_mul] using this

/-- The computed MLE is consistent through the theorem too. -/
theorem ae_tendsto_clampMLE' [IsProbabilityMeasure P] {a b : ℝ} (hab : a ≤ b)
    (hint1 : Integrable (X 0) P) (hint2 : Integrable (fun ω => X 0 ω ^ 2) P)
    (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hμ : ∫ ω, X 0 ω ∂P ∈ Icc a b) :
    ∀ᵐ ω ∂P, Tendsto (fun n => clampMLE a b X n ω) atTop (𝓝 (∫ ω, X 0 ω ∂P)) :=
  gauss_ae_tendsto hint1 hint2 hindep hident hμ (isMLEOn_clampMLE hab X)

/-! ## Non-vacuity: a constant sample -/

/-- **Non-vacuity**: the constant sample `X i = c` on a one-point probability space satisfies every
sampling hypothesis of `gauss_ae_tendsto`, its mean is `c`, and the computed MLE on `[c - 1, c + 1]`
converges almost surely to `c` by the consistency theorem. The instance is degenerate: for a
constant sample, independence and identical distribution hold trivially. A non-degenerate i.i.d.
instance on a product space (`Measure.infinitePi`) is not constructed here. -/
theorem gauss_constant_sample (c : ℝ) :
    let P : Measure Unit := Measure.dirac ()
    let X : ℕ → Unit → ℝ := fun _ _ => c
    Integrable (X 0) P ∧ Integrable (fun ω => X 0 ω ^ 2) P ∧ Pairwise ((· ⟂ᵢ[P] ·) on X) ∧
      (∀ i, IdentDistrib (X i) (X 0) P P) ∧ ∫ ω, X 0 ω ∂P = c ∧
      ∀ᵐ ω ∂P, Tendsto (fun n => clampMLE (c - 1) (c + 1) X n ω) atTop (𝓝 c) := by
  intro P X
  have h1 : Integrable (X 0) P := integrable_const c
  have h2 : Integrable (fun ω => X 0 ω ^ 2) P := integrable_const (c ^ 2)
  have h3 : Pairwise ((· ⟂ᵢ[P] ·) on X) := fun i j _ => indepFun_const_left c _
  have h4 : ∀ i, IdentDistrib (X i) (X 0) P P := fun _ => IdentDistrib.refl aemeasurable_const
  have h5 : ∫ ω, X 0 ω ∂P = c := by simp [X, P]
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  have hμ : ∫ ω, X 0 ω ∂P ∈ Icc (c - 1) (c + 1) := by rw [h5]; constructor <;> linarith
  have := ae_tendsto_clampMLE' (by linarith) h1 h2 h3 h4 hμ
  rwa [h5] at this

/-! ## Gaussian mean, two parameters (the vector case) -/

/-- The bivariate Gaussian log-likelihood with identity covariance, up to an additive constant:
`-((x₀ - θ₀)² + (x₁ - θ₁)²) / 2`. -/
noncomputable def gauss2LL (θ x : Fin 2 → ℝ) : ℝ := -((x 0 - θ 0) ^ 2 + (x 1 - θ 1) ^ 2) / 2

/-- Coefficients of the rank-4 decomposition of `gauss2LL`. -/
noncomputable def gauss2A : Fin 4 → (Fin 2 → ℝ) → ℝ :=
  ![fun _ => -1 / 2, fun θ => θ 0, fun θ => θ 1, fun θ => -(θ 0 ^ 2 + θ 1 ^ 2) / 2]

/-- Statistics of the rank-4 decomposition of `gauss2LL`. -/
noncomputable def gauss2G : Fin 4 → (Fin 2 → ℝ) → ℝ :=
  ![fun x => x 0 ^ 2 + x 1 ^ 2, fun x => x 0, fun x => x 1, fun _ => 1]

theorem gauss2LL_eq (θ x : Fin 2 → ℝ) : gauss2LL θ x = ∑ j, gauss2A j θ * gauss2G j x := by
  simp only [gauss2LL, gauss2A, gauss2G, Fin.sum_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons]
  ring

theorem continuous_gauss2A (j : Fin 4) : Continuous (gauss2A j) := by
  fin_cases j <;> simp [gauss2A] <;> fun_prop

theorem measurable_gauss2G (j : Fin 4) : Measurable (gauss2G j) := by
  fin_cases j <;> simp [gauss2G] <;> fun_prop

theorem continuous_gauss2LL (x : Fin 2 → ℝ) : Continuous fun θ => gauss2LL θ x := by
  unfold gauss2LL; fun_prop

variable {Y : ℕ → Ω → Fin 2 → ℝ}

theorem integrable_gauss2G [IsProbabilityMeasure P] (hint1 : ∀ k, Integrable (fun ω => Y 0 ω k) P)
    (hint2 : ∀ k, Integrable (fun ω => Y 0 ω k ^ 2) P) (j : Fin 4) :
    Integrable (fun ω => gauss2G j (Y 0 ω)) P := by
  fin_cases j
  · simp only [gauss2G]
    exact (hint2 0).add (hint2 1)
  · simpa [gauss2G] using hint1 0
  · simpa [gauss2G] using hint1 1
  · simp [gauss2G]

/-- The mean vector `(E Y₀, E Y₁)`. -/
noncomputable def mean2 (P : Measure Ω) (Y : ℕ → Ω → Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun k => ∫ ω, Y 0 ω k ∂P

theorem gauss2_popCrit [IsProbabilityMeasure P] (hint1 : ∀ k, Integrable (fun ω => Y 0 ω k) P)
    (hint2 : ∀ k, Integrable (fun ω => Y 0 ω k ^ 2) P) (θ : Fin 2 → ℝ) :
    popCrit P gauss2LL Y θ = -(∫ ω, (Y 0 ω 0 ^ 2 + Y 0 ω 1 ^ 2) ∂P) / 2 +
      θ 0 * mean2 P Y 0 + θ 1 * mean2 P Y 1 - (θ 0 ^ 2 + θ 1 ^ 2) / 2 := by
  rw [popCrit_eq_sum_of_finiteRank gauss2A gauss2G gauss2LL_eq (integrable_gauss2G hint1 hint2)]
  simp only [gauss2A, gauss2G, mean2, Fin.sum_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, integral_const, probReal_univ, smul_eq_mul]
  ring

/-- **Identifiability of the bivariate Gaussian mean** on a box containing the mean vector. -/
theorem gauss2_isIdentifiedOn [IsProbabilityMeasure P] {l u : Fin 2 → ℝ}
    (hint1 : ∀ k, Integrable (fun ω => Y 0 ω k) P)
    (hint2 : ∀ k, Integrable (fun ω => Y 0 ω k ^ 2) P) (hμ : mean2 P Y ∈ Icc l u) :
    IsIdentifiedOn (Icc l u) (popCrit P gauss2LL Y) (mean2 P Y) := by
  refine ⟨hμ, fun θ _ hne => ?_⟩
  rw [gauss2_popCrit hint1 hint2, gauss2_popCrit hint1 hint2]
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
  fin_cases k
  · have hk' : θ 0 ≠ mean2 P Y 0 := hk
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero.2 hk'), sq_nonneg (θ 1 - mean2 P Y 1)]
  · have hk' : θ 1 ≠ mean2 P Y 1 := hk
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero.2 hk'), sq_nonneg (θ 0 - mean2 P Y 0)]

/-- **Wald consistency of the bivariate Gaussian MLE**: on a box `[l, u]` in `Fin 2 → ℝ`
containing the mean vector, an MLE exists, and every MLE converges almost surely to the mean
vector. The uniform LLN and identifiability are derived, not assumed. -/
theorem gauss2_consistency [IsProbabilityMeasure P] {l u : Fin 2 → ℝ}
    (hint1 : ∀ k, Integrable (fun ω => Y 0 ω k) P)
    (hint2 : ∀ k, Integrable (fun ω => Y 0 ω k ^ 2) P) (hindep : Pairwise ((· ⟂ᵢ[P] ·) on Y))
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) P P) (hμ : mean2 P Y ∈ Icc l u) :
    (∃ est : ℕ → Ω → Fin 2 → ℝ, IsMLEOn (Icc l u) gauss2LL Y est) ∧
      ∀ est : ℕ → Ω → Fin 2 → ℝ, IsMLEOn (Icc l u) gauss2LL Y est →
        ∀ᵐ ω ∂P, Tendsto (fun n => est n ω) atTop (𝓝 (mean2 P Y)) := by
  have hcont : ∀ x, ContinuousOn (fun θ => gauss2LL θ x) (Icc l u) := fun x =>
    (continuous_gauss2LL x).continuousOn
  refine ⟨exists_isMLEOn isCompact_Icc ⟨_, hμ⟩ hcont Y, fun est hest => ?_⟩
  exact ae_tendsto_of_isMLEOn isCompact_Icc hcont (gauss2_isIdentifiedOn hint1 hint2 hμ)
    (uniformLLNOn_of_finiteRank_of_continuousOn isCompact_Icc gauss2A gauss2G gauss2LL_eq
      (fun j => (continuous_gauss2A j).continuousOn) measurable_gauss2G
      (integrable_gauss2G hint1 hint2) hindep hident) hest

/-! ## A non-identifiable model -/

/-- A model identified only up to sign: `ℓ θ x = -(x - θ²)² / 2`, the Gaussian log-likelihood with
mean `θ²`. -/
noncomputable def sqLL (θ x : ℝ) : ℝ := gaussLL (θ ^ 2) x

theorem continuous_sqLL (x : ℝ) : Continuous fun θ => sqLL θ x := by
  unfold sqLL gaussLL; fun_prop

/-- Every condition except identifiability holds: the uniform LLN for `sqLL` on `[-1, 1]`. -/
theorem sq_uniformLLNOn [IsProbabilityMeasure P] (hint1 : Integrable (X 0) P)
    (hint2 : Integrable (fun ω => X 0 ω ^ 2) P) (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) : UniformLLNOn P (Icc (-1) 1) sqLL X :=
  uniformLLNOn_of_finiteRank_of_continuousOn isCompact_Icc (fun j θ => gaussA j (θ ^ 2)) gaussG
    (fun θ x => gaussLL_eq (θ ^ 2) x)
    (fun j => ((continuous_gaussA j).comp (continuous_pow 2)).continuousOn) measurable_gaussG
    (integrable_gaussG hint1 hint2) hindep hident

/-- The population criterion of `sqLL` is even in `θ`, from the definitions. -/
theorem popCrit_sqLL_neg (P : Measure Ω) (X : ℕ → Ω → ℝ) (θ : ℝ) :
    popCrit P sqLL X (-θ) = popCrit P sqLL X θ := by
  simp [popCrit, sqLL]

/-- **Identifiability fails**: `1/2` is not the unique maximizer on `[-1, 1]`, since `-1/2`
gives the same value. -/
theorem not_isIdentifiedOn_sqLL (P : Measure Ω) (X : ℕ → Ω → ℝ) :
    ¬ IsIdentifiedOn (Icc (-1) 1) (popCrit P sqLL X) (1 / 2) := by
  rintro ⟨-, h⟩
  have hlt := h (-(1 / 2)) ⟨by norm_num, by norm_num⟩ (by norm_num)
  rw [popCrit_sqLL_neg] at hlt
  exact lt_irrefl _ hlt

omit [MeasurableSpace Ω] in
/-- The average log-likelihood of `sqLL` is even in `θ`. -/
theorem avgLogLik_sqLL_neg (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (θ : ℝ) :
    avgLogLik sqLL X n ω (-θ) = avgLogLik sqLL X n ω θ := by
  simp [avgLogLik, sqLL]

/-- **Consistency is not claimed, and is false**: on any nonzero measure, not every MLE of the
non-identifiable model on `[-1, 1]` converges almost surely to `1/2`. If `est` is an MLE, so is
`-est`, and both cannot converge to `1/2`. -/
theorem not_forall_ae_tendsto_sqLL (hP : P ≠ 0) (X : ℕ → Ω → ℝ) :
    ¬ ∀ est : ℕ → Ω → ℝ, IsMLEOn (Icc (-1) 1) sqLL X est →
      ∀ᵐ ω ∂P, Tendsto (fun n => est n ω) atTop (𝓝 (1 / 2)) := by
  intro h
  obtain ⟨est, hest⟩ := exists_isMLEOn (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
    ⟨0, by norm_num, by norm_num⟩ (fun x => (continuous_sqLL x).continuousOn) X
  have hneg : IsMLEOn (Icc (-1) 1) sqLL X fun n ω => -est n ω := by
    intro n ω
    obtain ⟨⟨h1, h2⟩, hmax⟩ := hest n ω
    refine ⟨⟨by linarith, by linarith⟩, fun θ hθ => ?_⟩
    rw [avgLogLik_sqLL_neg]
    exact hmax θ hθ
  have : (ae P).NeBot := ae_neBot.2 hP
  obtain ⟨ω, h1, h2⟩ := ((h est hest).and (h _ hneg)).exists
  have h3 : Tendsto (fun n => est n ω) atTop (𝓝 (-(1 / 2))) := by simpa using h2.neg
  have := tendsto_nhds_unique h1 h3
  norm_num at this

/-! ## A non-compact parameter set -/

/-- A criterion on `ℝ` with unique maximizer `0` that is not well separated: `Q θ → 0 = Q 0` as
`θ → ∞`. -/
noncomputable def flatQ (θ : ℝ) : ℝ := -(θ ^ 2 / (1 + θ ^ 4))

/-- Perturbed criteria: `flatQ`, except for the value `1 / (n + 1)` at `θ = n`. -/
noncomputable def flatQn (n : ℕ) (θ : ℝ) : ℝ := if θ = n then 1 / (n + 1) else flatQ θ

theorem flatQ_nonpos (θ : ℝ) : flatQ θ ≤ 0 := by
  unfold flatQ
  have : 0 ≤ θ ^ 2 / (1 + θ ^ 4) := by positivity
  linarith

theorem continuous_flatQ : Continuous flatQ := by
  unfold flatQ
  exact ((continuous_pow 2).div (continuous_const.add (continuous_pow 4))
    fun x => (by positivity : (0 : ℝ) < 1 + x ^ 4).ne').neg

theorem isIdentifiedOn_flatQ : IsIdentifiedOn univ flatQ 0 := by
  refine ⟨mem_univ _, fun θ _ hθ => ?_⟩
  have : 0 < θ ^ 2 / (1 + θ ^ 4) := by
    have := pow_pos (abs_pos.2 hθ) 2
    rw [sq_abs] at this
    exact div_pos this (by positivity)
  simp only [flatQ]
  norm_num
  linarith

theorem flatQ_natCast_abs_le {n : ℕ} (hn : 1 ≤ n) : |flatQ n| ≤ 1 / n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by linarith
  rw [flatQ, abs_neg, abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) hpos]
  nlinarith [pow_pos hpos 3, mul_le_mul_of_nonneg_left hn' (le_of_lt (pow_pos hpos 3))]

theorem tendstoUniformlyOn_flatQn : TendstoUniformlyOn flatQn flatQ atTop univ := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).eventually (gt_mem_nhds hε),
    eventually_ge_atTop 1] with n hn hn1 θ _
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn1
  by_cases hθ : θ = n
  · subst hθ
    simp only [flatQn, ite_true, Real.dist_eq]
    have h1 : |(1 : ℝ) / (n + 1)| ≤ 1 / n := by
      rw [abs_of_nonneg (by positivity)]
      exact one_div_le_one_div_of_le hpos (by linarith)
    calc |flatQ n - 1 / (n + 1)| ≤ |flatQ n| + |(1 : ℝ) / (n + 1)| := abs_sub _ _
      _ ≤ 1 / n + 1 / n := add_le_add (flatQ_natCast_abs_le hn1) h1
      _ = 2 / n := by ring
      _ < ε := hn
  · simp only [flatQn, hθ, ite_false, dist_self]
    exact hε

theorem flatQn_le (n : ℕ) (θ : ℝ) : flatQn n θ ≤ flatQn n n := by
  simp only [flatQn, ite_true]
  split_ifs
  · exact le_rfl
  · exact (flatQ_nonpos θ).trans (by positivity)

/-- **Compactness cannot be dropped from Wald's argmax theorem.** On the non-compact set
`K = ℝ`, `flatQ` is continuous with unique maximizer `0`, `flatQn n → flatQ` uniformly,
`est n = n` maximizes `flatQn n`, and yet `est n` does not converge to `0`. -/
theorem wald_fails_without_compactness :
    ¬ IsCompact (univ : Set ℝ) ∧ UpperSemicontinuousOn flatQ univ ∧
      IsIdentifiedOn univ flatQ 0 ∧ TendstoUniformlyOn flatQn flatQ atTop univ ∧
      (∀ n θ, flatQn n θ ≤ flatQn n n) ∧ ¬ Tendsto (fun n : ℕ => (n : ℝ)) atTop (𝓝 0) :=
  ⟨noncompact_univ ℝ, continuous_flatQ.continuousOn.upperSemicontinuousOn, isIdentifiedOn_flatQ,
    tendstoUniformlyOn_flatQn, flatQn_le,
    not_tendsto_nhds_of_tendsto_atTop tendsto_natCast_atTop_atTop 0⟩

end MathlibExtTest.Probability.Statistics.MLEConsistency
