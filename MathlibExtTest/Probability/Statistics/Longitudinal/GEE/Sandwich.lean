/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Longitudinal.GEE.Sandwich
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.StrongLaw

/-!
# Tests for GEE asymptotics and the sandwich covariance

* Smoke test: `sandwichCovariance 1 1 = 1`.
* Scalar sandwich: `sandwichCovariance (c • 1) (d • 1) = (d / c²) • 1` for `c ≠ 0`.
* A concrete independent-cluster model, the Gaussian random-intercept model
  `Y i j = β₀ + b i + e i j`, `j = 1, 2`, with `b i, e i 1, e i 2` independent standard normals,
  fitted by GEE with identity link and working independence (`D i = (1, 1)ᵀ`, `V i = I`). The
  estimator is the grand mean, the bread is `A = -2`, the meat is `B = Var(U i β₀) = 6`, and the
  sandwich is `3 / 2 = Var((Y i 1 + Y i 2) / 2)` (`sandwichCovariance_A_B`). The
  working-independence model-based variance `(Dᵀ V⁻¹ D)⁻¹ = 1/2` for `V i = I` is
  mentioned for comparison only; it is not formalized. In this model every hypothesis is
  discharged for:
  - (a) `tendstoInMeasure_of_tendstoUniformlyOn_of_root` (`tendstoInMeasure_βhat`), with
    `g β = 2 (β₀ - β)` on `closedBall β₀ 1` and uniform convergence from the strong law;
  - (b) `tendstoInDistribution_sqrt_smul_sub_sandwich` with the exact linearization
    (`tendstoInDistribution_randomIntercept`) and
    `tendstoInDistribution_sqrt_smul_sub_sandwich_of_hasFDerivAt`, hence
    `linearization_of_hasFDerivAt` (`tendstoInDistribution_randomIntercept_of_hasFDerivAt`); the
    cluster Lindeberg condition comes from `lindebergConditionTriangular_inner_of_identDistrib`;
  - (c) `tendstoInMeasure_empirical_sandwichCovariance_of_eq`, hence
    `tendstoInMeasure_empirical_sandwichCovariance` and `tendstoInMeasure_sandwichCovariance`
    (`tendstoInMeasure_empirical_sandwich_randomIntercept`), with meat limit
    `Bbar β = (6 + 4 (β₀ - β)²) • 1` from two strong-law applications and `Bbar β₀ = B`.

  The model is realized on an infinite product space.
* Boundary: a singular bread. With `A = 0`, deterministic bread estimators `Ahat n → 0` and meat
  `1` give sandwiches `(n + 1)² • 1` that do not converge to `sandwichCovariance 0 1 = 0`: the
  invertibility hypothesis of `tendstoInMeasure_sandwichCovariance` cannot be dropped.
* Boundary: Lindeberg failure. Exploding cluster scores `U k = 2 ^ k` violate the cluster
  Lindeberg condition, so the hypothesis is not vacuous.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory ProbabilityTheory.GEE Filter Finset RealInnerProductSpace
open scoped Real Topology

namespace GEESandwichTest

/-! ### Smoke test -/

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    sandwichCovariance (1 : E →L[ℝ] E) 1 = 1 := by
  have hsym : symmetrizedMeat (1 : E →L[ℝ] E) = 1 := by
    rw [symmetrizedMeat, ContinuousLinearMap.adjoint_one, ← two_smul ℝ (1 : E →L[ℝ] E),
      smul_smul]
    norm_num
  rw [sandwichCovariance, hsym, Ring.inverse_one, mul_one, one_mul,
    ContinuousLinearMap.one_def, ContinuousLinearMap.adjoint_id]

/-- The sandwich is self-adjoint for every meat, and depends on the meat only through its
symmetrization. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (A B : E →L[ℝ] E) :
    IsSelfAdjoint (sandwichCovariance A B) ∧
      sandwichCovariance A (symmetrizedMeat B) = sandwichCovariance A B :=
  ⟨isSelfAdjoint_sandwichCovariance A B, sandwichCovariance_symmetrizedMeat A B⟩

/-! ### Scalar sandwich -/

/-- In one dimension the sandwich of `c • 1` and `d • 1` is `d / c²`. -/
theorem sandwichCovariance_smul_one (c d : ℝ) (hc : c ≠ 0) :
    sandwichCovariance (c • (1 : ℝ →L[ℝ] ℝ)) (d • 1) = (d / c ^ 2) • 1 := by
  have hinv : Ring.inverse (c • (1 : ℝ →L[ℝ] ℝ)) = c⁻¹ • 1 := by
    have hu : IsUnit (c • (1 : ℝ →L[ℝ] ℝ)) :=
      ⟨⟨c • 1, c⁻¹ • 1, by rw [smul_mul_smul_comm, mul_one, mul_inv_cancel₀ hc, one_smul],
        by rw [smul_mul_smul_comm, mul_one, inv_mul_cancel₀ hc, one_smul]⟩, rfl⟩
    have h1 : Ring.inverse (c • (1 : ℝ →L[ℝ] ℝ)) * (c • 1) = 1 := Ring.inverse_mul_cancel _ hu
    calc Ring.inverse (c • (1 : ℝ →L[ℝ] ℝ))
        = Ring.inverse (c • (1 : ℝ →L[ℝ] ℝ)) * ((c • 1) * (c⁻¹ • 1)) := by
          rw [smul_mul_smul_comm, mul_one, mul_inv_cancel₀ hc, one_smul, mul_one]
      _ = c⁻¹ • 1 := by rw [← mul_assoc, h1, one_mul]
  have hadj : ContinuousLinearMap.adjoint (c⁻¹ • (1 : ℝ →L[ℝ] ℝ)) = c⁻¹ • 1 := by
    rw [map_smulₛₗ, ContinuousLinearMap.one_def, ContinuousLinearMap.adjoint_id]
    simp
  have hsym : symmetrizedMeat (d • (1 : ℝ →L[ℝ] ℝ)) = d • 1 := by
    have hadjB : ContinuousLinearMap.adjoint (d • (1 : ℝ →L[ℝ] ℝ)) = d • 1 := by
      rw [map_smulₛₗ, ContinuousLinearMap.one_def, ContinuousLinearMap.adjoint_id]
      simp
    rw [symmetrizedMeat, hadjB, ← two_smul ℝ (d • (1 : ℝ →L[ℝ] ℝ)), smul_smul]
    norm_num
  rw [sandwichCovariance, hsym, hinv, hadj]
  ext
  simp
  field_simp

/-! ### The Gaussian random-intercept model under working independence -/

/-- The latent standard Gaussian vector of a cluster: `(b, e 1, e 2)`. -/
abbrev F := EuclideanSpace ℝ (Fin 3)

/-- The loading vector of the cluster score: `U i β₀ = 2 b + e 1 + e 2 = ⟪ξ, s⟫`. -/
noncomputable def s : F := !₂[2, 1, 1]

theorem inner_s (x : F) : ⟪x, s⟫ = 2 * x 0 + x 1 + x 2 := by
  simp [s, PiLp.inner_apply, Fin.sum_univ_three]

theorem norm_s_sq : ‖s‖ ^ 2 = 6 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [s, Fin.sum_univ_three]
  norm_num

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- Response `j ∈ {1, 2}` of cluster `i`: `Y i j = β₀ + b i + e i j`, with
`(b i, e i 1, e i 2) = ξ i`. -/
noncomputable def Y (β₀ : ℝ) (ξ : ℕ → Ω → F) (i : ℕ) (j : Fin 3) (ω : Ω) : ℝ :=
  β₀ + ξ i ω 0 + ξ i ω j

/-- The GEE score of cluster `i` for the identity link under working independence:
`D iᵀ V i⁻¹ (Y i - μ i β) = (Y i 1 - β) + (Y i 2 - β)`. -/
noncomputable def U (β₀ : ℝ) (ξ : ℕ → Ω → F) (i : ℕ) (β : ℝ) (ω : Ω) : ℝ :=
  (Y β₀ ξ i 1 ω - β) + (Y β₀ ξ i 2 ω - β)

/-- The GEE estimator: the grand mean `∑_{i<n} (Y i 1 + Y i 2) / (2 n)`. -/
noncomputable def βhat (β₀ : ℝ) (ξ : ℕ → Ω → F) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ range n, (Y β₀ ξ i 1 ω + Y β₀ ξ i 2 ω)) / (2 * n)

theorem U_eq (β₀ : ℝ) (ξ : ℕ → Ω → F) (i : ℕ) (β : ℝ) (ω : Ω) :
    U β₀ ξ i β ω = ⟪ξ i ω, s⟫ + 2 * (β₀ - β) := by
  rw [inner_s, U, Y, Y]
  ring

theorem U_self (β₀ : ℝ) (ξ : ℕ → Ω → F) (i : ℕ) :
    U β₀ ξ i β₀ = fun ω ↦ ⟪ξ i ω, s⟫ := by
  ext ω
  rw [U_eq, sub_self, mul_zero, add_zero]

theorem sum_U (β₀ : ℝ) (ξ : ℕ → Ω → F) (n : ℕ) (β : ℝ) (ω : Ω) :
    ∑ i ∈ range n, U β₀ ξ i β ω =
      ∑ i ∈ range n, (Y β₀ ξ i 1 ω + Y β₀ ξ i 2 ω) - 2 * n * β := by
  simp only [U]
  rw [show 2 * (n : ℝ) * β = ∑ _i ∈ range n, 2 * β by simp; ring, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- The grand mean solves the GEE estimating equation exactly, for every `n`. -/
theorem sum_U_βhat (β₀ : ℝ) (ξ : ℕ → Ω → F) (n : ℕ) (ω : Ω) :
    ∑ i ∈ range n, U β₀ ξ i (βhat β₀ ξ n ω) ω = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [sum_U, βhat]
  field_simp
  ring

/-- The bread of the model: `A = E[∂U/∂β] = -2`. -/
noncomputable def A : ℝ →L[ℝ] ℝ := (-2 : ℝ) • 1

/-- The meat of the model: `B = E[U²] = Var(2 b + e 1 + e 2) = 6`. -/
noncomputable def B : ℝ →L[ℝ] ℝ := (6 : ℝ) • 1

theorem isUnit_A : IsUnit A :=
  ⟨⟨(-2 : ℝ) • 1, (-2 : ℝ)⁻¹ • 1, by rw [smul_mul_smul_comm, mul_one]; norm_num,
    by rw [smul_mul_smul_comm, mul_one]; norm_num⟩, rfl⟩

/-- **The sandwich of the random-intercept model is `3 / 2`**, the variance of a cluster mean
`(Y i 1 + Y i 2) / 2 = β₀ + b i + (e i 1 + e i 2) / 2`; the working-independence model-based
variance `(Dᵀ V⁻¹ D)⁻¹ = 1/2` for `V i = I` understates it. -/
theorem sandwichCovariance_A_B : sandwichCovariance A B = (3 / 2 : ℝ) • 1 := by
  rw [A, B, sandwichCovariance_smul_one _ _ (by norm_num)]
  norm_num

variable {ξ : ℕ → Ω → F}

omit [IsProbabilityMeasure P] in
theorem integral_inner_s (hlaw : ∀ i, HasLaw (ξ i) (stdGaussian F) P) (k : ℕ) :
    ∫ ω, ⟪ξ k ω, s⟫ ∂P = 0 := by
  have h := (hlaw k).integral_comp (f := fun x : F ↦ ⟪x, s⟫)
    (continuous_id.inner continuous_const).aestronglyMeasurable
  simp only [Function.comp_def] at h
  rw [h, ← integral_strongDual_stdGaussian (E := F) (innerSL ℝ s)]
  exact integral_congr_ae (ae_of_all _ fun x ↦ by simp [real_inner_comm])

omit [IsProbabilityMeasure P] in
theorem integral_inner_s_sq (hlaw : ∀ i, HasLaw (ξ i) (stdGaussian F) P) (k : ℕ) :
    ∫ ω, ⟪ξ k ω, s⟫ ^ 2 ∂P = 6 := by
  have h := (hlaw k).integral_comp (f := fun x : F ↦ ⟪x, s⟫ ^ 2)
    ((continuous_id.inner continuous_const).pow 2).aestronglyMeasurable
  simp only [Function.comp_def] at h
  rw [h]
  have hvar := variance_dual_stdGaussian (E := F) (innerSL ℝ s)
  rw [innerSL_apply_norm, norm_s_sq,
    variance_of_integral_eq_zero (innerSL ℝ s).continuous.aemeasurable
      (integral_strongDual_stdGaussian _)] at hvar
  rw [← hvar]
  exact integral_congr_ae (ae_of_all _ fun x ↦ by simp [real_inner_comm])

theorem inner_real (x t : ℝ) : ⟪x, t⟫ = x * t := by simp [mul_comm]

omit [IsProbabilityMeasure P] in
theorem measurable_βhat (hξ : ∀ i, Measurable (ξ i)) (β₀ : ℝ) (n : ℕ) :
    Measurable (βhat β₀ ξ n) := by
  have hc : ∀ j : Fin 3, Measurable fun x : F ↦ x j := fun j ↦
    (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.measurable
  unfold βhat Y
  exact (Finset.measurable_sum _ fun i _ ↦
    ((measurable_const.add ((hc 0).comp (hξ i))).add ((hc 1).comp (hξ i))).add
      ((measurable_const.add ((hc 0).comp (hξ i))).add ((hc 2).comp (hξ i)))).div_const _

theorem measurable_inner_s : Measurable fun x : F ↦ ⟪x, s⟫ :=
  (continuous_id.inner continuous_const).measurable

section Hypotheses

variable (hξ : ∀ i, Measurable (ξ i)) (hlaw : ∀ i, HasLaw (ξ i) (stdGaussian F) P)
  (hind : iIndepFun ξ P)
include hlaw

omit [IsProbabilityMeasure P] in
theorem memLp_U (β₀ : ℝ) (k : ℕ) : MemLp (U β₀ ξ k β₀) 2 P := by
  rw [U_self]
  exact (hlaw k).memLp_comp (MemLp.inner_const IsGaussian.memLp_two_id s)

omit [IsProbabilityMeasure P] in
theorem identDistrib_U (β₀ : ℝ) (k : ℕ) : IdentDistrib (U β₀ ξ k β₀) (U β₀ ξ 0 β₀) P P := by
  rw [U_self, U_self]
  exact (IdentDistrib.mk (hlaw k).aemeasurable (hlaw 0).aemeasurable
    ((hlaw k).map_eq.trans (hlaw 0).map_eq.symm)).comp measurable_inner_s

omit [IsProbabilityMeasure P] in
/-- The meat: `n⁻¹ ∑_{k<n} E[⟪U k β₀, t⟫²] = 6 t² = ⟪B t, t⟫` for `n ≥ 1`. -/
theorem tendsto_meat (β₀ t : ℝ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, ∫ ω, ⟪U β₀ ξ k β₀ ω, t⟫ ^ 2 ∂P) atTop
      (𝓝 ⟪B t, t⟫) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
  simp only [U_self, inner_real, mul_pow, integral_mul_const, integral_inner_s_sq hlaw,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, B, smul_apply, one_apply_eq_self,
    smul_eq_mul]
  field_simp

omit hlaw in
/-- The limit `N(0, 3/2)` has the projection laws required by the sandwich CLT. -/
theorem hasLaw_limit (t : ℝ) :
    HasLaw (fun x : ℝ ↦ ⟪id x, t⟫) (gaussianReal 0 (⟪sandwichCovariance A B t, t⟫).toNNReal)
      (gaussianReal 0 (3 / 2)) := by
  rw [sandwichCovariance_A_B]
  refine ⟨(continuous_id.inner continuous_const).aemeasurable, ?_⟩
  simp only [id, inner_real, smul_apply, one_apply_eq_self, smul_eq_mul]
  rw [gaussianReal_map_mul_const, mul_zero]
  congr 1
  apply NNReal.eq
  simp only [NNReal.coe_mul, NNReal.coe_mk]
  rw [Real.coe_toNNReal _ (by nlinarith [mul_self_nonneg t])]
  norm_num
  ring

end Hypotheses

/-- **Asymptotic normality of the GEE estimator in the random-intercept model, with the sandwich
variance `3 / 2`**, from `tendstoInDistribution_sqrt_smul_sub_sandwich` with the exact root and
the exact linearization `∑ U i β = ∑ (Y i 1 + Y i 2) - 2 n β` (bread `A = -2`). -/
theorem tendstoInDistribution_randomIntercept (hξ : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, HasLaw (ξ i) (stdGaussian F) P) (hind : iIndepFun ξ P) (β₀ : ℝ) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √n • (βhat β₀ ξ n ω - β₀)) atTop id
      (fun _ ↦ P) (gaussianReal 0 (3 / 2)) := by
  have hrem : ∀ n : ℕ, 1 ≤ n → ∀ ω, (n : ℝ)⁻¹ • (∑ i ∈ range n, U β₀ ξ i (βhat β₀ ξ n ω) ω -
      ∑ i ∈ range n, U β₀ ξ i β₀ ω) - A (βhat β₀ ξ n ω - β₀) = 0 := by
    intro n hn ω
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
    rw [sum_U, sum_U]
    simp only [A, smul_apply, one_apply_eq_self, smul_eq_mul]
    field_simp
    ring
  refine tendstoInDistribution_sqrt_smul_sub_sandwich (A := A) (B := B) isUnit_A
    (fun k ↦ by rw [U_self]; exact measurable_inner_s.comp (hξ k))
    (by simp_rw [U_self]; exact hind.comp (fun _ x ↦ ⟪x, s⟫) fun _ ↦ measurable_inner_s)
    (fun k ↦ by rw [U_self]; exact integral_inner_s hlaw k) (memLp_U hlaw β₀)
    (tendsto_meat hlaw β₀)
    (fun t ↦ lindebergConditionTriangular_inner_of_identDistrib (identDistrib_U hlaw β₀)
      (memLp_U hlaw β₀ 0) t)
    (fun n ↦ (measurable_βhat hξ β₀ n).aemeasurable) ?_ (fun ε hε ↦ ?_) aemeasurable_id
    (hasLaw_limit)
  · simp [sum_U_βhat]
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    refine (measure_mono_null (t := ∅) (fun ω hω ↦ ?_) measure_empty).symm
    simp only [Set.mem_ofPred_eq] at hω
    rw [hrem n hn ω, norm_zero] at hω
    exact absurd hω (not_lt.2 (by positivity))

/-! ### Consistency, differentiable linearization and the empirical sandwich in the model -/

omit [IsProbabilityMeasure P] in
/-- A sequence of events is eventually contained in events of vanishing probability. -/
theorem tendsto_measure_of_eventually_subset {S T : ℕ → Set Ω}
    (hT : Tendsto (fun n ↦ P (T n)) atTop (𝓝 0)) (hST : ∀ᶠ n in atTop, S n ⊆ T n) :
    Tendsto (fun n ↦ P (S n)) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT
    (Eventually.of_forall fun _ ↦ zero_le) (hST.mono fun _ hn ↦ measure_mono hn)

/-- The cluster-score averages `n⁻¹ ∑_{i<n} ⟪ξ i, s⟫` and `n⁻¹ ∑_{i<n} ⟪ξ i, s⟫²`. -/
noncomputable def m1 (ξ : ℕ → Ω → F) (n : ℕ) (ω : Ω) : ℝ := (∑ i ∈ range n, ⟪ξ i ω, s⟫) / n

@[inherit_doc m1]
noncomputable def m2 (ξ : ℕ → Ω → F) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ range n, ⟪ξ i ω, s⟫ ^ 2) / n

/-- Weak law of large numbers for `f (ξ i)`, from the strong law. -/
theorem tendstoInMeasure_avg (hξ : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, HasLaw (ξ i) (stdGaussian F) P) (hind : iIndepFun ξ P) {f : F → ℝ}
    (hf : Measurable f) (hfi : Integrable f (stdGaussian F)) :
    TendstoInMeasure P (fun (n : ℕ) ω ↦ (∑ i ∈ range n, f (ξ i ω)) / n) atTop
      (fun _ ↦ ∫ x, f x ∂(stdGaussian F)) := by
  have hident : ∀ i, IdentDistrib (ξ i) (ξ 0) P P := fun i ↦
    ⟨(hlaw i).aemeasurable, (hlaw 0).aemeasurable, (hlaw i).map_eq.trans (hlaw 0).map_eq.symm⟩
  have h := strong_law_ae_real (fun i ω ↦ f (ξ i ω)) ((hlaw 0).integrable_comp hfi)
    (fun i j hij ↦ (hind.indepFun hij).comp hf hf) fun i ↦ (hident i).comp hf
  have hmean : P[fun ω ↦ f (ξ 0 ω)] = ∫ x, f x ∂(stdGaussian F) :=
    (hlaw 0).integral_comp hf.aestronglyMeasurable
  rw [hmean] at h
  exact tendstoInMeasure_of_tendsto_ae (fun n ↦
    ((Finset.measurable_sum _ fun i _ ↦ hf.comp (hξ i)).div_const _).aestronglyMeasurable) h

theorem tendstoInMeasure_m1 (hξ : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, HasLaw (ξ i) (stdGaussian F) P) (hind : iIndepFun ξ P) :
    TendstoInMeasure P (m1 ξ) atTop (fun _ ↦ 0) := by
  have h := tendstoInMeasure_avg hξ hlaw hind measurable_inner_s
    (MemLp.inner_const IsGaussian.memLp_two_id s |>.integrable one_le_two)
  have h0 : ∫ x, ⟪x, s⟫ ∂(stdGaussian F) = 0 := by
    rw [← integral_strongDual_stdGaussian (E := F) (innerSL ℝ s)]
    exact integral_congr_ae (ae_of_all _ fun x ↦ by simp [real_inner_comm])
  rw [h0] at h
  exact h

theorem tendstoInMeasure_m2 (hξ : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, HasLaw (ξ i) (stdGaussian F) P) (hind : iIndepFun ξ P) :
    TendstoInMeasure P (m2 ξ) atTop (fun _ ↦ 6) := by
  have h := tendstoInMeasure_avg hξ hlaw hind (measurable_inner_s.pow_const 2)
    (MemLp.inner_const IsGaussian.memLp_two_id s).integrable_sq
  have h6 := integral_inner_s_sq (P := stdGaussian F) (ξ := fun _ ↦ id) (fun _ ↦ HasLaw.id) 0
  simp only [id] at h6
  rw [h6] at h
  exact h

theorem avg_U (β₀ : ℝ) (ξ : ℕ → Ω → F) {n : ℕ} (hn : 1 ≤ n) (β : ℝ) (ω : Ω) :
    (n : ℝ)⁻¹ • ∑ i ∈ range n, U β₀ ξ i β ω = m1 ξ n ω + 2 * (β₀ - β) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
  simp only [U_eq, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    smul_eq_mul, m1]
  field_simp

theorem βhat_sub (β₀ : ℝ) (ξ : ℕ → Ω → F) {n : ℕ} (hn : 1 ≤ n) (ω : Ω) :
    βhat β₀ ξ n ω - β₀ = m1 ξ n ω / 2 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
  have hY : ∀ i, Y β₀ ξ i 1 ω + Y β₀ ξ i 2 ω = 2 * β₀ + ⟪ξ i ω, s⟫ := fun i ↦ by
    rw [inner_s, Y, Y]
    ring
  simp only [βhat, hY, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, m1]
  field_simp
  ring

theorem rankOne_real (u : ℝ) :
    InnerProductSpace.rankOne ℝ u u = (u ^ 2) • (1 : ℝ →L[ℝ] ℝ) := by
  ext
  simp [InnerProductSpace.rankOne_apply]
  ring

theorem avg_rankOne (β₀ : ℝ) (ξ : ℕ → Ω → F) {n : ℕ} (hn : 1 ≤ n) (β : ℝ) (ω : Ω) :
    (n : ℝ)⁻¹ • ∑ i ∈ range n, InnerProductSpace.rankOne ℝ (U β₀ ξ i β ω) (U β₀ ξ i β ω) =
      (m2 ξ n ω + 2 * (2 * (β₀ - β)) * m1 ξ n ω + (2 * (β₀ - β)) ^ 2) • (1 : ℝ →L[ℝ] ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
  simp only [rankOne_real, ← Finset.sum_smul, smul_smul]
  congr 1
  simp only [U_eq, add_sq, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, ← Finset.sum_mul, ← Finset.mul_sum, m1, m2]
  field_simp

/-- **(a) in the model: the GEE estimator is consistent**, from
`tendstoInMeasure_of_tendstoUniformlyOn_of_root` with limit `g β = 2 (β₀ - β)` on
`K = closedBall β₀ 1`; the uniform deviation is `|n⁻¹ ∑ ⟪ξ i, s⟫|` for every `β`, which tends to
`0` by the law of large numbers. -/
theorem tendstoInMeasure_βhat (hξ : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, HasLaw (ξ i) (stdGaussian F) P) (hind : iIndepFun ξ P) (β₀ : ℝ) :
    TendstoInMeasure P (βhat β₀ ξ) atTop (fun _ ↦ β₀) := by
  have hm1 := tendstoInMeasure_iff_dist.1 (tendstoInMeasure_m1 hξ hlaw hind)
  refine tendstoInMeasure_of_tendstoUniformlyOn_of_root (U := fun i β ω ↦ U β₀ ξ i β ω)
    (g := fun β ↦ 2 * (β₀ - β)) (K := Metric.closedBall β₀ 1) (isCompact_closedBall _ _)
    (by fun_prop) (fun β _ hβ ↦ by linarith) (fun ε hε ↦ ?_) ?_ ?_
  · refine tendsto_measure_of_eventually_subset (hm1 ε hε) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn ω hω
    obtain ⟨β, -, hβ⟩ := hω
    simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero]
    rwa [avg_U β₀ ξ hn, add_sub_cancel_right, Real.norm_eq_abs] at hβ
  · refine tendsto_measure_of_eventually_subset (hm1 1 one_pos) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn ω hω
    simp only [Set.mem_ofPred_eq, Metric.mem_closedBall, Real.dist_eq, not_le,
      βhat_sub β₀ ξ hn, abs_div, abs_two, sub_zero] at hω ⊢
    linarith
  · simp [sum_U_βhat]

/-- The cluster scores are differentiable in `β` with derivative `A = -2`. -/
theorem hasFDerivAt_U (β₀ : ℝ) (ξ : ℕ → Ω → F) (i : ℕ) (ω : Ω) (b : ℝ) :
    HasFDerivAt (fun β ↦ U β₀ ξ i β ω) A b := by
  have h : HasDerivAt (fun β ↦ U β₀ ξ i β ω) (-2) b := by
    simp only [U_eq]
    have := ((hasDerivAt_id b).const_sub β₀).const_mul 2 |>.const_add ⟪ξ i ω, s⟫
    simpa using this
  refine h.hasFDerivAt.congr_fderiv ?_
  ext
  simp [A]

omit [IsProbabilityMeasure P] in
/-- The averaged Jacobian equals `A` exactly for `n ≥ 1`, so its uniform convergence holds. -/
theorem tendsto_jacobian (β₀ : ℝ) (δ : ℝ) :
    ∀ ε > 0, Tendsto (fun n : ℕ ↦ P {_ω | ∃ β ∈ Metric.ball β₀ δ,
      ε ≤ ‖(n : ℝ)⁻¹ • ∑ _i ∈ range n, A - (fun _ ↦ A) β‖}) atTop (𝓝 0) := by
  intro ε hε
  refine tendsto_measure_of_eventually_subset (T := fun _ ↦ ∅) (by simp) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn _ω hω
  obtain ⟨β, -, hβ⟩ := hω
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
  rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ hn', one_smul, sub_self, norm_zero] at hβ
  exact absurd hβ (not_le.2 hε)

/-- **(b) in the model through `tendstoInDistribution_sqrt_smul_sub_sandwich_of_hasFDerivAt`**:
differentiable scores with Jacobian `A`, consistency from `tendstoInMeasure_βhat`, and the
linearization supplied by `linearization_of_hasFDerivAt`. -/
theorem tendstoInDistribution_randomIntercept_of_hasFDerivAt (hξ : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, HasLaw (ξ i) (stdGaussian F) P) (hind : iIndepFun ξ P) (β₀ : ℝ) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √n • (βhat β₀ ξ n ω - β₀)) atTop id
      (fun _ ↦ P) (gaussianReal 0 (3 / 2)) :=
  tendstoInDistribution_sqrt_smul_sub_sandwich_of_hasFDerivAt (DU := fun _ _ _ ↦ A)
    (Abar := fun _ ↦ A) one_pos (fun i ω β _ ↦ hasFDerivAt_U β₀ ξ i ω β) continuousAt_const
    isUnit_A (tendsto_jacobian β₀ 1) (B := B)
    (fun k ↦ by rw [U_self]; exact measurable_inner_s.comp (hξ k))
    (by simp_rw [U_self]; exact hind.comp (fun _ x ↦ ⟪x, s⟫) fun _ ↦ measurable_inner_s)
    (fun k ↦ by rw [U_self]; exact integral_inner_s hlaw k) (memLp_U hlaw β₀)
    (tendsto_meat hlaw β₀)
    (fun t ↦ lindebergConditionTriangular_inner_of_identDistrib (identDistrib_U hlaw β₀)
      (memLp_U hlaw β₀ 0) t)
    (fun n ↦ (measurable_βhat hξ β₀ n).aemeasurable) (tendstoInMeasure_βhat hξ hlaw hind β₀)
    (by simp [sum_U_βhat]) aemeasurable_id hasLaw_limit

/-- The in-probability limit of the averaged rank-one operators: `Bbar β = (6 + 4 (β₀ - β)²) • 1`. -/
noncomputable def Bbar (β₀ β : ℝ) : ℝ →L[ℝ] ℝ := (6 + (2 * (β₀ - β)) ^ 2) • 1

/-- **(c) in the model: the empirical sandwich is consistent for the CLT covariance `3 / 2`**,
from `tendstoInMeasure_empirical_sandwichCovariance_of_eq` with bread `A` and meat limit
`Bbar`, which equals the CLT meat `B = 6` at `β₀`. The uniform convergence of the averaged outer
products on `ball β₀ 1` follows from the laws of large numbers for `⟪ξ i, s⟫` and `⟪ξ i, s⟫²`. -/
theorem tendstoInMeasure_empirical_sandwich_randomIntercept (hξ : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, HasLaw (ξ i) (stdGaussian F) P) (hind : iIndepFun ξ P) (β₀ : ℝ) :
    TendstoInMeasure P (fun (n : ℕ) ω ↦ sandwichCovariance
        ((n : ℝ)⁻¹ • ∑ _i ∈ range n, A)
        ((n : ℝ)⁻¹ • ∑ i ∈ range n, InnerProductSpace.rankOne ℝ (U β₀ ξ i (βhat β₀ ξ n ω) ω) (U β₀ ξ i (βhat β₀ ξ n ω) ω))) atTop
      (fun _ ↦ (3 / 2 : ℝ) • 1) := by
  rw [← sandwichCovariance_A_B]
  have hm1 := tendstoInMeasure_iff_dist.1 (tendstoInMeasure_m1 hξ hlaw hind)
  have hm2 := tendstoInMeasure_iff_dist.1 (tendstoInMeasure_m2 hξ hlaw hind)
  refine tendstoInMeasure_empirical_sandwichCovariance_of_eq (DU := fun _ _ _ ↦ A)
    (Abar := fun _ ↦ A) (Bbar := Bbar β₀) one_pos continuousAt_const
    (by unfold Bbar; fun_prop) (by simp [Bbar, B]) isUnit_A (tendsto_jacobian β₀ 1)
    (fun ε hε ↦ ?_) (tendstoInMeasure_βhat hξ hlaw hind β₀)
  have hsum := (hm2 (ε / 2) (half_pos hε)).add (hm1 (ε / 8) (by positivity))
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  refine (measure_mono fun ω hω ↦ ?_).trans (measure_union_le _ _)
  obtain ⟨β, hβ, hle⟩ := hω
  rw [avg_rankOne β₀ ξ hn, Bbar, ← sub_smul, norm_smul, norm_one, mul_one, Real.norm_eq_abs]
    at hle
  have hc : |2 * (β₀ - β)| ≤ 2 := by
    rw [Metric.mem_ball, Real.dist_eq] at hβ
    rw [abs_mul, abs_two, abs_sub_comm]
    linarith
  simp only [Set.mem_union, Set.mem_ofPred_eq, Real.dist_eq, sub_zero]
  by_contra hcon
  push Not at hcon
  have h3 : |2 * (2 * (β₀ - β)) * m1 ξ n ω| ≤ 4 * |m1 ξ n ω| := by
    rw [abs_mul, abs_mul, abs_two]
    nlinarith [abs_nonneg (m1 ξ n ω)]
  have h4 := abs_add_le (m2 ξ n ω - 6) (2 * (2 * (β₀ - β)) * m1 ξ n ω)
  have h5 : m2 ξ n ω + 2 * (2 * (β₀ - β)) * m1 ξ n ω + (2 * (β₀ - β)) ^ 2 -
      (6 + (2 * (β₀ - β)) ^ 2) = m2 ξ n ω - 6 + 2 * (2 * (β₀ - β)) * m1 ξ n ω := by ring
  rw [h5] at hle
  linarith [hcon.1, hcon.2]

/-- The random-intercept model is realized by i.i.d. standard Gaussian vectors on the infinite
product space `ℕ → F`. -/
example (β₀ : ℝ) :
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → F) ↦ √n • (βhat β₀ (fun i ω ↦ ω i) n ω - β₀)) atTop id
      (fun _ ↦ Measure.infinitePi fun _ ↦ stdGaussian F) (gaussianReal 0 (3 / 2)) :=
  tendstoInDistribution_randomIntercept (fun i ↦ measurable_pi_apply i)
    (fun i ↦ (measurePreserving_eval_infinitePi (fun _ ↦ stdGaussian F) i).hasLaw)
    (iIndepFun_infinitePi (X := fun _ x ↦ x) fun _ ↦ measurable_id) β₀

/-! ### Boundary: a singular bread breaks sandwich consistency -/

/-- With the singular bread `A = 0`, the deterministic bread estimators `(n + 1)⁻¹ • 1` converge
to `A` and the meat is the constant `1`, yet the sandwiches `(n + 1)² • 1` do not converge to
`sandwichCovariance 0 1 = 0`: `tendstoInMeasure_sandwichCovariance` needs `IsUnit A`. -/
theorem singular_bread_sandwich :
    TendstoInMeasure (Measure.dirac ())
        (fun (n : ℕ) (_ : Unit) ↦ (1 / ((n : ℝ) + 1)) • (1 : ℝ →L[ℝ] ℝ)) atTop (fun _ ↦ 0) ∧
      ¬ TendstoInMeasure (Measure.dirac ())
        (fun (n : ℕ) (_ : Unit) ↦
          sandwichCovariance ((1 / ((n : ℝ) + 1)) • (1 : ℝ →L[ℝ] ℝ)) ((1 : ℝ) • 1))
        atTop (fun _ ↦ sandwichCovariance 0 ((1 : ℝ) • 1)) := by
  refine ⟨?_, fun h ↦ ?_⟩
  · refine tendstoInMeasure_of_tendsto_ae (fun _ ↦ aestronglyMeasurable_const)
      (ae_of_all _ fun _ ↦ ?_)
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const (1 : ℝ →L[ℝ] ℝ)
  have hzero : sandwichCovariance (0 : ℝ →L[ℝ] ℝ) ((1 : ℝ) • 1) = 0 := by
    simp [sandwichCovariance]
  have hn : ∀ n : ℕ, sandwichCovariance ((1 / ((n : ℝ) + 1)) • (1 : ℝ →L[ℝ] ℝ)) ((1 : ℝ) • 1) =
      ((n : ℝ) + 1) ^ 2 • 1 := fun n ↦ by
    rw [sandwichCovariance_smul_one _ _ (by positivity)]
    congr 1
    field_simp
  rw [tendstoInMeasure_iff_dist] at h
  have h1 := h 1 one_pos
  simp only [hzero, hn, dist_zero_right, norm_smul, norm_one, mul_one, Real.norm_eq_abs] at h1
  have huniv : ∀ n : ℕ, {_x : Unit | (1 : ℝ) ≤ |((n : ℝ) + 1) ^ 2|} = Set.univ := fun n ↦ by
    ext
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    rw [abs_of_nonneg (by positivity)]
    nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  simp only [huniv, measure_univ] at h1
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h1)

/-! ### Boundary: Lindeberg failure -/

/-- Exploding cluster scores `U k = 2 ^ k` violate the cluster Lindeberg condition in direction
`1`: the last cluster alone contributes `4 ^ (n - 1) / n > 1` to the Lindeberg sum. -/
theorem not_lindeberg_exploding :
    ¬ LindebergConditionTriangular
      (fun n k (_ : Unit) ↦ (√n)⁻¹ * ⟪(2 : ℝ) ^ k, (1 : ℝ)⟫) (Measure.dirac ()) := by
  intro h
  have hge : ∀ n : ℕ, 2 ≤ n → 1 ≤ ∑ k ∈ range n, ∫ ω, ((√n)⁻¹ * ⟪(2 : ℝ) ^ k, (1 : ℝ)⟫) ^ 2 *
      Set.indicator {ω' : Unit | 1 < |(√n)⁻¹ * ⟪(2 : ℝ) ^ k, (1 : ℝ)⟫|} 1 ω
        ∂(Measure.dirac ()) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    simp only [integral_dirac, inner_real, mul_one]
    set x : ℝ := (√((m + 1 : ℕ) : ℝ))⁻¹ * 2 ^ m with hx_def
    have hpow : (m : ℝ) + 1 < 4 ^ m := by
      have := one_add_mul_le_pow (show (-2 : ℝ) ≤ 3 by norm_num) m
      norm_num at this
      linarith
    have hx2 : 1 < x ^ 2 := by
      rw [hx_def, mul_pow, inv_pow, Real.sq_sqrt (by positivity), ← pow_mul, pow_mul',
        show (2 : ℝ) ^ 2 = 4 by norm_num, inv_mul_eq_div, one_lt_div (by positivity)]
      push_cast
      exact hpow
    have hx : 1 < |x| := by
      rw [← sq_lt_sq₀ zero_le_one (abs_nonneg x), sq_abs, one_pow]
      exact hx2
    calc (1 : ℝ) ≤ x ^ 2 * Set.indicator {_ω' : Unit | 1 < |x|} 1 () := by
          simp only [Set.indicator_apply, Set.mem_ofPred_eq, hx, ↓reduceIte, Pi.one_apply,
            mul_one]
          exact hx2.le
      _ ≤ _ := Finset.single_le_sum (f := fun k ↦ ((√((m + 1 : ℕ) : ℝ))⁻¹ * (2 : ℝ) ^ k) ^ 2 *
            Set.indicator {_ω' : Unit | 1 < |(√((m + 1 : ℕ) : ℝ))⁻¹ * (2 : ℝ) ^ k|} 1 ())
          (fun k _ ↦ mul_nonneg (sq_nonneg _) (Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _))
          (Finset.mem_range.2 (Nat.lt_succ_self m))
  obtain ⟨n, hn⟩ := (((h 1 one_pos).eventually (gt_mem_nhds one_pos)).and
    (eventually_ge_atTop 2)).exists
  exact absurd (hge n hn.2) (not_le.2 hn.1)

end GEESandwichTest
