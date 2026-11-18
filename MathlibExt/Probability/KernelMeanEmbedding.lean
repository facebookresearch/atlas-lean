/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Reproducing
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import MathlibExt.Analysis.InnerProductSpace.PositiveDefiniteKernel
public import MathlibExt.Analysis.FunctionalAnalysis.RepresenterTheorem

/-!
# Kernel mean embeddings and the maximum mean discrepancy

Let `H` be a real reproducing kernel Hilbert space of functions `X → ℝ` (Mathlib's
`RKHS ℝ H X ℝ`), with canonical feature map `φ(x) = k(·, x)` (`featureMap`) and kernel
`k(x, y) = ⟪φ(x), φ(y)⟫` (`kernelValue`). For a measure `μ` on `X` whose feature map is Bochner
integrable, the *kernel mean embedding* is `μ_P = ∫ φ(x) dP(x) ∈ H` (`meanEmbedding`). The
*maximum mean discrepancy* over the unit ball of `H` is
`MMD(P, Q) = sup_{‖f‖ ≤ 1} (E_P f - E_Q f)` (`mmd`).

## Main results

* `inner_meanEmbedding`: the reproducing property of the mean embedding,
  `⟪f, μ_P⟫ = E_P f` for every `f ∈ H` (Gretton et al. 2012, Lemma 3).
* `integrable_featureMap_of_integrable_sqrt`: the feature map is integrable as soon as it is
  strongly measurable and `E √k(x, x) < ∞`, the hypothesis of Lemma 3.
* `mmd_eq_norm_sub`: `MMD(P, Q) = ‖μ_P - μ_Q‖` (Lemma 4).
* `mmd_sq_eq`: `MMD(P, Q)² = E k(x, x') - 2 E k(x, y) + E k(y, y')` with independent copies,
  written with product measures (Lemma 6).
* `mmdBiased_eq` and `mmdBiased_sq_eq`: the biased empirical MMD (equation (2)) is the distance
  between the empirical mean embeddings and its square is the V-statistic of equation (5).
* `mmd_eq_zero_iff_of_universal`: for a continuous kernel on a compact metric space whose RKHS is
  dense in `C(X)`, `MMD(P, Q) = 0` if and only if `P = Q` (Theorem 5).

## References

* A. Gretton, K. M. Borgwardt, M. J. Rasch, B. Schölkopf and A. Smola, "A kernel two-sample
  test", *J. Mach. Learn. Res.* **13** (2012), 723–773, Section 2.
* K. Muandet, K. Fukumizu, B. Sriperumbudur and B. Schölkopf, "Kernel mean embedding of
  distributions: a review and beyond", *Found. Trends Mach. Learn.* **10** (2017), 1–141.
-/

@[expose] public section

open MeasureTheory RKHS MathlibExt.Analysis.InnerProductSpace MathlibExt.Analysis
open scoped InnerProductSpace

namespace MathlibExt.Probability.KernelMeanEmbedding

variable {X : Type*}
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [RKHS ℝ H X ℝ]

/-- **Canonical feature map of a reproducing kernel Hilbert space.** The feature map sends
`x` to the kernel function `φ(x) = k(·, x) ∈ H`, the representer of evaluation at `x`
(Gretton et al., *A kernel two-sample test*, JMLR 13 (2012), Section 2.2). -/
noncomputable def featureMap (x : X) : H :=
  kerFun H x 1

/-- **Scalar kernel of a real reproducing kernel Hilbert space.** The kernel is the inner
product of feature maps, `k(x, y) = ⟪φ(x), φ(y)⟫` (Gretton et al., *A kernel two-sample test*,
JMLR 13 (2012), Section 2.2). -/
noncomputable def kernelValue (x y : X) : ℝ :=
  ⟪featureMap H x, featureMap H y⟫_ℝ

variable {H}

/-- **Reproducing property of the feature map.** For every `f ∈ H`, `⟪f, φ(x)⟫ = f(x)`
(Gretton et al., *A kernel two-sample test*, JMLR 13 (2012), Section 2.2). -/
theorem inner_featureMap (f : H) (x : X) : ⟪f, featureMap H x⟫_ℝ = f x := by
  rw [featureMap, inner_kerFun]
  simp

/-- **Kernel functions are feature maps.** The function `φ(y)` takes the value `k(x, y)` at
`x`: `φ(y)(x) = k(x, y)` (Gretton et al., *A kernel two-sample test*, JMLR 13 (2012),
Section 2.2). -/
theorem featureMap_apply (x y : X) : featureMap H y x = kernelValue H x y := by
  rw [kernelValue, ← inner_featureMap (featureMap H y) x]
  exact real_inner_comm _ _

/-- **Symmetry of the kernel.** `k(x, y) = k(y, x)` (Gretton et al., *A kernel two-sample
test*, JMLR 13 (2012), Section 2.2). -/
theorem kernelValue_comm (x y : X) : kernelValue H x y = kernelValue H y x :=
  real_inner_comm _ _

/-- **Norm of a feature map.** `‖φ(x)‖ = √k(x, x)` (Gretton et al., *A kernel two-sample
test*, JMLR 13 (2012), proof of Lemma 3). -/
theorem norm_featureMap (x : X) : ‖featureMap H x‖ = √(kernelValue H x x) := by
  rw [kernelValue, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-- **The kernel of an RKHS is a positive-definite kernel.** Every kernel matrix
`(k(xᵢ, xⱼ))ᵢⱼ` of `k(x, y) = ⟪φ(x), φ(y)⟫` is positive semidefinite, the converse direction of
Aronszajn's theorem (F. Bach, *Learning Theory from First Principles*, MIT Press (2024),
Section 7.3, Proposition 7.3). -/
theorem isPosDefKernel_kernelValue :
    PositiveDefiniteKernel.IsPosDefKernel (kernelValue H : X → X → ℝ) :=
  PositiveDefiniteKernel.isPosDefKernel_of_eq_inner (featureMap H) fun _ _ => rfl

/-- **The kernel Gram matrix of the representer theorem.** The Gram matrix
`RepresenterTheorem.kernelGram` used for kernel ridge regression has entries
`k(xᵢ, xⱼ) = kernelValue H xᵢ xⱼ` (Gretton et al., *A kernel two-sample test*, JMLR 13 (2012),
Section 2.2: `⟪φ(x), φ(y)⟫ = k(x, y)`). -/
theorem kernelGram_apply {n : ℕ} (x : Fin n → X) (i j : Fin n) :
    FunctionalAnalysis.RepresenterTheorem.kernelGram H x i j = kernelValue H (x i) (x j) := by
  rw [FunctionalAnalysis.RepresenterTheorem.kernelGram, Matrix.of_apply, kernel_apply,
    ContinuousLinearMap.comp_apply, adjoint_kerFun, ← featureMap, featureMap_apply]

variable [MeasurableSpace X]

variable (H) in
/-- **Kernel mean embedding.** The mean embedding of a measure `P` is the Bochner integral
`μ_P = ∫ φ(x) dP(x)` of the feature map; it is the element of `H` representing expectation
under `P` (Gretton et al., *A kernel two-sample test*, JMLR 13 (2012), Section 2.2 and
Lemma 3). The definition is meaningful when the feature map is integrable, see
`inner_meanEmbedding`. -/
noncomputable def meanEmbedding (μ : Measure X) : H :=
  ∫ x, featureMap H x ∂μ

/-- **Elements of an RKHS are integrable against measures with integrable feature map.**
If `φ` is Bochner integrable for `μ`, then every `f ∈ H` is `μ`-integrable, since
`f(x) = ⟪f, φ(x)⟫` (Gretton et al., *A kernel two-sample test*, JMLR 13 (2012), proof of
Lemma 3). -/
theorem integrable_apply {μ : Measure X} (hφ : Integrable (featureMap H) μ) (f : H) :
    Integrable (fun x => f x) μ := by
  simpa only [inner_featureMap] using hφ.const_inner (𝕜 := ℝ) f

/-- **Reproducing property of the kernel mean embedding** (Gretton et al., *A kernel
two-sample test*, JMLR 13 (2012), Lemma 3). If the feature map is Bochner integrable for `μ`,
then `⟪f, μ_P⟫ = ∫ f dP` for every `f ∈ H`. -/
theorem inner_meanEmbedding {μ : Measure X} (hφ : Integrable (featureMap H) μ) (f : H) :
    ⟪f, meanEmbedding H μ⟫_ℝ = ∫ x, f x ∂μ := by
  rw [meanEmbedding, ← integral_inner hφ f]
  simp only [inner_featureMap]

/-- **The mean embedding as a function** (Gretton et al., *A kernel two-sample test*, JMLR 13
(2012), Lemma 3 and its proof). If the feature map is Bochner integrable for `μ`, the mean
embedding is the function `μ_P(t) = ∫ k(t, x) dP(x)`. -/
theorem meanEmbedding_apply {μ : Measure X} (hφ : Integrable (featureMap H) μ) (t : X) :
    meanEmbedding H μ t = ∫ x, kernelValue H t x ∂μ := by
  rw [← inner_featureMap, real_inner_comm, inner_meanEmbedding hφ]
  simp only [featureMap_apply, kernelValue_comm]

/-- **Existence of the kernel mean embedding** (Gretton et al., *A kernel two-sample test*,
JMLR 13 (2012), Lemma 3). If the feature map is strongly measurable and
`∫ √k(x, x) dP(x) < ∞`, then the feature map is Bochner integrable, so the mean embedding
`μ_P ∈ H` exists and satisfies `inner_meanEmbedding`. The paper assumes `k` measurable; the
measurability hypothesis here is the one Bochner integration needs. -/
theorem integrable_featureMap_of_integrable_sqrt {μ : Measure X}
    (hm : AEStronglyMeasurable (featureMap H) μ)
    (hk : Integrable (fun x => √(kernelValue H x x)) μ) :
    Integrable (featureMap H) μ := by
  refine ⟨hm, ?_⟩
  have : HasFiniteIntegral (fun x => √(kernelValue H x x)) μ := hk.2
  refine this.congr' (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_featureMap, Real.norm_of_nonneg (Real.sqrt_nonneg _)]

/-! ### The maximum mean discrepancy -/

variable (H) in
/-- **Maximum mean discrepancy over the unit ball of an RKHS** (Gretton et al., *A kernel
two-sample test*, JMLR 13 (2012), Definition 2, equation (1), with `F` the unit ball of `H`).
`MMD(P, Q) = sup_{‖f‖ ≤ 1} (∫ f dP - ∫ f dQ)`. -/
noncomputable def mmd (μ ν : Measure X) : ℝ :=
  sSup ((fun f : H => ∫ x, f x ∂μ - ∫ x, f x ∂ν) '' Metric.closedBall 0 1)

omit [CompleteSpace H] [RKHS ℝ H X ℝ] [MeasurableSpace X] in
/-- **The unit ball attains the norm of a vector.** On the closed unit ball of a real inner
product space, `f ↦ ⟪f, v⟫` attains its supremum `‖v‖` (the Cauchy–Schwarz step in the proof of
Lemma 4 of Gretton et al., *A kernel two-sample test*, JMLR 13 (2012)). -/
theorem isGreatest_inner_closedBall (v : H) :
    IsGreatest ((fun f : H => ⟪f, v⟫_ℝ) '' Metric.closedBall 0 1) ‖v‖ := by
  refine ⟨?_, ?_⟩
  · by_cases hv : v = 0
    · exact ⟨0, by simp, by simp [hv]⟩
    · refine ⟨‖v‖⁻¹ • v, ?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
      · simp only [real_inner_smul_left, real_inner_self_eq_norm_sq]
        have : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
        field_simp
  · rintro _ ⟨f, hf, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hf
    calc ⟪f, v⟫_ℝ ≤ ‖f‖ * ‖v‖ := real_inner_le_norm f v
      _ ≤ 1 * ‖v‖ := by gcongr
      _ = ‖v‖ := one_mul _

/-- **The MMD is the distance between mean embeddings** (Gretton et al., *A kernel two-sample
test*, JMLR 13 (2012), Lemma 4). If the feature map is Bochner integrable for `P` and `Q`, then
`MMD(P, Q) = ‖μ_P - μ_Q‖`. -/
theorem mmd_eq_norm_sub {μ ν : Measure X} (hμ : Integrable (featureMap H) μ)
    (hν : Integrable (featureMap H) ν) :
    mmd H μ ν = ‖meanEmbedding H μ - meanEmbedding H ν‖ := by
  have h : (fun f : H => ∫ x, f x ∂μ - ∫ x, f x ∂ν) =
      fun f : H => ⟪f, meanEmbedding H μ - meanEmbedding H ν⟫_ℝ := by
    funext f
    rw [inner_sub_right, inner_meanEmbedding hμ, inner_meanEmbedding hν]
  rw [mmd, h]
  exact (isGreatest_inner_closedBall _).csSup_eq

/-- **The MMD vanishes on the diagonal** (Gretton et al., *A kernel two-sample test*, JMLR 13
(2012), Section 2.2; pseudometric axioms as in its footnote 3). If the feature map is Bochner
integrable for `P`, then `MMD(P, P) = 0`. -/
theorem mmd_self {μ : Measure X} (hμ : Integrable (featureMap H) μ) : mmd H μ μ = 0 := by
  rw [mmd_eq_norm_sub hμ hμ, sub_self, norm_zero]

/-- **Symmetry of the MMD** (Gretton et al., *A kernel two-sample test*, JMLR 13 (2012),
Section 2.2; pseudometric axioms as in its footnote 3). If the feature map is Bochner integrable for
`P` and `Q`, then `MMD(P, Q) = MMD(Q, P)`. -/
theorem mmd_comm {μ ν : Measure X} (hμ : Integrable (featureMap H) μ)
    (hν : Integrable (featureMap H) ν) : mmd H μ ν = mmd H ν μ := by
  rw [mmd_eq_norm_sub hμ hν, mmd_eq_norm_sub hν hμ, norm_sub_rev]

/-- **Triangle inequality for the MMD** (Gretton et al., *A kernel two-sample test*, JMLR 13
(2012), Section 2.2; pseudometric axioms as in its footnote 3). If the feature map is Bochner
integrable for `P`, `Q` and `R`, then `MMD(P, R) ≤ MMD(P, Q) + MMD(Q, R)`. -/
theorem mmd_le_add {μ ν ρ : Measure X} (hμ : Integrable (featureMap H) μ)
    (hν : Integrable (featureMap H) ν) (hρ : Integrable (featureMap H) ρ) :
    mmd H μ ρ ≤ mmd H μ ν + mmd H ν ρ := by
  rw [mmd_eq_norm_sub hμ hρ, mmd_eq_norm_sub hμ hν, mmd_eq_norm_sub hν hρ]
  exact norm_sub_le_norm_sub_add_norm_sub _ _ _

/-- **Inner product of two mean embeddings.** If the feature map is Bochner integrable for `P`
and `Q`, then `⟪μ_P, μ_Q⟫ = ∫∫ k(x, y) dP(x) dQ(y)` (Gretton et al., *A kernel two-sample
test*, JMLR 13 (2012), proof of Lemma 6). -/
theorem inner_meanEmbedding_meanEmbedding {μ ν : Measure X} (hμ : Integrable (featureMap H) μ)
    (hν : Integrable (featureMap H) ν) :
    ⟪meanEmbedding H μ, meanEmbedding H ν⟫_ℝ = ∫ y, ∫ x, kernelValue H x y ∂μ ∂ν := by
  rw [inner_meanEmbedding hν]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [meanEmbedding_apply hμ, kernelValue_comm y]

/-- **Integrability of the kernel on a product.** If the feature map is Bochner integrable
for the s-finite measures `P` and `Q`, then `(x, y) ↦ k(x, y)` is `P ⊗ Q`-integrable, since
`|k(x, y)| ≤ ‖φ(x)‖ ‖φ(y)‖` (used in the proof of Lemma 6 of Gretton et al., *A kernel
two-sample test*, JMLR 13 (2012)). -/
theorem integrable_kernelValue_prod {μ ν : Measure X} [SFinite μ] [SFinite ν]
    (hμ : Integrable (featureMap H) μ) (hν : Integrable (featureMap H) ν) :
    Integrable (fun z : X × X => kernelValue H z.1 z.2) (μ.prod ν) := by
  have hprod : Integrable (fun z : X × X => ‖featureMap H z.1‖ * ‖featureMap H z.2‖)
      (μ.prod ν) := hμ.norm.mul_prod hν.norm
  refine hprod.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · exact (hμ.1.comp_fst).inner (hν.1.comp_snd)
  · exact (Real.norm_eq_abs _).le.trans (abs_real_inner_le_norm _ _)

/-- **Inner product of mean embeddings as an expectation over independent copies.** If the
feature map is Bochner integrable for the s-finite measures `P` and `Q`, then
`⟪μ_P, μ_Q⟫ = E_{(x, y) ~ P ⊗ Q} k(x, y)` (Gretton et al., *A kernel two-sample test*, JMLR 13
(2012), proof of Lemma 6). -/
theorem inner_meanEmbedding_eq_integral_prod {μ ν : Measure X} [SFinite μ] [SFinite ν]
    (hμ : Integrable (featureMap H) μ) (hν : Integrable (featureMap H) ν) :
    ⟪meanEmbedding H μ, meanEmbedding H ν⟫_ℝ =
      ∫ z, kernelValue H z.1 z.2 ∂(μ.prod ν) := by
  rw [inner_meanEmbedding_meanEmbedding hμ hν,
    integral_prod_symm _ (integrable_kernelValue_prod hμ hν)]

/-- **Population MMD in terms of the kernel** (Gretton et al., *A kernel two-sample test*,
JMLR 13 (2012), Lemma 6). If the feature map is Bochner integrable for the s-finite measures
`P` and `Q`, then, with `x, x'` independent with law `P` and `y, y'` independent with law `Q`,
`MMD(P, Q)² = E k(x, x') - 2 E k(x, y) + E k(y, y')`. -/
theorem mmd_sq_eq {μ ν : Measure X} [SFinite μ] [SFinite ν]
    (hμ : Integrable (featureMap H) μ) (hν : Integrable (featureMap H) ν) :
    mmd H μ ν ^ 2 =
      ∫ z, kernelValue H z.1 z.2 ∂(μ.prod μ) - 2 * ∫ z, kernelValue H z.1 z.2 ∂(μ.prod ν) +
        ∫ z, kernelValue H z.1 z.2 ∂(ν.prod ν) := by
  rw [mmd_eq_norm_sub hμ hν, norm_sub_sq_real, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, inner_meanEmbedding_eq_integral_prod hμ hμ,
    inner_meanEmbedding_eq_integral_prod hμ hν, inner_meanEmbedding_eq_integral_prod hν hν]

/-! ### Empirical estimates -/

variable (H) in
/-- **Empirical mean embedding.** For a nonempty sample `x₁, …, x_m` (`m ≥ 1`), the empirical
mean embedding is `μ_X = (1/m) ∑ᵢ φ(xᵢ)` (Gretton et al., *A kernel two-sample test*, JMLR 13
(2012), Section 2.2, before equation (5)). For an empty sample, which is excluded, the average
would be `0`. -/
noncomputable def empiricalEmbedding {m : ℕ} [NeZero m] (x : Fin m → X) : H :=
  (m : ℝ)⁻¹ • ∑ i, featureMap H (x i)

variable (H) in
/-- **Biased empirical MMD** (Gretton et al., *A kernel two-sample test*, JMLR 13 (2012),
equation (2), with `F` the unit ball of `H`). For nonempty samples `x₁, …, x_m` and
`y₁, …, y_n`, `MMD_b = sup_{‖f‖ ≤ 1} ((1/m) ∑ᵢ f(xᵢ) - (1/n) ∑ⱼ f(yⱼ))`. For an empty sample,
which is excluded, its empirical average would be `0`. -/
noncomputable def mmdBiased {m n : ℕ} [NeZero m] [NeZero n] (x : Fin m → X) (y : Fin n → X) :
    ℝ :=
  sSup ((fun f : H => (m : ℝ)⁻¹ * ∑ i, f (x i) - (n : ℝ)⁻¹ * ∑ j, f (y j)) ''
    Metric.closedBall 0 1)

omit [MeasurableSpace X] in
/-- **Reproducing property of the empirical mean embedding.** `⟪f, μ_X⟫ = (1/m) ∑ᵢ f(xᵢ)`
(Gretton et al., *A kernel two-sample test*, JMLR 13 (2012), Section 2.2, before
equation (5)). -/
theorem inner_empiricalEmbedding {m : ℕ} [NeZero m] (f : H) (x : Fin m → X) :
    ⟪f, empiricalEmbedding H x⟫_ℝ = (m : ℝ)⁻¹ * ∑ i, f (x i) := by
  simp only [empiricalEmbedding, real_inner_smul_right, inner_sum, inner_featureMap]

omit [MeasurableSpace X] in
/-- **The biased empirical MMD is the distance between empirical mean embeddings**
(Gretton et al., *A kernel two-sample test*, JMLR 13 (2012), Section 2.2, before equation (5)):
`MMD_b = ‖μ_X - μ_Y‖`. -/
theorem mmdBiased_eq {m n : ℕ} [NeZero m] [NeZero n] (x : Fin m → X) (y : Fin n → X) :
    mmdBiased H x y = ‖empiricalEmbedding H x - empiricalEmbedding H y‖ := by
  have h : (fun f : H => (m : ℝ)⁻¹ * ∑ i, f (x i) - (n : ℝ)⁻¹ * ∑ j, f (y j)) =
      fun f : H => ⟪f, empiricalEmbedding H x - empiricalEmbedding H y⟫_ℝ := by
    funext f
    rw [inner_sub_right, inner_empiricalEmbedding, inner_empiricalEmbedding]
  rw [mmdBiased, h]
  exact (isGreatest_inner_closedBall _).csSup_eq

omit [MeasurableSpace X] in
/-- **Inner product of empirical mean embeddings.**
`⟪μ_X, μ_Y⟫ = (1/(mn)) ∑ᵢ ∑ⱼ k(xᵢ, yⱼ)` (Gretton et al., *A kernel two-sample test*, JMLR 13
(2012), derivation of equation (5)). -/
theorem inner_empiricalEmbedding_empiricalEmbedding {m n : ℕ} [NeZero m] [NeZero n]
    (x : Fin m → X) (y : Fin n → X) :
    ⟪empiricalEmbedding H x, empiricalEmbedding H y⟫_ℝ =
      ((m : ℝ) * n)⁻¹ * ∑ i, ∑ j, kernelValue H (x i) (y j) := by
  simp only [empiricalEmbedding, real_inner_smul_left, real_inner_smul_right, sum_inner,
    inner_sum, kernelValue, mul_inv]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

omit [MeasurableSpace X] in
/-- **The biased empirical MMD as a V-statistic** (Gretton et al., *A kernel two-sample test*,
JMLR 13 (2012), equation (5)):
`MMD_b² = (1/m²) ∑_{i,j} k(xᵢ, xⱼ) - (2/(mn)) ∑_{i,j} k(xᵢ, yⱼ) + (1/n²) ∑_{i,j} k(yᵢ, yⱼ)`. -/
theorem mmdBiased_sq_eq {m n : ℕ} [NeZero m] [NeZero n] (x : Fin m → X) (y : Fin n → X) :
    mmdBiased H x y ^ 2 =
      ((m : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, kernelValue H (x i) (x j) -
        2 * ((m : ℝ) * n)⁻¹ * ∑ i, ∑ j, kernelValue H (x i) (y j) +
        ((n : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, kernelValue H (y i) (y j) := by
  rw [mmdBiased_eq, norm_sub_sq_real, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, inner_empiricalEmbedding_empiricalEmbedding,
    inner_empiricalEmbedding_empiricalEmbedding, inner_empiricalEmbedding_empiricalEmbedding]
  ring

/-! ### Characteristic and universal kernels -/

variable (H) in
/-- **Characteristic kernel** (Fukumizu et al. 2008; Gretton et al., *A kernel two-sample
test*, JMLR 13 (2012), Section 2.2, after Theorem 5). The kernel of `H` is characteristic if
the mean embedding is injective on probability measures with integrable feature map. -/
def IsCharacteristic : Prop :=
  ∀ μ ν : Measure X, IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    Integrable (featureMap H) μ → Integrable (featureMap H) ν →
    meanEmbedding H μ = meanEmbedding H ν → μ = ν

/-- **The MMD of a characteristic kernel separates probability measures** (Gretton et al.,
*A kernel two-sample test*, JMLR 13 (2012), Section 2.2). For a characteristic kernel and
probability measures with integrable feature map, `MMD(P, Q) = 0` if and only if `P = Q`. For
every kernel the MMD is a pseudometric on such measures; it is a metric exactly when the kernel
is characteristic. -/
theorem mmd_eq_zero_iff_of_isCharacteristic (hH : IsCharacteristic H) {μ ν : Measure X}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hμ : Integrable (featureMap H) μ)
    (hν : Integrable (featureMap H) ν) : mmd H μ ν = 0 ↔ μ = ν := by
  rw [mmd_eq_norm_sub hμ hν, norm_eq_zero, sub_eq_zero]
  refine ⟨hH μ ν ‹_› ‹_› hμ hν, ?_⟩
  rintro rfl
  rfl

section Universal

omit [MeasurableSpace X] in
/-- **Operator-valued and scalar kernels.** For a real scalar RKHS, Mathlib's operator-valued
kernel `RKHS.kernel H x y` is multiplication by the scalar kernel `k(x, y) = ⟪φ(x), φ(y)⟫`
(Gretton et al., *A kernel two-sample test*, JMLR 13 (2012), Section 2.2). -/
theorem kernel_eq_smul (x y : X) :
    kernel H x y = kernelValue H x y • ContinuousLinearMap.id ℝ ℝ := by
  ext
  rw [kernel_apply, ContinuousLinearMap.comp_apply, adjoint_kerFun, ← featureMap,
    featureMap_apply]
  simp

omit [MeasurableSpace X] in
/-- **Continuity of the feature map.** A continuous scalar kernel has a continuous feature
map `x ↦ k(·, x)` into `H`, as `‖φ(x) - φ(y)‖² = k(x, x) - 2 k(x, y) + k(y, y)` (via Mathlib's
`RKHS.continuous_kernel_iff_continuous_kerFun`; continuity of `k` is part of universality in
Theorem 5 of Gretton et al., *A kernel two-sample test*, JMLR 13 (2012)). -/
theorem continuous_featureMap_of_continuous_kernelValue [TopologicalSpace X]
    (hk : Continuous fun p : X × X => kernelValue H p.1 p.2) :
    Continuous (featureMap H) := by
  have hK : Continuous fun p : X × X => kernel H p.1 p.2 := by
    simp only [kernel_eq_smul]
    exact hk.smul continuous_const
  have hk' := (continuous_kernel_iff_continuous_kerFun H).1 hK
  exact hk'.clm_apply continuous_const

/-- **Mean embeddings exist for continuous kernels on compact spaces.** On a compact metric
space with its Borel σ-algebra, a continuous feature map is Bochner integrable for every finite
measure, so the mean embedding of every Borel probability measure exists (the setting of
Theorem 5 of Gretton et al., *A kernel two-sample test*, JMLR 13 (2012)). -/
theorem integrable_featureMap_of_continuous [MetricSpace X] [CompactSpace X] [BorelSpace X]
    (hc : Continuous (featureMap H)) (μ : Measure X) [IsFiniteMeasure μ] :
    Integrable (featureMap H) μ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  exact Integrable.of_bound hc.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => hC x (Set.mem_univ x))

/-- **The MMD of a universal kernel characterizes distributions** (Gretton et al., *A kernel
two-sample test*, JMLR 13 (2012), Theorem 5). Let `X` be a compact metric space with its Borel
σ-algebra and `H` a universal RKHS on `X`: its kernel `k` is continuous and `H` is dense in
`C(X)` for the supremum norm. Then for Borel probability measures `P` and `Q`,
`MMD(P, Q) = 0` if and only if `P = Q`. -/
theorem mmd_eq_zero_iff_of_universal [MetricSpace X] [CompactSpace X] [BorelSpace X]
    (hk : Continuous fun p : X × X => kernelValue H p.1 p.2)
    (hdense : ∀ (f : C(X, ℝ)) (ε : ℝ), 0 < ε → ∃ g : H, ∀ x, |f x - g x| ≤ ε)
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    mmd H μ ν = 0 ↔ μ = ν := by
  have hc := continuous_featureMap_of_continuous_kernelValue hk
  have hμ := integrable_featureMap_of_continuous hc μ
  have hν := integrable_featureMap_of_continuous hc ν
  refine ⟨fun h => ?_, ?_⟩
  · rw [mmd_eq_norm_sub hμ hν, norm_eq_zero, sub_eq_zero] at h
    have hH : ∀ g : H, ∫ x, g x ∂μ = ∫ x, g x ∂ν := fun g => by
      rw [← inner_meanEmbedding hμ, ← inner_meanEmbedding hν, h]
    -- Lemma 1 of Gretton et al. (Dudley, Lemma 9.3.2).
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
    have key : ∀ ε : ℝ, 0 < ε → |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ 2 * ε := by
      intro ε hε
      obtain ⟨g, hg⟩ := hdense f.toContinuousMap ε hε
      have hg' : ∀ x, ‖f x - g x‖ ≤ ε := fun x => by
        simpa [Real.norm_eq_abs] using hg x
      have hfi : ∀ (ρ : Measure X) [IsFiniteMeasure ρ], Integrable (fun x => f x) ρ :=
        fun ρ _ => f.integrable ρ
      have bound : ∀ (ρ : Measure X) [IsProbabilityMeasure ρ], Integrable (featureMap H) ρ →
          |∫ x, f x ∂ρ - ∫ x, g x ∂ρ| ≤ ε := by
        intro ρ _ hρ
        rw [← integral_sub (hfi ρ) (integrable_apply hρ g), ← Real.norm_eq_abs]
        have := norm_integral_le_of_norm_le_const (μ := ρ)
          (Filter.Eventually.of_forall hg')
        simpa using this
      have h1 := bound μ hμ
      have h2 := bound ν hν
      rw [hH g] at h1
      calc |∫ x, f x ∂μ - ∫ x, f x ∂ν|
          = |(∫ x, f x ∂μ - ∫ x, g x ∂ν) - (∫ x, f x ∂ν - ∫ x, g x ∂ν)| := by ring_nf
        _ ≤ |∫ x, f x ∂μ - ∫ x, g x ∂ν| + |∫ x, f x ∂ν - ∫ x, g x ∂ν| := abs_sub _ _
        _ ≤ ε + ε := add_le_add h1 h2
        _ = 2 * ε := by ring
    by_contra hne
    have hpos : 0 < |∫ x, f x ∂μ - ∫ x, f x ∂ν| := abs_pos.mpr (sub_ne_zero.mpr hne)
    have := key (|∫ x, f x ∂μ - ∫ x, f x ∂ν| / 4) (by positivity)
    linarith
  · rintro rfl
    rw [mmd_eq_norm_sub hμ hμ, sub_self, norm_zero]

/-- **Universal kernels are characteristic** (Gretton et al., *A kernel two-sample test*,
JMLR 13 (2012), Theorem 5 and the discussion after it). On a compact metric space, a continuous
kernel whose RKHS is dense in `C(X)` is characteristic. -/
theorem isCharacteristic_of_universal [MetricSpace X] [CompactSpace X] [BorelSpace X]
    (hk : Continuous fun p : X × X => kernelValue H p.1 p.2)
    (hdense : ∀ (f : C(X, ℝ)) (ε : ℝ), 0 < ε → ∃ g : H, ∀ x, |f x - g x| ≤ ε) :
    IsCharacteristic H := by
  intro μ ν _ _ hμ hν h
  rw [← mmd_eq_zero_iff_of_universal hk hdense μ ν, mmd_eq_norm_sub hμ hν, h, sub_self,
    norm_zero]

end Universal

end MathlibExt.Probability.KernelMeanEmbedding
