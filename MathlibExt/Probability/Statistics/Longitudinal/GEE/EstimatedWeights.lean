/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Longitudinal.GEE.Sandwich
public import MathlibExt.Probability.Statistics.Slutsky

/-!
# GEE with estimated working-correlation weights

# GEE with estimated working-correlation weights

In practice the GEE working covariance `Vᵢ(β, α, φ) = φ Aᵢ^{1/2} R(α) Aᵢ^{1/2}` is not fixed: the
working-correlation parameter `α` and the scale `φ` are replaced by estimates `α̂(Y)`, `φ̂(Y)`
computed from the responses of all clusters. The weights then depend on `Y`, so the
fixed-weight unbiasedness of `Unbiasedness.lean` (`integral_geeEstFun_eq_zero`) and the
independent-cluster sandwich CLT of `Sandwich.lean` do not apply directly: the
estimated-weight cluster scores are no longer independent, and `E[U(β₀; α̂(Y))] = 0` can fail
in finite samples (see the tests). Liang and Zeger (1986, Theorem 2) show that unbiasedness and
the sandwich covariance are recovered asymptotically. This file proves that recovery.

Throughout, `U i β θ ω ∈ E` is the score of cluster `i` at regression parameter `β ∈ E` (a
finite-dimensional real inner product space) and nuisance parameter `θ ∈ F` (a real normed space;
`θ = (α, φ)` collects the working correlation and the scale), and `θhat n ω` is an arbitrary
random nuisance estimate, which may depend on every cluster and on a preliminary estimate of `β`.
The nuisance limit `θ₀` is the probability limit of `θhat`; the working correlation at `θ₀` need
not be the true correlation.

## Main results

* `tendstoInMeasure_inv_sqrt_smul_sum_sub_of_hasFDerivAt` (**asymptotic unbiasedness
  recovered**): if the scores are differentiable in `θ` near `θ₀`, the averaged nuisance
  derivative `n⁻¹ • ∑_{i<n} ∂U i β₀ θ/∂θ` tends to `0` uniformly near `θ₀` in probability, and
  `√n • (θhat n - θ₀)` is bounded in probability, then
  `(√n)⁻¹ • ∑ U i β₀ (θhat n) - (√n)⁻¹ • ∑ U i β₀ θ₀ → 0` in probability.
* `integral_nuisanceDeriv_eq_zero`, `hasFDerivAt_apply_residual`: for a score linear in the
  residual, `U i β₀ θ = L θ (Yᵢ - μᵢ(β₀))` (for GEE `L θ = Dᵢᵀ Vᵢ(θ)⁻¹`), the nuisance derivative
  is `h ↦ L' h (Yᵢ - μᵢ(β₀))`, which has mean zero whenever the mean model is correct, for every
  nuisance value. This is why the averaged nuisance derivative tends to `0`.
* `tendstoInDistribution_inv_sqrt_smul_sum_estimatedWeights`: the estimated-weight score
  `(√n)⁻¹ • ∑ U i β₀ (θhat n)` has the same centered Gaussian limit as the score with the
  nuisance fixed at `θ₀`.
* `tendstoInDistribution_sqrt_smul_sub_sandwich_estimatedWeights` (**sandwich with estimated
  weights**, Liang–Zeger Theorem 2): a root `βhat n` of `∑ U i β (θhat n) = 0` that linearizes in
  `β` with invertible derivative `A` satisfies `√n • (βhat n - β₀) → N(0, A⁻¹ B A⁻ᵀ)`, the
  sandwich of `Sandwich.lean` at the fixed nuisance `θ₀`.
  `linearization_estimatedWeights_of_hasFDerivAt` proves the linearization from
  differentiability in `β` and uniform convergence of the averaged Jacobian near `(β₀, θ₀)`, and
  `tendstoInDistribution_sqrt_smul_sub_sandwich_estimatedWeights_of_hasFDerivAt` combines them.
* `tendstoInMeasure_empirical_sandwichCovariance_estimatedWeights`: the empirical sandwich with
  plug-in `(βhat n, θhat n)` converges in probability to the sandwich at `(β₀, θ₀)`.
* Nuisance estimators: `tendstoInMeasure_of_sqrt_smul_sub_bounded` (`√n`-consistency implies
  consistency), `sqrt_smul_sub_bounded_prodMk` (combine `α̂` and `φ̂`), and
  `sqrt_smul_sub_bounded_of_lipschitz_plugin` (the role of Liang–Zeger condition (iii), which
  bounds `|∂α̂/∂φ|` by an `O_p(1)` variable; here the bound may cover all plug-in arguments, e.g.
  `(β̃, φ̂)`: an estimator `α̂(β̃, φ̂)` is `√n`-consistent when its plug-in arguments and its
  oracle version `α̂(β₀, φ₀)` are).

## Hypotheses that stay explicit, and what is not claimed

* The uniform law of large numbers for the averaged nuisance derivative (`hunif`) and for the
  averaged `β`-Jacobian is a hypothesis; `integral_nuisanceDeriv_eq_zero` identifies its limit
  as `0` but no uniform LLN is proved here.
* `√n`-consistency of `θhat` is a hypothesis (bounded in probability, in the form produced by
  `exists_forall_measure_lt_norm_le_of_tendstoInDistribution`). The theorems do not depend on how
  `θhat` is built. If `θhat = α̂(βhat)` is evaluated at the final root itself, its
  `√n`-consistency needs that of `βhat`; this file does not resolve that circularity, so the
  intended use is a preliminary `√n`-consistent `β̃` (for example the working-independence GEE)
  plugged into `α̂` through `sqrt_smul_sub_bounded_of_lipschitz_plugin`.
* Root existence, the cluster CLT hypotheses at `(β₀, θ₀)`, and invertibility of the bread are
  hypotheses, as in `Sandwich.lean`.
* Nothing is claimed about finite samples: `E[U(β₀; θhat)] ≠ 0` is possible (tests), and so is a
  finite-sample bias of `βhat`.

## Proof

The estimated-weight and fixed-weight normalized scores differ by
`√n • (f(θhat) - f(θ₀))` with `f θ = n⁻¹ • ∑ U i β₀ θ`. On the event where `‖√n (θhat - θ₀)‖ ≤ K`
(probability close to one for large `K`) and `n` is large, `θhat` lies in the ball, and the mean
value inequality bounds the difference by `η · K`, where `η` bounds the averaged nuisance
derivative on the ball, which is small with probability tending to one. Slutsky's lemma
(`tendstoInDistribution_of_tendstoInMeasure_sub`) then transfers the fixed-weight cluster CLT
`tendstoInDistribution_inv_sqrt_smul_sum_of_lindeberg` to the estimated-weight score. For the
estimator, the estimated-weight sums `Sₙ(β) = ∑_{i<n} U i β (θhat n)` depend on `n` through
`θhat n`; writing them as partial sums of the telescoping sequence `S_{i+1} - S_i` reduces to the
fixed-index linearization theorem `tendstoInDistribution_sqrt_smul_sub_of_linearization`.
Sandwich consistency is `tendstoInMeasure_sandwichCovariance` applied to the plug-in lemma
`tendstoInMeasure_comp_of_tendstoUniformlyOn` on the product parameter space `E × F`.

## Source receipt

* K.-Y. Liang and S. L. Zeger, *Longitudinal data analysis using generalized linear models*,
  Biometrika 73 (1986), 13–22: Theorem 2 (asymptotic normality of the GEE estimator with
  `α̂(Y, β, φ)` and `φ̂(Y, β)` `√n`-consistent and `|∂α̂/∂φ| = O_p(1)`, with the sandwich
  covariance unchanged), and its proof in the Appendix, where the term
  `n^{-1} ∑ ∂Uᵢ/∂α · √n (α̂ - α)` is `o_p(1)` because `∂Uᵢ/∂α` is linear in `Sᵢ = Yᵢ - μᵢ` and
  so has mean zero.
* A. W. van der Vaart, *Asymptotic Statistics* (1998), §5.3 (asymptotic normality of
  Z-estimators).

Reuse search (API-00 gate, 2026-11-12, base `1686a6b76`): pinned Mathlib `v4.35.0` and this
repository have no estimated-nuisance Z-estimator, plug-in working-correlation, or
`O_p`/bounded-in-probability API; the T34/T35 files cover fixed weights only (their docstrings
defer the plug-in case). Reused: `tendstoInDistribution_inv_sqrt_smul_sum_of_lindeberg`,
`tendstoInDistribution_sqrt_smul_sub_of_linearization`, `sandwichCovariance`,
`inner_sandwichCovariance_apply`, `tendstoInMeasure_sandwichCovariance`,
`tendstoInMeasure_comp_of_tendstoUniformlyOn` (`Sandwich.lean`);
`TendstoInMeasure.comp_const_of_continuousAt` (`Slutsky.lean`); Mathlib's
`tendstoInDistribution_of_tendstoInMeasure_sub`,
`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`, `Finset.sum_range_sub` and
`ContinuousLinearMap.integral_comp_comm`.
-/

@[expose] public section

open MeasureTheory Filter Finset RealInnerProductSpace
open scoped Real Topology ENNReal

namespace ProbabilityTheory.GEE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/-! ### `√n`-consistent nuisance estimators -/

omit [IsProbabilityMeasure P] in
/-- A `√n`-consistent estimator is consistent: if `√n • (θhat n - θ₀)` is bounded in
probability (for every `ε > 0` there is a radius `K` with `P {K < ‖√n • (θhat n - θ₀)‖} ≤ ε`
for all `n`), then `θhat n → θ₀` in probability. -/
theorem tendstoInMeasure_of_sqrt_smul_sub_bounded {θhat : ℕ → Ω → F} {θ₀ : F}
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℝ, ∀ n : ℕ,
      P {ω | K < ‖√(n : ℝ) • (θhat n ω - θ₀)‖} ≤ ε) :
    TendstoInMeasure P θhat atTop (fun _ ↦ θ₀) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  obtain ⟨K, hK⟩ := htight δ hδ
  have hsqrt : Tendsto (fun n : ℕ ↦ √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hsqrt.eventually_gt_atTop (K / ε)] with n hn
  refine (measure_mono fun ω hω ↦ ?_).trans (hK n)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  calc K = K / ε * ε := by field_simp
    _ < √(n : ℝ) * ε := mul_lt_mul_of_pos_right hn hε
    _ ≤ √(n : ℝ) * ‖θhat n ω - θ₀‖ := by gcongr

omit [IsProbabilityMeasure P] in
/-- **Joint `√n`-consistency from the components.** If `√n • (αhat n - α₀)` and
`√n • (φhat n - φ₀)` are bounded in probability, so is `√n • ((αhat n, φhat n) - (α₀, φ₀))` (in
the sup norm of the product). This combines a working-correlation estimator `α̂` and a scale
estimator `φ̂` into one nuisance estimator `θ̂ = (α̂, φ̂)`. -/
theorem sqrt_smul_sub_bounded_prodMk {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {αhat : ℕ → Ω → F} {α₀ : F} {φhat : ℕ → Ω → G} {φ₀ : G}
    (hα : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℝ, ∀ n : ℕ,
      P {ω | K < ‖√(n : ℝ) • (αhat n ω - α₀)‖} ≤ ε)
    (hφ : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℝ, ∀ n : ℕ,
      P {ω | K < ‖√(n : ℝ) • (φhat n ω - φ₀)‖} ≤ ε) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℝ, ∀ n : ℕ,
      P {ω | K < ‖√(n : ℝ) • ((αhat n ω, φhat n ω) - (α₀, φ₀))‖} ≤ ε := by
  intro ε hε
  obtain ⟨K₁, hK₁⟩ := hα (ε / 2) (ENNReal.half_pos hε.ne')
  obtain ⟨K₂, hK₂⟩ := hφ (ε / 2) (ENNReal.half_pos hε.ne')
  refine ⟨max K₁ K₂, fun n ↦ ?_⟩
  refine (measure_mono (t := {ω | K₁ < ‖√(n : ℝ) • (αhat n ω - α₀)‖} ∪
    {ω | K₂ < ‖√(n : ℝ) • (φhat n ω - φ₀)‖}) fun ω hω ↦ ?_).trans
    (((measure_union_le _ _).trans (add_le_add (hK₁ n) (hK₂ n))).trans_eq (ENNReal.add_halves ε))
  simp only [Set.mem_ofPred_eq, Prod.mk_sub_mk, Prod.smul_mk, Prod.norm_mk, Set.mem_union] at hω ⊢
  by_contra hcon
  push Not at hcon
  exact hω.not_ge (max_le_max hcon.1 hcon.2)

omit [IsProbabilityMeasure P] in
/-- **Plug-in of a `√n`-consistent argument into a locally Lipschitz estimator** (the role of
condition (iii) of Liang and Zeger's Theorem 2). Suppose the estimator `ahat n` differs from an
oracle version `atilde n` (the same estimator evaluated at the true values of its plug-in
arguments) by at most `H n · ‖bhat n - b₀‖`, where the random Lipschitz factor `H n` is bounded in
probability and `√n • (bhat n - b₀)` is bounded in probability. If the oracle is
`√n`-consistent, `√n • (atilde n - a₀)` bounded in probability, then so is
`√n • (ahat n - a₀)`.

For the working correlation, `ahat n = α̂(β̃, φ̂)` with plug-in `b = (β, φ)`,
`atilde n = α̂(β₀, φ₀)`, and `H` a bound on the derivative of `α̂` in `(β, φ)`. -/
theorem sqrt_smul_sub_bounded_of_lipschitz_plugin {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {ahat atilde : ℕ → Ω → F} {a₀ : F} {bhat : ℕ → Ω → G} {b₀ : G}
    {H : ℕ → Ω → ℝ} (hlip : ∀ n ω, ‖ahat n ω - atilde n ω‖ ≤ H n ω * ‖bhat n ω - b₀‖)
    (hH : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℝ, ∀ n : ℕ, P {ω | K < H n ω} ≤ ε)
    (hb : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℝ, ∀ n : ℕ,
      P {ω | K < ‖√(n : ℝ) • (bhat n ω - b₀)‖} ≤ ε)
    (ha : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℝ, ∀ n : ℕ,
      P {ω | K < ‖√(n : ℝ) • (atilde n ω - a₀)‖} ≤ ε) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℝ, ∀ n : ℕ,
      P {ω | K < ‖√(n : ℝ) • (ahat n ω - a₀)‖} ≤ ε := by
  intro ε hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  have hε4 : 0 < ε / 2 / 2 := ENNReal.half_pos hε2.ne'
  obtain ⟨K₁, hK₁⟩ := hH _ hε4
  obtain ⟨K₂, hK₂⟩ := hb _ hε4
  obtain ⟨K₃, hK₃⟩ := ha _ hε2
  refine ⟨max K₁ 0 * max K₂ 0 + K₃, fun n ↦ ?_⟩
  refine (measure_mono (t := ({ω | K₁ < H n ω} ∪ {ω | K₂ < ‖√(n : ℝ) • (bhat n ω - b₀)‖}) ∪
    {ω | K₃ < ‖√(n : ℝ) • (atilde n ω - a₀)‖}) fun ω hω ↦ ?_).trans ?_
  · simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
    have hs : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
    have hdiff : ‖√(n : ℝ) • (ahat n ω - atilde n ω)‖ ≤ max K₁ 0 * max K₂ 0 := by
      rw [norm_smul, Real.norm_of_nonneg hs]
      calc √(n : ℝ) * ‖ahat n ω - atilde n ω‖ ≤ √(n : ℝ) * (H n ω * ‖bhat n ω - b₀‖) := by
            gcongr
            exact hlip n ω
        _ = H n ω * ‖√(n : ℝ) • (bhat n ω - b₀)‖ := by
            rw [norm_smul, Real.norm_of_nonneg hs]
            ring
        _ ≤ max K₁ 0 * ‖√(n : ℝ) • (bhat n ω - b₀)‖ := by
            gcongr
            exact h1.trans (le_max_left _ _)
        _ ≤ max K₁ 0 * max K₂ 0 := by
            gcongr
            exact h2.trans (le_max_left _ _)
    have hsplit : √(n : ℝ) • (ahat n ω - a₀) =
        √(n : ℝ) • (ahat n ω - atilde n ω) + √(n : ℝ) • (atilde n ω - a₀) := by
      rw [← smul_add, sub_add_sub_cancel]
    rw [hsplit] at hω
    exact hω.not_ge ((norm_add_le _ _).trans (add_le_add hdiff h3))
  · calc _ ≤ P ({ω | K₁ < H n ω} ∪ {ω | K₂ < ‖√(n : ℝ) • (bhat n ω - b₀)‖}) +
          P {ω | K₃ < ‖√(n : ℝ) • (atilde n ω - a₀)‖} := measure_union_le _ _
      _ ≤ (ε / 2 / 2 + ε / 2 / 2) + ε / 2 := by
          gcongr
          · exact (measure_union_le _ _).trans (add_le_add (hK₁ n) (hK₂ n))
          · exact hK₃ n
      _ = ε := by rw [ENNReal.add_halves, ENNReal.add_halves]

omit [IsProbabilityMeasure P] in
/-- Convergence in probability of a pair from convergence of its components. -/
private lemma tendstoInMeasure_prodMk {G H : Type*} [PseudoMetricSpace G] [PseudoMetricSpace H]
    {f : ℕ → Ω → G} {g : ℕ → Ω → H} {a : G} {b : H}
    (hf : TendstoInMeasure P f atTop (fun _ ↦ a)) (hg : TendstoInMeasure P g atTop (fun _ ↦ b)) :
    TendstoInMeasure P (fun n ω ↦ (f n ω, g n ω)) atTop (fun _ ↦ (a, b)) := by
  rw [tendstoInMeasure_iff_dist] at hf hg ⊢
  intro ε hε
  have hsum := (hf ε hε).add (hg ε hε)
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ ↦ zero_le)
    fun n ↦ (measure_mono fun ω hω ↦ ?_).trans (measure_union_le _ _)
  simp only [Set.mem_ofPred_eq, Set.mem_union, Prod.dist_eq] at hω ⊢
  by_contra hcon
  push Not at hcon
  exact hω.not_gt (max_lt hcon.1 hcon.2)

/-! ### The nuisance derivative of a score linear in the residual is unbiased -/

/-- **Nuisance derivative of a residual-linear score.** If the score at nuisance value `θ` is
`L θ r` for a weight `L θ : R →L[ℝ] E` applied to a residual `r` (for GEE,
`L θ r = Dᵀ V(θ)⁻¹ r`), and `L` has derivative `L'` at `θ`, then the score is differentiable in
`θ` with derivative `h ↦ L' h r`. -/
theorem hasFDerivAt_apply_residual {R S : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
    [NormedAddCommGroup S] [NormedSpace ℝ S] {L : F → R →L[ℝ] S} {L' : F →L[ℝ] R →L[ℝ] S}
    {θ : F} (hL : HasFDerivAt L L' θ) (r : R) :
    HasFDerivAt (fun a ↦ L a r) ((ContinuousLinearMap.apply ℝ S r).comp L') θ :=
  (ContinuousLinearMap.apply ℝ S r).hasFDerivAt.comp θ hL

omit [IsProbabilityMeasure P] in
/-- **The nuisance derivative has mean zero** (the reason the plug-in nuisance is
asymptotically negligible). If the residual `Rᵢ = Yᵢ - μᵢ(β₀)` is integrable with mean zero (a
correct mean model at `β₀`), then every directional nuisance derivative `L' h Rᵢ` of the
residual-linear score `θ ↦ L θ Rᵢ` has mean zero, for every nuisance value at which the
derivative `L'` is taken. The working correlation need not be correct. -/
theorem integral_nuisanceDeriv_eq_zero {R S : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
    [CompleteSpace R] [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
    (L' : F →L[ℝ] R →L[ℝ] S) {res : Ω → R}
    (hres : Integrable res P) (hmean : ∫ ω, res ω ∂P = 0) (h : F) :
    ∫ ω, L' h (res ω) ∂P = 0 := by
  rw [(L' h).integral_comp_comm hres, hmean, map_zero]

/-! ### Asymptotic equivalence of estimated-weight and fixed-weight scores -/

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [IsProbabilityMeasure P] in
/-- **Plugging in a `√n`-consistent nuisance estimator does not change the normalized score**
(Liang and Zeger 1986, proof of Theorem 2). Let `U i β θ ω` be the score of cluster `i` at
regression parameter `β` and nuisance parameter `θ` (working correlation and scale), and let
`θhat n` be any random nuisance estimate, which may depend on all responses. Assume

* the scores at `β₀` are differentiable in `θ` on a ball around `θ₀`, with derivative
  `DθU i θ ω`;
* the averaged nuisance derivative tends to `0` uniformly on the ball in probability: for every
  `ε > 0`, `P {∃ θ ∈ ball θ₀ δ, ε ≤ ‖n⁻¹ • ∑_{i<n} DθU i θ‖} → 0` (a uniform law of large
  numbers for variables of mean zero, see `integral_nuisanceDeriv_eq_zero`);
* `√n • (θhat n - θ₀)` is bounded in probability.

Then `(√n)⁻¹ • ∑_{i<n} U i β₀ (θhat n) - (√n)⁻¹ • ∑_{i<n} U i β₀ θ₀ → 0` in probability. -/
theorem tendstoInMeasure_inv_sqrt_smul_sum_sub_of_hasFDerivAt {U : ℕ → E → F → Ω → E}
    {DθU : ℕ → F → Ω → F →L[ℝ] E} {β₀ : E} {θ₀ : F} {δ : ℝ} (hδ : 0 < δ)
    (hdiff : ∀ i ω, ∀ θ ∈ Metric.ball θ₀ δ, HasFDerivAt (fun a ↦ U i β₀ a ω) (DθU i θ ω) θ)
    (hunif : ∀ ε > 0, Tendsto (fun n : ℕ ↦ P {ω | ∃ θ ∈ Metric.ball θ₀ δ,
      ε ≤ ‖(n : ℝ)⁻¹ • ∑ i ∈ range n, DθU i θ ω‖}) atTop (𝓝 0))
    {θhat : ℕ → Ω → F}
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℝ, ∀ n : ℕ,
      P {ω | K < ‖√(n : ℝ) • (θhat n ω - θ₀)‖} ≤ ε) :
    TendstoInMeasure P (fun (n : ℕ) ω ↦ (√n)⁻¹ • ∑ i ∈ range n, U i β₀ (θhat n ω) ω -
      (√n)⁻¹ • ∑ i ∈ range n, U i β₀ θ₀ ω) atTop 0 := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro ρ hρ
  obtain ⟨K₀, hK₀⟩ := htight (ρ / 2) (ENNReal.half_pos hρ.ne')
  set K := max K₀ 0
  have hK : 0 ≤ K := le_max_right _ _
  set η := ε / (K + 1)
  have hη : 0 < η := by positivity
  have hηK : η * K < ε := by
    have : η * (K + 1) = ε := by simp only [η]; field_simp
    nlinarith
  have hsqrt : Tendsto (fun n : ℕ ↦ √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hsqrt.eventually_gt_atTop (K / δ),
    (hunif η hη).eventually (eventually_le_nhds (ENNReal.half_pos hρ.ne'))] with n hn hn'
  refine (measure_mono (t := {ω | K₀ < ‖√(n : ℝ) • (θhat n ω - θ₀)‖} ∪
    {ω | ∃ θ ∈ Metric.ball θ₀ δ, η ≤ ‖(n : ℝ)⁻¹ • ∑ i ∈ range n, DθU i θ ω‖})
    fun ω hω ↦ ?_).trans ?_
  · simp only [Set.mem_ofPred_eq, Pi.zero_apply, sub_zero, Set.mem_union] at hω ⊢
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hs : 0 < √(n : ℝ) := (div_nonneg hK hδ.le).trans_lt hn
    have hnK : ‖√(n : ℝ) • (θhat n ω - θ₀)‖ ≤ K := h1.trans (le_max_left _ _)
    rw [norm_smul, Real.norm_of_nonneg hs.le] at hnK
    have hball : θhat n ω ∈ Metric.ball θ₀ δ := by
      rw [Metric.mem_ball, dist_eq_norm]
      have h3 : K < √(n : ℝ) * δ := by
        have := (div_lt_iff₀ hδ).1 hn
        linarith
      by_contra h4
      push Not at h4
      nlinarith
    set f : F → E := fun a ↦ (n : ℝ)⁻¹ • ∑ i ∈ range n, U i β₀ a ω
    set f' : F → F →L[ℝ] E := fun a ↦ (n : ℝ)⁻¹ • ∑ i ∈ range n, DθU i a ω
    have hf : ∀ a ∈ Metric.ball θ₀ δ, HasFDerivWithinAt f (f' a) (Metric.ball θ₀ δ) a :=
      fun a ha ↦ ((HasFDerivAt.fun_sum fun i _ ↦ hdiff i ω a ha).fun_const_smul
        ((n : ℝ)⁻¹)).hasFDerivWithinAt
    have hmv := (convex_ball θ₀ δ).norm_image_sub_le_of_norm_hasFDerivWithin_le hf
      (fun a ha ↦ (h2 a ha).le) (Metric.mem_ball_self hδ) hball
    have hsq : √(n : ℝ) * (n : ℝ)⁻¹ = (√(n : ℝ))⁻¹ := by
      rw [← div_eq_mul_inv, Real.sqrt_div_self', one_div]
    have heq : (√(n : ℝ))⁻¹ • ∑ i ∈ range n, U i β₀ (θhat n ω) ω -
        (√(n : ℝ))⁻¹ • ∑ i ∈ range n, U i β₀ θ₀ ω = √(n : ℝ) • (f (θhat n ω) - f θ₀) := by
      simp only [f, ← smul_sub, smul_smul, hsq]
    rw [heq, norm_smul, Real.norm_of_nonneg hs.le] at hω
    have : √(n : ℝ) * ‖f (θhat n ω) - f θ₀‖ < ε :=
      calc √(n : ℝ) * ‖f (θhat n ω) - f θ₀‖ ≤ √(n : ℝ) * (η * ‖θhat n ω - θ₀‖) := by gcongr
        _ = η * (√(n : ℝ) * ‖θhat n ω - θ₀‖) := by ring
        _ ≤ η * K := by gcongr
        _ < ε := hηK
    exact this.not_ge hω
  · exact ((measure_union_le _ _).trans (add_le_add (hK₀ n) hn')).trans_eq (ENNReal.add_halves ρ)

/-- **Central limit theorem for the estimated-weight score** (asymptotic unbiasedness
recovered). Under the hypotheses of `tendstoInMeasure_inv_sqrt_smul_sum_sub_of_hasFDerivAt` on
the nuisance, and the cluster CLT hypotheses of
`tendstoInDistribution_inv_sqrt_smul_sum_of_lindeberg` for the scores `U k β₀ θ₀` at the
limiting nuisance value `θ₀`, the estimated-weight score `(√n)⁻¹ • ∑_{i<n} U i β₀ (θhat n)`
converges in distribution to the same centered limit `Y` as with the nuisance known. In finite
samples the estimated-weight score need not have mean zero (see the tests); its limit does. -/
theorem tendstoInDistribution_inv_sqrt_smul_sum_estimatedWeights {U : ℕ → E → F → Ω → E}
    {DθU : ℕ → F → Ω → F →L[ℝ] E} {β₀ : E} {θ₀ : F} {δ : ℝ} (hδ : 0 < δ)
    (hdiff : ∀ i ω, ∀ θ ∈ Metric.ball θ₀ δ, HasFDerivAt (fun a ↦ U i β₀ a ω) (DθU i θ ω) θ)
    (hunif : ∀ ε > 0, Tendsto (fun n : ℕ ↦ P {ω | ∃ θ ∈ Metric.ball θ₀ δ,
      ε ≤ ‖(n : ℝ)⁻¹ • ∑ i ∈ range n, DθU i θ ω‖}) atTop (𝓝 0))
    {θhat : ℕ → Ω → F}
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℝ, ∀ n : ℕ,
      P {ω | K < ‖√(n : ℝ) • (θhat n ω - θ₀)‖} ≤ ε)
    (hSmeas : ∀ n, AEMeasurable (fun ω ↦ ∑ i ∈ range n, U i β₀ (θhat n ω) ω) P)
    {Y : Ω' → E} {q : E → ℝ} (hY : AEMeasurable Y P')
    (hYlaw : ∀ t, HasLaw (fun ω ↦ ⟪Y ω, t⟫) (gaussianReal 0 (q t).toNNReal) P')
    (hmeas : ∀ k, Measurable (U k β₀ θ₀)) (hindep : iIndepFun (fun k ↦ U k β₀ θ₀) P)
    (hmean : ∀ k, ∫ ω, U k β₀ θ₀ ω ∂P = 0) (hL2 : ∀ k, MemLp (U k β₀ θ₀) 2 P)
    (hvar : ∀ t, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, ∫ ω, ⟪U k β₀ θ₀ ω, t⟫ ^ 2 ∂P)
      atTop (𝓝 (q t)))
    (hL : ∀ t, LindebergConditionTriangular (fun n k ω ↦ (√n)⁻¹ * ⟪U k β₀ θ₀ ω, t⟫) P) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ (√n)⁻¹ • ∑ i ∈ range n, U i β₀ (θhat n ω) ω) atTop Y
      (fun _ ↦ P) P' :=
  tendstoInDistribution_of_tendstoInMeasure_sub _ Y
    (tendstoInDistribution_inv_sqrt_smul_sum_of_lindeberg (U := fun k ↦ U k β₀ θ₀) hY hYlaw
      hmeas hindep hmean hL2 hvar hL)
    (tendstoInMeasure_inv_sqrt_smul_sum_sub_of_hasFDerivAt hδ hdiff hunif htight)
    fun n ↦ (hSmeas n).const_smul _

/-! ### Asymptotic normality and the sandwich with estimated weights -/

/-- **GEE asymptotic normality with estimated working-correlation weights** (Liang and Zeger
1986, Theorem 2). Let `U i β θ` be the cluster scores, `θhat n` a random nuisance estimate
(working correlation and scale, possibly depending on all responses and on a preliminary
estimate of `β`), and `βhat n` a root of the estimated-weight equation
`∑_{i<n} U i (βhat n) (θhat n) = 0` with probability tending to one that linearizes in `β` with
an invertible derivative `A`:
`‖n⁻¹ • (∑ U i (βhat n) (θhat n) - ∑ U i β₀ (θhat n)) - A (βhat n - β₀)‖ ≤ ε ‖βhat n - β₀‖`
with probability tending to one, for every `ε > 0`. Assume the nuisance hypotheses of
`tendstoInMeasure_inv_sqrt_smul_sum_sub_of_hasFDerivAt` (the averaged nuisance derivative is
asymptotically negligible and `θhat` is `√n`-consistent for `θ₀`) and the cluster CLT hypotheses
at `(β₀, θ₀)` with meat quadratic form `⟪B t, t⟫`. Then
`√n • (βhat n - β₀) → N(0, sandwichCovariance A B)` in distribution: the same sandwich as with
the nuisance fixed at its limit `θ₀`. The working correlation at `θ₀` need not be the true
correlation. -/
theorem tendstoInDistribution_sqrt_smul_sub_sandwich_estimatedWeights {U : ℕ → E → F → Ω → E}
    {DθU : ℕ → F → Ω → F →L[ℝ] E} {β₀ : E} {θ₀ : F} {δ : ℝ} (hδ : 0 < δ)
    {A B : E →L[ℝ] E} (hA : IsUnit A)
    (hmeas : ∀ k, Measurable (U k β₀ θ₀)) (hindep : iIndepFun (fun k ↦ U k β₀ θ₀) P)
    (hmean : ∀ k, ∫ ω, U k β₀ θ₀ ω ∂P = 0) (hL2 : ∀ k, MemLp (U k β₀ θ₀) 2 P)
    (hvar : ∀ t, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, ∫ ω, ⟪U k β₀ θ₀ ω, t⟫ ^ 2 ∂P)
      atTop (𝓝 ⟪B t, t⟫))
    (hL : ∀ t, LindebergConditionTriangular (fun n k ω ↦ (√n)⁻¹ * ⟪U k β₀ θ₀ ω, t⟫) P)
    (hdiff : ∀ i ω, ∀ θ ∈ Metric.ball θ₀ δ, HasFDerivAt (fun a ↦ U i β₀ a ω) (DθU i θ ω) θ)
    (hunif : ∀ ε > 0, Tendsto (fun n : ℕ ↦ P {ω | ∃ θ ∈ Metric.ball θ₀ δ,
      ε ≤ ‖(n : ℝ)⁻¹ • ∑ i ∈ range n, DθU i θ ω‖}) atTop (𝓝 0))
    {θhat : ℕ → Ω → F}
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℝ, ∀ n : ℕ,
      P {ω | K < ‖√(n : ℝ) • (θhat n ω - θ₀)‖} ≤ ε)
    (hSmeas : ∀ n, AEMeasurable (fun ω ↦ ∑ i ∈ range n, U i β₀ (θhat n ω) ω) P)
    {βhat : ℕ → Ω → E} (hβ : ∀ n, AEMeasurable (βhat n) P)
    (hroot : Tendsto (fun n ↦ P {ω | ∑ i ∈ range n, U i (βhat n ω) (θhat n ω) ω ≠ 0}) atTop
      (𝓝 0))
    (hlin : ∀ ε > 0, Tendsto (fun n : ℕ ↦ P {ω | ε * ‖βhat n ω - β₀‖ <
      ‖(n : ℝ)⁻¹ • (∑ i ∈ range n, U i (βhat n ω) (θhat n ω) ω -
        ∑ i ∈ range n, U i β₀ (θhat n ω) ω) - A (βhat n ω - β₀)‖}) atTop (𝓝 0))
    {W : Ω' → E} (hW : AEMeasurable W P')
    (hWlaw : ∀ t, HasLaw (fun ω ↦ ⟪W ω, t⟫)
      (gaussianReal 0 (⟪sandwichCovariance A B t, t⟫).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √n • (βhat n ω - β₀)) atTop W (fun _ ↦ P) P' := by
  set Ai := Ring.inverse A with hAi_def
  -- the cluster CLT for the transformed fixed-nuisance scores `-A⁻¹ U k β₀ θ₀`
  set s : E → E := fun t ↦ -ContinuousLinearMap.adjoint Ai t with hs_def
  set V : ℕ → Ω → E := fun k ω ↦ -Ai (U k β₀ θ₀ ω) with hV_def
  have hVinner : ∀ k ω t, ⟪V k ω, t⟫ = ⟪U k β₀ θ₀ ω, s t⟫ := by
    intro k ω t
    simp only [hV_def, hs_def, inner_neg_left, inner_neg_right,
      ContinuousLinearMap.adjoint_inner_right]
  have hq : ∀ t, ⟪B (s t), s t⟫ = ⟪sandwichCovariance A B t, t⟫ := by
    intro t
    simp only [hs_def, map_neg, inner_neg_neg, inner_sandwichCovariance_apply, hAi_def]
  have hCLT : TendstoInDistribution (fun (n : ℕ) ω ↦ (√n)⁻¹ • ∑ k ∈ range n, V k ω) atTop W
      (fun _ ↦ P) P' := by
    refine tendstoInDistribution_inv_sqrt_smul_sum_of_lindeberg hW hWlaw
      (fun k ↦ (Ai.continuous.measurable.comp (hmeas k)).neg)
      (hindep.comp (fun _ x ↦ -Ai x) fun _ ↦ Ai.continuous.measurable.neg)
      (fun k ↦ ?_) (fun k ↦ ((hL2 k).continuousLinearMap_comp Ai).neg) (fun t ↦ ?_)
      (fun t ↦ ?_)
    · simp only [hV_def, integral_neg, Ai.integral_comp_comm ((hL2 k).integrable one_le_two),
        hmean k, map_zero, neg_zero]
    · simp_rw [hVinner, ← hq]
      exact hvar (s t)
    · simp_rw [hVinner]
      exact hL (s t)
  have hX0 : TendstoInDistribution
      (fun (n : ℕ) ω ↦ -Ai ((√n)⁻¹ • ∑ i ∈ range n, U i β₀ θ₀ ω)) atTop W (fun _ ↦ P) P' := by
    refine hCLT.congr (fun n ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun _ ↦ rfl)
    simp only [hV_def, map_smul, map_sum, smul_neg, Finset.sum_neg_distrib]
  -- plugging in `θhat` changes the transformed score sums by `o_p(1)`
  have hX : TendstoInDistribution
      (fun (n : ℕ) ω ↦ -Ai ((√n)⁻¹ • ∑ i ∈ range n, U i β₀ (θhat n ω) ω)) atTop W
      (fun _ ↦ P) P' := by
    refine tendstoInDistribution_of_tendstoInMeasure_sub _ W hX0 ?_
      fun n ↦ (Ai.continuous.measurable.comp_aemeasurable ((hSmeas n).const_smul _)).neg
    have h1 := tendstoInMeasure_inv_sqrt_smul_sum_sub_of_hasFDerivAt hδ hdiff hunif htight
    have h2 := TendstoInMeasure.comp_const_of_continuousAt (f := fun x : E ↦ -Ai x) (c := 0)
      Ai.continuous.neg.continuousAt h1
    simp only [map_zero, neg_zero] at h2
    refine h2.congr_left fun n ↦ ae_of_all _ fun ω ↦ ?_
    simp only [Pi.sub_apply, map_sub, neg_sub_neg, neg_sub]
  -- the estimated-weight sums are the partial sums of a telescoping sequence
  set S : ℕ → E → Ω → E := fun n β ω ↦ ∑ i ∈ range n, U i β (θhat n ω) ω with hS_def
  set U' : ℕ → E → Ω → E := fun i β ω ↦ S (i + 1) β ω - S i β ω with hU'_def
  have hsum : ∀ n β ω, ∑ i ∈ range n, U' i β ω = S n β ω := by
    intro n β ω
    rw [Finset.sum_range_sub (fun i ↦ S i β ω) n]
    simp [hS_def]
  refine tendstoInDistribution_sqrt_smul_sub_of_linearization (U := U') hA ?_ hβ ?_ ?_
  · simp_rw [hsum]
    exact hX
  · simp_rw [hsum]
    exact hroot
  · intro ε hε
    simp_rw [hsum]
    exact hlin ε hε

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [NormedSpace ℝ F]
  [IsProbabilityMeasure P] in
/-- **Linearization with estimated weights from differentiability (proved input).** If each
cluster score is differentiable in `β` near `β₀` for every nuisance value near `θ₀`, with
derivative `DU i β θ ω`, the averaged Jacobian `n⁻¹ • ∑ DU i β θ` converges uniformly near
`(β₀, θ₀)` in probability to a sensitivity function `Abar (β, θ)` continuous at `(β₀, θ₀)`, and
`βhat n → β₀`, `θhat n → θ₀` in probability, then the estimated-weight estimating function
linearizes along `βhat` with derivative `Abar (β₀, θ₀)`: this is the hypothesis `hlin` of
`tendstoInDistribution_sqrt_smul_sub_sandwich_estimatedWeights`. -/
theorem linearization_estimatedWeights_of_hasFDerivAt {U : ℕ → E → F → Ω → E}
    {DU : ℕ → E → F → Ω → E →L[ℝ] E} {β₀ : E} {θ₀ : F} {δ : ℝ} (hδ : 0 < δ)
    (hdiff : ∀ i ω, ∀ θ ∈ Metric.ball θ₀ δ, ∀ β ∈ Metric.ball β₀ δ,
      HasFDerivAt (fun b ↦ U i b θ ω) (DU i β θ ω) β)
    {Abar : E × F → E →L[ℝ] E} (hAbar : ContinuousAt Abar (β₀, θ₀))
    (hunif : ∀ ε > 0, Tendsto (fun n : ℕ ↦ P {ω | ∃ p ∈ Metric.ball (β₀, θ₀) δ,
      ε ≤ ‖(n : ℝ)⁻¹ • ∑ i ∈ range n, DU i p.1 p.2 ω - Abar p‖}) atTop (𝓝 0))
    {βhat : ℕ → Ω → E} {θhat : ℕ → Ω → F}
    (hβcons : TendstoInMeasure P βhat atTop (fun _ ↦ β₀))
    (hθcons : TendstoInMeasure P θhat atTop (fun _ ↦ θ₀)) :
    ∀ ε > 0, Tendsto (fun n : ℕ ↦ P {ω | ε * ‖βhat n ω - β₀‖ <
      ‖(n : ℝ)⁻¹ • (∑ i ∈ range n, U i (βhat n ω) (θhat n ω) ω -
        ∑ i ∈ range n, U i β₀ (θhat n ω) ω) - Abar (β₀, θ₀) (βhat n ω - β₀)‖}) atTop (𝓝 0) := by
  intro ε hε
  have hcons := tendstoInMeasure_prodMk hβcons hθcons
  rw [tendstoInMeasure_iff_dist] at hcons
  obtain ⟨r₀, hr₀, hAr⟩ := Metric.continuousAt_iff.1 hAbar (ε / 2) (half_pos hε)
  set r := min r₀ δ
  have hr : 0 < r := lt_min hr₀ hδ
  have hsum := (hcons r hr).add (hunif (ε / 2) (half_pos hε))
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ ↦ zero_le)
    fun n ↦ (measure_mono fun ω hω ↦ ?_).trans (measure_union_le _ _)
  simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [Prod.dist_eq] at h1
  have hβr : dist (βhat n ω) β₀ < r := (le_max_left _ _).trans_lt h1
  have hθr : dist (θhat n ω) θ₀ < r := (le_max_right _ _).trans_lt h1
  have hθδ : θhat n ω ∈ Metric.ball θ₀ δ :=
    Metric.mem_ball.2 (hθr.trans_le (min_le_right _ _))
  have hsub : Metric.ball β₀ r ⊆ Metric.ball β₀ δ := Metric.ball_subset_ball (min_le_right _ _)
  have hpair : ∀ b ∈ Metric.ball β₀ r, dist ((b, θhat n ω) : E × F) (β₀, θ₀) < r := by
    intro b hb
    rw [Prod.dist_eq]
    exact max_lt (Metric.mem_ball.1 hb) hθr
  set f : E → E := fun b ↦ (n : ℝ)⁻¹ • ∑ i ∈ range n, U i b (θhat n ω) ω - Abar (β₀, θ₀) b
  set f' : E → E →L[ℝ] E := fun b ↦
    (n : ℝ)⁻¹ • ∑ i ∈ range n, DU i b (θhat n ω) ω - Abar (β₀, θ₀)
  have hf : ∀ b ∈ Metric.ball β₀ r, HasFDerivWithinAt f (f' b) (Metric.ball β₀ r) b := by
    intro b hb
    exact (((HasFDerivAt.fun_sum fun i _ ↦ hdiff i ω _ hθδ b (hsub hb)).fun_const_smul
      ((n : ℝ)⁻¹)).fun_sub (Abar (β₀, θ₀)).hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ b ∈ Metric.ball β₀ r, ‖f' b‖ ≤ ε := by
    intro b hb
    have hp := hpair b hb
    have hpδ : ((b, θhat n ω) : E × F) ∈ Metric.ball (β₀, θ₀) δ :=
      Metric.mem_ball.2 (hp.trans_le (min_le_right _ _))
    calc ‖f' b‖ = ‖((n : ℝ)⁻¹ • ∑ i ∈ range n, DU i b (θhat n ω) ω - Abar (b, θhat n ω)) +
          (Abar (b, θhat n ω) - Abar (β₀, θ₀))‖ := by simp only [f', sub_add_sub_cancel]
      _ ≤ ‖(n : ℝ)⁻¹ • ∑ i ∈ range n, DU i b (θhat n ω) ω - Abar (b, θhat n ω)‖ +
          ‖Abar (b, θhat n ω) - Abar (β₀, θ₀)‖ := norm_add_le _ _
      _ ≤ ε / 2 + ε / 2 := by
          gcongr
          · exact (h2 _ hpδ).le
          · have h3 := hAr (hp.trans_le (min_le_left _ _))
            rw [dist_eq_norm] at h3
            exact h3.le
      _ = ε := add_halves ε
  have hmv := (convex_ball β₀ r).norm_image_sub_le_of_norm_hasFDerivWithin_le hf hbound
    (Metric.mem_ball_self hr) (Metric.mem_ball.2 hβr)
  have heq : f (βhat n ω) - f β₀ = (n : ℝ)⁻¹ • (∑ i ∈ range n, U i (βhat n ω) (θhat n ω) ω -
      ∑ i ∈ range n, U i β₀ (θhat n ω) ω) - Abar (β₀, θ₀) (βhat n ω - β₀) := by
    simp only [f, smul_sub, map_sub]
    abel
  rw [heq] at hmv
  exact hω.not_ge hmv

/-- **GEE asymptotic normality with estimated weights from differentiable scores.** The
combination of `linearization_estimatedWeights_of_hasFDerivAt` and
`tendstoInDistribution_sqrt_smul_sub_sandwich_estimatedWeights`: with scores differentiable in
`β` and in the nuisance `θ`, an averaged `β`-Jacobian converging uniformly near `(β₀, θ₀)` to a
sensitivity `Abar` continuous at `(β₀, θ₀)` with `Abar (β₀, θ₀)` invertible, an asymptotically
negligible averaged nuisance derivative, a `√n`-consistent nuisance estimator `θhat`, a
consistent root `βhat` of the estimated-weight equation, and the cluster CLT hypotheses at
`(β₀, θ₀)`,
`√n • (βhat n - β₀) → N(0, sandwichCovariance (Abar (β₀, θ₀)) B)` in distribution. -/
theorem tendstoInDistribution_sqrt_smul_sub_sandwich_estimatedWeights_of_hasFDerivAt
    {U : ℕ → E → F → Ω → E} {DU : ℕ → E → F → Ω → E →L[ℝ] E}
    {DθU : ℕ → F → Ω → F →L[ℝ] E} {β₀ : E} {θ₀ : F} {δ : ℝ} (hδ : 0 < δ)
    (hdiff : ∀ i ω, ∀ θ ∈ Metric.ball θ₀ δ, ∀ β ∈ Metric.ball β₀ δ,
      HasFDerivAt (fun b ↦ U i b θ ω) (DU i β θ ω) β)
    {Abar : E × F → E →L[ℝ] E} (hAbar : ContinuousAt Abar (β₀, θ₀)) (hA : IsUnit (Abar (β₀, θ₀)))
    (hunif : ∀ ε > 0, Tendsto (fun n : ℕ ↦ P {ω | ∃ p ∈ Metric.ball (β₀, θ₀) δ,
      ε ≤ ‖(n : ℝ)⁻¹ • ∑ i ∈ range n, DU i p.1 p.2 ω - Abar p‖}) atTop (𝓝 0))
    (hdiffθ : ∀ i ω, ∀ θ ∈ Metric.ball θ₀ δ, HasFDerivAt (fun a ↦ U i β₀ a ω) (DθU i θ ω) θ)
    (hunifθ : ∀ ε > 0, Tendsto (fun n : ℕ ↦ P {ω | ∃ θ ∈ Metric.ball θ₀ δ,
      ε ≤ ‖(n : ℝ)⁻¹ • ∑ i ∈ range n, DθU i θ ω‖}) atTop (𝓝 0))
    {θhat : ℕ → Ω → F}
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℝ, ∀ n : ℕ,
      P {ω | K < ‖√(n : ℝ) • (θhat n ω - θ₀)‖} ≤ ε)
    (hSmeas : ∀ n, AEMeasurable (fun ω ↦ ∑ i ∈ range n, U i β₀ (θhat n ω) ω) P)
    {B : E →L[ℝ] E}
    (hmeas : ∀ k, Measurable (U k β₀ θ₀)) (hindep : iIndepFun (fun k ↦ U k β₀ θ₀) P)
    (hmean : ∀ k, ∫ ω, U k β₀ θ₀ ω ∂P = 0) (hL2 : ∀ k, MemLp (U k β₀ θ₀) 2 P)
    (hvar : ∀ t, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, ∫ ω, ⟪U k β₀ θ₀ ω, t⟫ ^ 2 ∂P)
      atTop (𝓝 ⟪B t, t⟫))
    (hL : ∀ t, LindebergConditionTriangular (fun n k ω ↦ (√n)⁻¹ * ⟪U k β₀ θ₀ ω, t⟫) P)
    {βhat : ℕ → Ω → E} (hβ : ∀ n, AEMeasurable (βhat n) P)
    (hβcons : TendstoInMeasure P βhat atTop (fun _ ↦ β₀))
    (hroot : Tendsto (fun n ↦ P {ω | ∑ i ∈ range n, U i (βhat n ω) (θhat n ω) ω ≠ 0}) atTop
      (𝓝 0))
    {W : Ω' → E} (hW : AEMeasurable W P')
    (hWlaw : ∀ t, HasLaw (fun ω ↦ ⟪W ω, t⟫)
      (gaussianReal 0 (⟪sandwichCovariance (Abar (β₀, θ₀)) B t, t⟫).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √n • (βhat n ω - β₀)) atTop W (fun _ ↦ P) P' :=
  tendstoInDistribution_sqrt_smul_sub_sandwich_estimatedWeights hδ hA hmeas hindep hmean hL2
    hvar hL hdiffθ hunifθ htight hSmeas hβ hroot
    (linearization_estimatedWeights_of_hasFDerivAt hδ hdiff hAbar hunif hβcons
      (tendstoInMeasure_of_sqrt_smul_sub_bounded htight)) hW hWlaw

omit [MeasurableSpace E] [BorelSpace E] [NormedSpace ℝ F] [IsProbabilityMeasure P] in
/-- **Consistency of the empirical sandwich with estimated weights.** Plug-in bread
`n⁻¹ • ∑_{i<n} DU i (βhat n) (θhat n)` and meat
`n⁻¹ • ∑_{i<n} U i (βhat n) (θhat n) U i (βhat n) (θhat n)ᵀ`, with averaged Jacobians and
averaged rank-one operators converging uniformly near `(β₀, θ₀)` in probability to `Abar` and
`Bbar`, both continuous at `(β₀, θ₀)`, `Abar (β₀, θ₀)` invertible, and `βhat`, `θhat` consistent.
Then the empirical sandwich converges in probability to
`sandwichCovariance (Abar (β₀, θ₀)) (Bbar (β₀, θ₀))`, the sandwich at the limiting nuisance
value; it is the covariance of
`tendstoInDistribution_sqrt_smul_sub_sandwich_estimatedWeights_of_hasFDerivAt` when
`Bbar (β₀, θ₀)` equals the CLT meat `B`. -/
theorem tendstoInMeasure_empirical_sandwichCovariance_estimatedWeights {U : ℕ → E → F → Ω → E}
    {DU : ℕ → E → F → Ω → E →L[ℝ] E} {β₀ : E} {θ₀ : F} {δ : ℝ} (hδ : 0 < δ)
    {Abar Bbar : E × F → E →L[ℝ] E} (hAbar : ContinuousAt Abar (β₀, θ₀))
    (hBbar : ContinuousAt Bbar (β₀, θ₀)) (hA : IsUnit (Abar (β₀, θ₀)))
    (hAunif : ∀ ε > 0, Tendsto (fun n : ℕ ↦ P {ω | ∃ p ∈ Metric.ball (β₀, θ₀) δ,
      ε ≤ ‖(n : ℝ)⁻¹ • ∑ i ∈ range n, DU i p.1 p.2 ω - Abar p‖}) atTop (𝓝 0))
    (hBunif : ∀ ε > 0, Tendsto (fun n : ℕ ↦ P {ω | ∃ p ∈ Metric.ball (β₀, θ₀) δ,
      ε ≤ ‖(n : ℝ)⁻¹ • ∑ i ∈ range n,
        InnerProductSpace.rankOne ℝ (U i p.1 p.2 ω) (U i p.1 p.2 ω) - Bbar p‖}) atTop (𝓝 0))
    {βhat : ℕ → Ω → E} {θhat : ℕ → Ω → F}
    (hβcons : TendstoInMeasure P βhat atTop (fun _ ↦ β₀))
    (hθcons : TendstoInMeasure P θhat atTop (fun _ ↦ θ₀)) :
    TendstoInMeasure P (fun (n : ℕ) ω ↦ sandwichCovariance
        ((n : ℝ)⁻¹ • ∑ i ∈ range n, DU i (βhat n ω) (θhat n ω) ω)
        ((n : ℝ)⁻¹ • ∑ i ∈ range n, InnerProductSpace.rankOne ℝ (U i (βhat n ω) (θhat n ω) ω)
          (U i (βhat n ω) (θhat n ω) ω))) atTop
      (fun _ ↦ sandwichCovariance (Abar (β₀, θ₀)) (Bbar (β₀, θ₀))) := by
  have hcons := tendstoInMeasure_prodMk hβcons hθcons
  have hA' : TendstoInMeasure P (fun (n : ℕ) ω ↦
      (n : ℝ)⁻¹ • ∑ i ∈ range n, DU i (βhat n ω) (θhat n ω) ω) atTop
      (fun _ ↦ Abar (β₀, θ₀)) :=
    tendstoInMeasure_comp_of_tendstoUniformlyOn (E := E × F) (F := E →L[ℝ] E)
      (βhat := fun n ω ↦ (βhat n ω, θhat n ω))
      (Φ := fun n p ω ↦ (n : ℝ)⁻¹ • ∑ i ∈ range n, DU i p.1 p.2 ω) hδ hAbar
      (fun ε hε ↦ by simpa only [dist_eq_norm] using hAunif ε hε) hcons
  have hB' : TendstoInMeasure P (fun (n : ℕ) ω ↦
      (n : ℝ)⁻¹ • ∑ i ∈ range n, InnerProductSpace.rankOne ℝ (U i (βhat n ω) (θhat n ω) ω)
        (U i (βhat n ω) (θhat n ω) ω)) atTop (fun _ ↦ Bbar (β₀, θ₀)) :=
    tendstoInMeasure_comp_of_tendstoUniformlyOn (E := E × F) (F := E →L[ℝ] E)
      (βhat := fun n ω ↦ (βhat n ω, θhat n ω)) (Φ := fun n p ω ↦
        (n : ℝ)⁻¹ • ∑ i ∈ range n, InnerProductSpace.rankOne ℝ (U i p.1 p.2 ω) (U i p.1 p.2 ω))
      hδ hBbar (fun ε hε ↦ by simpa only [dist_eq_norm] using hBunif ε hε) hcons
  exact tendstoInMeasure_sandwichCovariance hA hA' hB'

end ProbabilityTheory.GEE
