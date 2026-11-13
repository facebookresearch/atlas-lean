/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GLM.NegativeBinomialDispersion
public import MathlibExt.Probability.Statistics.EstimatedInformation
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Restricted and profile likelihood for the negative binomial shape; composite tests for `β`

`NegativeBinomialDispersion` estimates the shape `θ` (the `k` of the NB2 variance `μ + μ² / k`)
jointly with the coefficients `β` of the log-link negative binomial regression. This file
supplies the restricted-likelihood theory needed to test a composite null `H₀ : β = β₀` with the
shape left free (a nuisance parameter), and the profile likelihood for the shape.

## Restricted and profile likelihood (deterministic)

* `nbRestrictedLogLik X o y β₀ θ = nbJointLogLik X o y (β₀, θ)`: the likelihood under
  `H₀ : β = β₀`. `hasDerivAt_nbRestrictedLogLik`: its derivative is the shape score
  `nbJointShapeScore`; `nbJointShapeScore_eq_zero_of_isMaxOn`: a restricted maximizer `θ̃ > 0`
  solves the restricted likelihood equation.
* `nbLogPmf_nonpos`, `nbJointLogLik_nonpos`: for `θ > 0` the log-likelihood is a sum of logs of
  probabilities, hence `≤ 0`. So every `β`-section is bounded above and the **profile
  log-likelihood** `nbProfileLogLik X o y θ = ⨆ β, nbJointLogLik X o y (β, θ)` is a genuine
  supremum.
* `nbProfileLogLik_eq_of_isMaxOn`: at a section maximizer the profile is attained.
  `nbSection_maximizer_unique`: under an injective design a section maximizer is unique (it is a
  maximizer of the fixed-shape likelihood, `nbLogLik_maximizer_unique`).
  `nbGradient_eq_zero_of_isMaxOn_section`: it solves the fixed-shape score equation.
* `isMaxOn_nbProfileLogLik_of_isMaxOn` and `isMaxOn_nbJointLogLik_of_isMaxOn_profile`: `(β̂, θ̂)`
  maximizes the joint likelihood over `θ > 0` iff `θ̂` maximizes the profile and `β̂` maximizes
  the `θ̂`-section.
* `hasDerivAt_nbProfileLogLik` (envelope theorem): along a differentiable path of section
  maximizers, the profile score is the shape score at the section maximizer.

## Composite likelihood-ratio statistic (deterministic)

* `nbCompositeLRStat X o y p̂ β₀ θ̃ = 2 (ℓ(p̂) - ℓ(β₀, θ̃))`. `nbCompositeLRStat_nonneg`: it is
  `≥ 0` when `p̂` is a joint maximizer. `nbCompositeLRStat_eq_profile`: it equals
  `2 (ℓ_prof(θ̂) - ℓ(β₀, θ̃))`. `nbCompositeLRStat_eq_sub`: it is the full simple-null statistic
  minus the restricted simple-null statistic.
* `sumElim_dotProduct_fromBlocks_mulVec`, `nbJointFisherInfo_inv_quadForm`: with a block-diagonal
  information `[[A, 0], [0, D]]` the full score quadratic form splits as
  `Tᵀ A⁻¹ T + U² / D` (coefficient score `T`, shape score `U`). For `nbJointFisherInfo` the
  block-diagonal inverse is the merged `inv_nbJointFisherInfo`.

## Asymptotics

* `tendstoInMeasure_nbRestrictedMLE`: consistency of the restricted MLE of the shape under `H₀`,
  from the merged `tendstoInMeasure_nbJointMLE` on the slice `{β₀} ×ˢ K`.
* `tendstoInMeasure_nbCoefScore_restricted_sub`: plugging in the restricted shape estimate `θ̃`
  does not change the scaled coefficient score to first order. The proof is a mean-value bound
  in `θ`: the derivative of the score in `θ` is the cross term `nbCross`
  (`hasFDerivAt_nbScore_prod`), whose sample average tends to zero by orthogonality, while
  `√n (θ̃ - θ₀)` is bounded in probability.
* `tendstoInDistribution_quadForm_of_sub`: an abstract Rao statistic `⟪Â⁻¹ T̃ₙ, T̃ₙ⟫ → χ²_d`
  when `Tₙ →ᵈ N(0, A)`, `T̃ₙ - Tₙ → 0` and `Âₙ → A` in probability.
* `tendstoInDistribution_nbCompositeScoreStatistic`: **composite score test** for `H₀ : β = β₀`
  with the shape estimated under `H₀`: `⟪Â⁻¹ T̃ₙ, T̃ₙ⟫ → χ²_{|κ|}`.
* `tendstoInDistribution_nbCompositeLRStat`: **composite likelihood-ratio test** for
  `H₀ : β = β₀` with the shape free: `2 (ℓ(β̂, θ̂) - ℓ(β₀, θ̃)) → χ²_{|κ|}`.

## Hypotheses taken from T131 (joint asymptotics), and what is not proved

The joint `(β, θ)` asymptotics of `NegativeBinomialAN` (T131, an open PR) are not imported. The
facts this file needs from that setup enter as explicit hypotheses:

* the central limit theorem for the scaled coefficient score at the truth,
  `Tₙ = n^{-1/2} ∑_{i<n} nbScore θ₀ yᵢ ηᵢ xᵢ →ᵈ N(0, A)` (`hT`);
* the Wilks expansions `2 (ℓ(p̂) - ℓ(p₀)) = sₙᵀ I⁻¹ sₙ + o_P(1)` for the joint MLE (`hfull`)
  and `2 (ℓ(β₀, θ̃) - ℓ(p₀)) = Uₙ² / D + o_P(1)` for the restricted MLE (`hres`), with
  `sₙ = (Tₙ, Uₙ)` the scaled joint score;
* the block-diagonal limit information `I = [[A, 0], [0, D]]` (written into the form of
  `hfull`, with `hA : A.PosDef` and `hD : D ≠ 0`; the cross information vanishes by
  `hasSum_nbCross_mul_negBinomialReal`);
* `√n (θ̃ - θ₀)` bounded in probability (`htight`; it follows from asymptotic normality of the
  one-parameter restricted MLE, which is not proved here), and the uniform law of large numbers
  for the cross average on a neighborhood of `θ₀` (`hcross`; its limit is zero because
  `E[y - μ] = 0` under `H₀`, for every `θ`).

The composite limits also take a.e.-measurability of the statistic as a hypothesis
(`hTtil_meas`, `hLR_meas`); it is not derived from measurability of the estimators.

Not proved: existence of the restricted or profile maximizer, asymptotic normality of `θ̃`,
smoothness of the section maximizer `θ ↦ β̂(θ)` (the envelope theorem assumes it), and the
boundary `θ = ∞` (Poisson). The uniform LLN and CLT hypotheses are not derived from a sampling
model.

## References

* J. F. Lawless, "Negative binomial and mixed Poisson regression", Canad. J. Statist. 15 (1987)
  209–225, §2–3 (joint and profile maximum likelihood for `(β, k)`; `β̂` and `k̂` are
  asymptotically independent).
* A. C. Cameron and P. K. Trivedi, *Regression Analysis of Count Data*, 2nd ed. (2013), §3.3
  and §5.6 (NB2 maximum likelihood; score and likelihood-ratio tests with nuisance parameters).
* A. W. van der Vaart, *Asymptotic Statistics* (1998), §16.1 (likelihood-ratio tests for
  composite nulls) and §25.4 (profile likelihood).

## Source receipt (API-00)

Reused from `NegativeBinomialDispersion`: `nbLogPmf`, `nbJointLogLik`, `nbJointShapeScore`,
`hasFDerivAt_nbJointLogLik` (joint score), `hasFDerivAt_nbScore_prod` (`∂_θ nbScore = nbCross`),
`inv_nbJointFisherInfo` (block-diagonal inverse), `nbAvgLogLik`, `tendstoInMeasure_nbJointMLE`.
Reused from `NegativeBinomial`: `nbLogLik`, `nbGradient`, `nbLogLik_maximizer_unique`. Reused
from `VectorInference`/`EstimatedInformation`: `hasLaw_inner_inverse_chiSquare`,
`TendstoInDistribution.of_map_eq`, `measurable_ring_inverse`. Reused from Mathlib:
`tendstoInDistribution_of_tendstoInMeasure_sub`,
`TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const`. Proved here: the
restricted/profile statements, the envelope identity, the composite-statistic algebra, the
mean-value plug-in bound and the composite limits.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.GLM.NegativeBinomial

open Finset Real Matrix ProbabilityTheory MeasureTheory Filter Topology
open scoped Nat RealInnerProductSpace ENNReal
open MathlibExt.Probability.Statistics.VectorInference
  (isUnit_of_inner_self_pos hasLaw_inner_inverse_chiSquare)

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ### The restricted likelihood in the shape -/

/-- The negative binomial log-likelihood restricted to the null `H₀ : β = β₀`, as a function of
the shape `θ` alone: `θ ↦ nbJointLogLik X o y (β₀, θ)`. -/
noncomputable def nbRestrictedLogLik (X : Matrix ι κ ℝ) (o : ι → ℝ) (y : ι → ℕ) (β₀ : κ → ℝ)
    (θ : ℝ) : ℝ :=
  nbJointLogLik X o y (β₀, θ)

/-- **The restricted score is the shape score.** For `θ > 0` the restricted log-likelihood is
differentiable with derivative `nbJointShapeScore X o y (β₀, θ)`. -/
theorem hasDerivAt_nbRestrictedLogLik (X : Matrix ι κ ℝ) (o : ι → ℝ) (y : ι → ℕ) (β₀ : κ → ℝ)
    {θ : ℝ} (hθ : 0 < θ) :
    HasDerivAt (nbRestrictedLogLik X o y β₀) (nbJointShapeScore X o y (β₀, θ)) θ := by
  have hpath : HasDerivAt (fun t : ℝ => (β₀, t)) ((0 : κ → ℝ), (1 : ℝ)) θ :=
    (hasDerivAt_const θ β₀).prodMk (hasDerivAt_id θ)
  have h := (hasFDerivAt_nbJointLogLik X o y (p := (β₀, θ)) hθ).comp_hasDerivAt θ hpath
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', _root_.smul_apply,
    Real.dotL_apply, zero_dotProduct, smul_eq_mul, mul_one, zero_add] at h
  exact h

/-- **The restricted likelihood equation.** A local maximizer `θ̃ > 0` of the restricted
log-likelihood solves `nbJointShapeScore X o y (β₀, θ̃) = 0`. -/
theorem nbJointShapeScore_eq_zero_of_isLocalMax (X : Matrix ι κ ℝ) (o : ι → ℝ) (y : ι → ℕ)
    (β₀ : κ → ℝ) {θ : ℝ} (hθ : 0 < θ) (h : IsLocalMax (nbRestrictedLogLik X o y β₀) θ) :
    nbJointShapeScore X o y (β₀, θ) = 0 :=
  h.hasDerivAt_eq_zero (hasDerivAt_nbRestrictedLogLik X o y β₀ hθ)

/-- A maximizer `θ̃ > 0` of the restricted log-likelihood over `θ > 0` solves the restricted
likelihood equation. -/
theorem nbJointShapeScore_eq_zero_of_isMaxOn (X : Matrix ι κ ℝ) (o : ι → ℝ) (y : ι → ℕ)
    (β₀ : κ → ℝ) {θ : ℝ} (hθ : 0 < θ)
    (h : IsMaxOn (nbRestrictedLogLik X o y β₀) (Set.Ioi 0) θ) :
    nbJointShapeScore X o y (β₀, θ) = 0 :=
  nbJointShapeScore_eq_zero_of_isLocalMax X o y β₀ hθ (h.isLocalMax (Ioi_mem_nhds hθ))

/-! ### Boundedness and the profile likelihood -/

/-- **The log mass function is nonpositive**: for `θ > 0`, `nbLogPmf θ y η = log NB(y; θ, e^η)`
and the mass is at most one. -/
theorem nbLogPmf_nonpos {θ : ℝ} (hθ : 0 < θ) (y : ℕ) (η : ℝ) : nbLogPmf θ y η ≤ 0 := by
  rw [← log_negBinomialReal_exp_eq_nbLogPmf hθ η y]
  have hμ : 0 ≤ exp η := (exp_pos η).le
  exact Real.log_nonpos (negBinomialReal_nonneg hθ hμ y)
    (le_hasSum (hasSum_negBinomialReal hθ hμ) y fun j _ => negBinomialReal_nonneg hθ hμ j)

/-- For a positive shape the joint log-likelihood is nonpositive. -/
theorem nbJointLogLik_nonpos (X : Matrix ι κ ℝ) (o : ι → ℝ) (y : ι → ℕ) {p : (κ → ℝ) × ℝ}
    (hθ : 0 < p.2) : nbJointLogLik X o y p ≤ 0 :=
  Finset.sum_nonpos fun i _ => nbLogPmf_nonpos hθ (y i) _

/-- The `θ`-section of the joint log-likelihood is the fixed-shape log-likelihood `nbLogLik` plus
a term that does not depend on `β`. -/
theorem nbJointLogLik_eq_nbLogLik_add (X : Matrix ι κ ℝ) (o : ι → ℝ) (y : ι → ℕ) (β : κ → ℝ)
    (θ : ℝ) :
    nbJointLogLik X o y (β, θ) = nbLogLik θ X o (fun i => (y i : ℝ)) β +
      ∑ i, (∑ j ∈ range (y i), log (θ + j) - log ((y i) ! : ℝ) + θ * log θ) := by
  simp only [nbJointLogLik, nbLogLik, nbLogPmf, ← sum_add_distrib]
  exact sum_congr rfl fun i _ => by ring

/-- The profile log-likelihood of the shape: `θ ↦ ⨆ β, nbJointLogLik X o y (β, θ)`. For `θ > 0`
the supremum is finite (`bddAbove_range_nbJointLogLik`). -/
noncomputable def nbProfileLogLik (X : Matrix ι κ ℝ) (o : ι → ℝ) (y : ι → ℕ) (θ : ℝ) : ℝ :=
  ⨆ β : κ → ℝ, nbJointLogLik X o y (β, θ)

/-- For `θ > 0` every `θ`-section of the joint log-likelihood is bounded above (by `0`). -/
theorem bddAbove_range_nbJointLogLik (X : Matrix ι κ ℝ) (o : ι → ℝ) (y : ι → ℕ) {θ : ℝ}
    (hθ : 0 < θ) : BddAbove (Set.range fun β : κ → ℝ => nbJointLogLik X o y (β, θ)) :=
  ⟨0, by rintro _ ⟨β, rfl⟩; exact nbJointLogLik_nonpos X o y (p := (β, θ)) hθ⟩

/-- For `θ > 0` the joint log-likelihood is below the profile. -/
theorem nbJointLogLik_le_nbProfileLogLik (X : Matrix ι κ ℝ) (o : ι → ℝ) (y : ι → ℕ) {θ : ℝ}
    (hθ : 0 < θ) (β : κ → ℝ) : nbJointLogLik X o y (β, θ) ≤ nbProfileLogLik X o y θ :=
  le_ciSup (bddAbove_range_nbJointLogLik X o y hθ) β

/-- The profile is nonpositive for `θ > 0`. -/
theorem nbProfileLogLik_nonpos (X : Matrix ι κ ℝ) (o : ι → ℝ) (y : ι → ℕ) {θ : ℝ}
    (hθ : 0 < θ) : nbProfileLogLik X o y θ ≤ 0 :=
  ciSup_le fun β => nbJointLogLik_nonpos X o y (p := (β, θ)) hθ

/-- **The profile is attained at a section maximizer.** -/
theorem nbProfileLogLik_eq_of_isMaxOn (X : Matrix ι κ ℝ) (o : ι → ℝ) (y : ι → ℕ) {β : κ → ℝ}
    {θ : ℝ} (h : IsMaxOn (fun b => nbJointLogLik X o y (b, θ)) Set.univ β) :
    nbProfileLogLik X o y θ = nbJointLogLik X o y (β, θ) := by
  refine le_antisymm (ciSup_le fun b => h (Set.mem_univ b))
    (le_ciSup (f := fun b => nbJointLogLik X o y (b, θ)) ?_ β)
  exact ⟨_, by rintro _ ⟨b, rfl⟩; exact h (Set.mem_univ b)⟩

/-- **At most one section maximizer.** For `θ > 0` and an injective design, the `θ`-section of
the joint log-likelihood has at most one maximizer: it differs from the fixed-shape
log-likelihood by a `β`-free term (`nbJointLogLik_eq_nbLogLik_add`), and
`nbLogLik_maximizer_unique` applies. -/
theorem nbSection_maximizer_unique {θ : ℝ} (hθ : 0 < θ) {X : Matrix ι κ ℝ}
    (hinj : Function.Injective X.mulVec) (o : ι → ℝ) (y : ι → ℕ) {β₁ β₂ : κ → ℝ}
    (h₁ : IsMaxOn (fun b => nbJointLogLik X o y (b, θ)) Set.univ β₁)
    (h₂ : IsMaxOn (fun b => nbJointLogLik X o y (b, θ)) Set.univ β₂) : β₁ = β₂ := by
  have key : ∀ {β : κ → ℝ}, IsMaxOn (fun b => nbJointLogLik X o y (b, θ)) Set.univ β →
      IsMaxOn (nbLogLik θ X o (fun i => (y i : ℝ))) Set.univ β := fun {β} h b hb => by
    have := h hb
    simp only [Set.mem_ofPred_eq, nbJointLogLik_eq_nbLogLik_add] at this ⊢
    linarith
  exact nbLogLik_maximizer_unique hθ hinj o (fun i => Nat.cast_nonneg _) (key h₁) (key h₂)

/-- The `β`-derivative of the `θ`-section is the fixed-shape score vector. -/
theorem hasFDerivAt_nbJointLogLik_section (X : Matrix ι κ ℝ) (o : ι → ℝ) (y : ι → ℕ)
    (β : κ → ℝ) {θ : ℝ} (hθ : 0 < θ) :
    HasFDerivAt (fun b => nbJointLogLik X o y (b, θ))
      (Real.dotL (nbGradient θ X o (fun i => (y i : ℝ)) β)) β := by
  have hin : HasFDerivAt (fun b : κ → ℝ => (b, θ))
      ((ContinuousLinearMap.id ℝ (κ → ℝ)).prod 0) β :=
    (hasFDerivAt_id (𝕜 := ℝ) β).prodMk (hasFDerivAt_const θ β)
  have h := (hasFDerivAt_nbJointLogLik X o y (p := (β, θ)) hθ).comp β hin
  have h2 := h.congr_fderiv (g' := Real.dotL (nbGradient θ X o (fun i => (y i : ℝ)) β))
    (ContinuousLinearMap.ext fun v => by simp)
  exact h2

/-- **A section maximizer solves the fixed-shape score equation**: for `θ > 0`,
`nbGradient θ X o y β̂ = 0`. -/
theorem nbGradient_eq_zero_of_isMaxOn_section (X : Matrix ι κ ℝ) (o : ι → ℝ) (y : ι → ℕ)
    {β : κ → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (h : IsMaxOn (fun b => nbJointLogLik X o y (b, θ)) Set.univ β) :
    nbGradient θ X o (fun i => (y i : ℝ)) β = 0 := by
  have h0 := (h.isLocalMax Filter.univ_mem).hasFDerivAt_eq_zero
    (hasFDerivAt_nbJointLogLik_section X o y β hθ)
  funext j
  classical
  have := congrArg (fun L : (κ → ℝ) →L[ℝ] ℝ => L (Pi.single j 1)) h0
  simpa [Real.dotL_apply, dotProduct_single] using this

/-- **Joint maximizer gives a profile maximizer.** If `p̂ = (β̂, θ̂)` with `θ̂ > 0` maximizes the
joint log-likelihood over `θ > 0`, then `θ̂` maximizes the profile over `θ > 0`, `β̂` maximizes the
`θ̂`-section, and the profile at `θ̂` is the joint maximum. -/
theorem isMaxOn_nbProfileLogLik_of_isMaxOn (X : Matrix ι κ ℝ) (o : ι → ℝ) (y : ι → ℕ)
    {phat : (κ → ℝ) × ℝ} (hθ : 0 < phat.2)
    (h : IsMaxOn (nbJointLogLik X o y) (Set.univ ×ˢ Set.Ioi 0) phat) :
    IsMaxOn (nbProfileLogLik X o y) (Set.Ioi 0) phat.2 ∧
      IsMaxOn (fun b => nbJointLogLik X o y (b, phat.2)) Set.univ phat.1 ∧
      nbProfileLogLik X o y phat.2 = nbJointLogLik X o y phat := by
  have hsec : IsMaxOn (fun b => nbJointLogLik X o y (b, phat.2)) Set.univ phat.1 :=
    fun b _ => h ⟨Set.mem_univ b, hθ⟩
  have heq : nbProfileLogLik X o y phat.2 = nbJointLogLik X o y phat :=
    nbProfileLogLik_eq_of_isMaxOn X o y hsec
  refine ⟨fun θ hθ' => ?_, hsec, heq⟩
  simp only [Set.mem_ofPred_eq, heq]
  exact ciSup_le fun b => h ⟨Set.mem_univ b, hθ'⟩

/-- **Profile maximizer gives a joint maximizer.** If `θ̂ > 0` maximizes the profile over
`θ > 0` and `β̂` maximizes the `θ̂`-section, then `(β̂, θ̂)` maximizes the joint log-likelihood
over `θ > 0`. -/
theorem isMaxOn_nbJointLogLik_of_isMaxOn_profile (X : Matrix ι κ ℝ) (o : ι → ℝ) (y : ι → ℕ)
    {βhat : κ → ℝ} {θhat : ℝ}
    (hprof : IsMaxOn (nbProfileLogLik X o y) (Set.Ioi 0) θhat)
    (hsec : IsMaxOn (fun b => nbJointLogLik X o y (b, θhat)) Set.univ βhat) :
    IsMaxOn (nbJointLogLik X o y) (Set.univ ×ˢ Set.Ioi 0) (βhat, θhat) := by
  rintro ⟨b, θ⟩ ⟨-, hθ⟩
  have h1 := nbJointLogLik_le_nbProfileLogLik X o y (hθ : 0 < θ) b
  have h2 : nbProfileLogLik X o y θ ≤ nbProfileLogLik X o y θhat := hprof hθ
  rw [nbProfileLogLik_eq_of_isMaxOn X o y hsec] at h2
  exact h1.trans h2

/-- **Envelope theorem for the profile.** Let `θ ↦ β̂(θ)` be a path of section maximizers on a
neighborhood of `θ₀ > 0`, differentiable at `θ₀`. Then the profile log-likelihood is
differentiable at `θ₀` and its derivative (the profile score) is the shape score at
`(β̂(θ₀), θ₀)`: the coefficient part of the joint score vanishes at a section maximizer
(`nbGradient_eq_zero_of_isMaxOn_section`). -/
theorem hasDerivAt_nbProfileLogLik (X : Matrix ι κ ℝ) (o : ι → ℝ) (y : ι → ℕ)
    {βhat : ℝ → κ → ℝ} {βhat' : κ → ℝ} {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    (hsec : ∀ᶠ θ in 𝓝 θ₀, IsMaxOn (fun b => nbJointLogLik X o y (b, θ)) Set.univ (βhat θ))
    (hβ : HasDerivAt βhat βhat' θ₀) :
    HasDerivAt (nbProfileLogLik X o y) (nbJointShapeScore X o y (βhat θ₀, θ₀)) θ₀ := by
  have hg := nbGradient_eq_zero_of_isMaxOn_section X o y hθ₀ hsec.self_of_nhds
  have hpath : HasDerivAt (fun t : ℝ => (βhat t, t)) (βhat', (1 : ℝ)) θ₀ :=
    hβ.prodMk (hasDerivAt_id θ₀)
  have h := (hasFDerivAt_nbJointLogLik X o y (p := (βhat θ₀, θ₀)) hθ₀).comp_hasDerivAt_of_eq θ₀
    hpath rfl
  have h' : HasDerivAt (fun θ => nbJointLogLik X o y (βhat θ, θ))
      (nbJointShapeScore X o y (βhat θ₀, θ₀)) θ₀ :=
    h.congr_deriv (by simp [hg])
  exact h'.congr_of_eventuallyEq
    (hsec.mono fun θ hθ => nbProfileLogLik_eq_of_isMaxOn X o y hθ)

/-! ### The composite likelihood-ratio statistic -/

/-- The likelihood-ratio statistic for the composite null `H₀ : β = β₀` with the shape free:
`2 (ℓ(p̂) - ℓ(β₀, θ̃))`, with `p̂` the joint and `θ̃` the restricted estimate. -/
noncomputable def nbCompositeLRStat (X : Matrix ι κ ℝ) (o : ι → ℝ) (y : ι → ℕ)
    (phat : (κ → ℝ) × ℝ) (β₀ : κ → ℝ) (θtil : ℝ) : ℝ :=
  2 * (nbJointLogLik X o y phat - nbRestrictedLogLik X o y β₀ θtil)

/-- The composite likelihood-ratio statistic is nonnegative when `p̂` maximizes the joint
log-likelihood over `θ > 0` and `θ̃ > 0`. -/
theorem nbCompositeLRStat_nonneg (X : Matrix ι κ ℝ) (o : ι → ℝ) (y : ι → ℕ)
    {phat : (κ → ℝ) × ℝ} (h : IsMaxOn (nbJointLogLik X o y) (Set.univ ×ˢ Set.Ioi 0) phat)
    (β₀ : κ → ℝ) {θtil : ℝ} (hθ : 0 < θtil) : 0 ≤ nbCompositeLRStat X o y phat β₀ θtil := by
  have := h (show (β₀, θtil) ∈ Set.univ ×ˢ Set.Ioi (0 : ℝ) from ⟨Set.mem_univ _, hθ⟩)
  simp only [Set.mem_ofPred_eq] at this
  simp only [nbCompositeLRStat, nbRestrictedLogLik]
  linarith

/-- **The composite statistic through the profile.** At a joint maximizer `p̂ = (β̂, θ̂)` the
composite statistic is `2 (ℓ_prof(θ̂) - ℓ(β₀, θ̃))`. -/
theorem nbCompositeLRStat_eq_profile (X : Matrix ι κ ℝ) (o : ι → ℝ) (y : ι → ℕ)
    {phat : (κ → ℝ) × ℝ} (hθ : 0 < phat.2)
    (h : IsMaxOn (nbJointLogLik X o y) (Set.univ ×ˢ Set.Ioi 0) phat) (β₀ : κ → ℝ) (θtil : ℝ) :
    nbCompositeLRStat X o y phat β₀ θtil =
      2 * (nbProfileLogLik X o y phat.2 - nbRestrictedLogLik X o y β₀ θtil) := by
  rw [nbCompositeLRStat, (isMaxOn_nbProfileLogLik_of_isMaxOn X o y hθ h).2.2]

/-- **Composite statistic as a difference of simple-null statistics.** For any `θ₀`,
`2 (ℓ(p̂) - ℓ(β₀, θ̃)) = 2 (ℓ(p̂) - ℓ(β₀, θ₀)) - 2 (ℓ(β₀, θ̃) - ℓ(β₀, θ₀))`. -/
theorem nbCompositeLRStat_eq_sub (X : Matrix ι κ ℝ) (o : ι → ℝ) (y : ι → ℕ)
    (phat : (κ → ℝ) × ℝ) (β₀ : κ → ℝ) (θtil θ₀ : ℝ) :
    nbCompositeLRStat X o y phat β₀ θtil =
      2 * (nbJointLogLik X o y phat - nbJointLogLik X o y (β₀, θ₀)) -
        2 * (nbRestrictedLogLik X o y β₀ θtil - nbJointLogLik X o y (β₀, θ₀)) := by
  simp only [nbCompositeLRStat]
  ring

/-- **Block-diagonal quadratic forms split.** For the block-diagonal matrix
`[[A, 0], [0, d]]` over `κ ⊕ Unit` and the vector `s = (T, U)`,
`sᵀ [[A, 0], [0, d]] s = Tᵀ A T + d U²`. -/
theorem sumElim_dotProduct_fromBlocks_mulVec (A : Matrix κ κ ℝ) (d : ℝ) (T : κ → ℝ) (U : ℝ) :
    Sum.elim T (fun _ : Unit => U) ⬝ᵥ
        (fromBlocks A 0 0 (of fun _ _ => d) *ᵥ Sum.elim T (fun _ : Unit => U)) =
      T ⬝ᵥ (A *ᵥ T) + d * U ^ 2 := by
  rw [fromBlocks_mulVec, sumElim_dotProduct_sumElim]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, zero_mulVec, add_zero, zero_add]
  congr 1
  simp only [dotProduct, mulVec, of_apply, Finset.univ_unique, Finset.sum_singleton]
  ring

/-- **The joint score quadratic form splits.** If the fixed-shape Fisher information
`A = Xᵀ diag(F) X` is invertible and the total shape information `D` is nonzero, then for
`s = (T, U)`, `sᵀ I⁻¹ s = Tᵀ A⁻¹ T + U² / D` with `I = nbJointFisherInfo θ X o β`
(`inv_nbJointFisherInfo`). -/
theorem nbJointFisherInfo_inv_quadForm [DecidableEq ι] [DecidableEq κ] (θ : ℝ)
    (X : Matrix ι κ ℝ) (o : ι → ℝ) (β : κ → ℝ)
    (hA : IsUnit (Xᵀ * diagonal (fun i => nbFisherWeight θ ((X *ᵥ β) i + o i)) * X))
    (hD : ∑ i, nbShapeFisherInfo θ ((X *ᵥ β) i + o i) ≠ 0) (T : κ → ℝ) (U : ℝ) :
    Sum.elim T (fun _ : Unit => U) ⬝ᵥ
        ((nbJointFisherInfo θ X o β)⁻¹ *ᵥ Sum.elim T (fun _ : Unit => U)) =
      T ⬝ᵥ ((Xᵀ * diagonal (fun i => nbFisherWeight θ ((X *ᵥ β) i + o i)) * X)⁻¹ *ᵥ T) +
        U ^ 2 / ∑ i, nbShapeFisherInfo θ ((X *ᵥ β) i + o i) := by
  rw [inv_nbJointFisherInfo θ X o β hA hD, sumElim_dotProduct_fromBlocks_mulVec]
  ring


/-- The inverse of the block-diagonal matrix `[[A, 0], [0, d]]` is `[[A⁻¹, 0], [0, d⁻¹]]`. -/
theorem inv_fromBlocks_zero_zero [DecidableEq κ] {A : Matrix κ κ ℝ} (hA : IsUnit A) {d : ℝ}
    (hd : d ≠ 0) :
    (fromBlocks A 0 0 (of fun _ _ : Unit => d))⁻¹ = fromBlocks A⁻¹ 0 0 (of fun _ _ => d⁻¹) := by
  refine inv_eq_right_inv ?_
  rw [fromBlocks_multiply, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hA)]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, ← fromBlocks_one]
  congr 1
  ext
  simp [mul_apply, hd]

/-- **The score quadratic form under a block-diagonal information.** For
`I = [[A, 0], [0, d]]` with `A` invertible and `d ≠ 0`, and `s = (T, U)`,
`sᵀ I⁻¹ s = Tᵀ A⁻¹ T + U² / d`. -/
theorem sumElim_dotProduct_inv_fromBlocks_mulVec [DecidableEq κ] {A : Matrix κ κ ℝ}
    (hA : IsUnit A) {d : ℝ} (hd : d ≠ 0) (T : κ → ℝ) (U : ℝ) :
    Sum.elim T (fun _ : Unit => U) ⬝ᵥ
        ((fromBlocks A 0 0 (of fun _ _ : Unit => d))⁻¹ *ᵥ Sum.elim T (fun _ : Unit => U)) =
      T ⬝ᵥ (A⁻¹ *ᵥ T) + U ^ 2 / d := by
  rw [inv_fromBlocks_zero_zero hA hd, sumElim_dotProduct_fromBlocks_mulVec]
  ring

/-! ### Consistency of the restricted MLE of the shape -/

section Asymptotics

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Consistency of the restricted MLE of the shape under `H₀ : β = β₀`, under explicit
hypotheses.** Let `K` be a compact set of positive shapes and `M` a population criterion,
continuous on `K`, uniquely maximized at `θ₀ ∈ K`. If the averaged restricted log-likelihood
`θ ↦ nbAvgLogLik x o y n ω (β₀, θ)` converges to `M` uniformly on `K` in probability and `θ̃ n`
lies in `K` and is a near-maximizer with probability tending to one, then `θ̃ n → θ₀` in
probability. This is `tendstoInMeasure_nbJointMLE` on the slice `{β₀} ×ˢ K`. -/
theorem tendstoInMeasure_nbRestrictedMLE (x : ℕ → Ω → κ → ℝ) (o : ℕ → Ω → ℝ)
    (y : ℕ → Ω → ℕ) (β₀ : κ → ℝ) {M : ℝ → ℝ} {K : Set ℝ} (hK : IsCompact K)
    (hM : ContinuousOn M K) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ K) (hKpos : ∀ θ ∈ K, 0 < θ)
    (hident : ∀ θ ∈ K, θ ≠ θ₀ → M θ < M θ₀)
    (hunif : ∀ ε > 0, Tendsto (fun n : ℕ =>
      P {ω | ∃ θ ∈ K, ε ≤ |nbAvgLogLik x o y n ω (β₀, θ) - M θ|}) atTop (𝓝 0))
    {θtil : ℕ → Ω → ℝ} (hθK : Tendsto (fun n => P {ω | θtil n ω ∉ K}) atTop (𝓝 0))
    (hmax : ∀ δ > 0, Tendsto (fun n => P {ω |
      nbAvgLogLik x o y n ω (β₀, θtil n ω) < nbAvgLogLik x o y n ω (β₀, θ₀) - δ}) atTop (𝓝 0)) :
    TendstoInMeasure P θtil atTop (fun _ => θ₀) := by
  set K' : Set ((κ → ℝ) × ℝ) := ({β₀} : Set (κ → ℝ)) ×ˢ K with hK'def
  have hK'c : IsCompact K' := isCompact_singleton.prod hK
  have hMc : ContinuousOn (fun p : (κ → ℝ) × ℝ => M p.2) K' :=
    hM.comp continuousOn_snd fun p hp => hp.2
  have hp₀ : ((β₀, θ₀) : (κ → ℝ) × ℝ) ∈ K' := ⟨Set.mem_singleton β₀, hθ₀⟩
  have hpos : ∀ p ∈ K', 0 < p.2 := fun p hp => hKpos p.2 hp.2
  have hid : ∀ p ∈ K', p ≠ (β₀, θ₀) → M p.2 < M (β₀, θ₀).2 := fun p hp hne =>
    hident p.2 hp.2 fun h2 => hne (Prod.ext (Set.mem_singleton_iff.1 hp.1) h2)
  have hunif' : ∀ ε > 0, Tendsto (fun n : ℕ => P {ω | ∃ p ∈ K',
      ε ≤ |nbAvgLogLik x o y n ω p - M p.2|}) atTop (𝓝 0) := fun ε hε => by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hunif ε hε)
      (fun _ => zero_le) fun n => measure_mono ?_
    rintro ω ⟨⟨b, θ⟩, ⟨hb, hθ⟩, hle⟩
    rw [Set.mem_singleton_iff] at hb
    subst hb
    exact ⟨θ, hθ, hle⟩
  have hset : ∀ n, {ω | ((β₀, θtil n ω) : (κ → ℝ) × ℝ) ∉ K'} = {ω | θtil n ω ∉ K} := fun n => by
    ext ω
    simp [hK'def, Set.mem_prod]
  have hK'' : Tendsto (fun n => P {ω | ((β₀, θtil n ω) : (κ → ℝ) × ℝ) ∉ K'}) atTop (𝓝 0) := by
    simp_rw [hset]
    exact hθK
  have h := tendstoInMeasure_nbJointMLE (P := P) (M := fun p : (κ → ℝ) × ℝ => M p.2) (K := K')
    (p₀ := (β₀, θ₀)) (phat := fun n ω => (β₀, θtil n ω)) x o y hK'c hMc hp₀ hpos hid hunif'
    hK'' hmax
  have h2 := tendstoInMeasure_snd_of_nbJointMLE h
  exact h2

/-! ### Plugging the restricted shape into the coefficient score -/

/-- The coefficient score of the first `n` observations at coefficients `β₀` and shape `θ`, as a
vector of `EuclideanSpace ℝ κ`: `∑_{i<n} nbScore θ yᵢ ηᵢ • xᵢ` with `ηᵢ = xᵢ ⬝ᵥ β₀ + oᵢ`. -/
noncomputable def nbCoefScoreSum (x : ℕ → Ω → κ → ℝ) (o : ℕ → Ω → ℝ) (y : ℕ → Ω → ℕ)
    (β₀ : κ → ℝ) (n : ℕ) (ω : Ω) (θ : ℝ) : EuclideanSpace ℝ κ :=
  ∑ i ∈ range n, nbScore θ (y i ω) (x i ω ⬝ᵥ β₀ + o i ω) • WithLp.toLp 2 (x i ω)

/-- The averaged cross term `n⁻¹ ∑_{i<n} nbCross θ yᵢ ηᵢ • xᵢ`, the `θ`-derivative of the
averaged coefficient score. -/
noncomputable def nbCrossAvg (x : ℕ → Ω → κ → ℝ) (o : ℕ → Ω → ℝ) (y : ℕ → Ω → ℕ)
    (β₀ : κ → ℝ) (n : ℕ) (ω : Ω) (θ : ℝ) : EuclideanSpace ℝ κ :=
  (n : ℝ)⁻¹ • ∑ i ∈ range n, nbCross θ (y i ω) (x i ω ⬝ᵥ β₀ + o i ω) • WithLp.toLp 2 (x i ω)

omit [MeasurableSpace Ω] in
/-- The `θ`-derivative of the coefficient score is the summed cross term
(`hasFDerivAt_nbScore_prod`). -/
theorem hasDerivAt_nbCoefScoreSum (x : ℕ → Ω → κ → ℝ) (o : ℕ → Ω → ℝ) (y : ℕ → Ω → ℕ)
    (β₀ : κ → ℝ) (n : ℕ) (ω : Ω) {θ : ℝ} (hθ : 0 < θ) :
    HasDerivAt (nbCoefScoreSum x o y β₀ n ω)
      (∑ i ∈ range n, nbCross θ (y i ω) (x i ω ⬝ᵥ β₀ + o i ω) • WithLp.toLp 2 (x i ω)) θ := by
  unfold nbCoefScoreSum
  refine HasDerivAt.fun_sum fun i _ => HasDerivAt.smul_const ?_ _
  have hpath : HasDerivAt (fun t : ℝ => (t, x i ω ⬝ᵥ β₀ + o i ω)) ((1 : ℝ), (0 : ℝ)) θ :=
    (hasDerivAt_id θ).prodMk (hasDerivAt_const θ _)
  have h := (hasFDerivAt_nbScore_prod hθ (y i ω : ℝ) (x i ω ⬝ᵥ β₀ + o i ω)).comp_hasDerivAt_of_eq
    θ hpath rfl
  exact h.congr_deriv (by simp)

omit [MeasurableSpace Ω] in
/-- **Mean-value bound for the coefficient score in the shape.** On a closed ball of shapes
around `θ₀` that stays in `θ > 0`, if the summed cross term is bounded by `B`, then
`‖S(θ) - S(θ₀)‖ ≤ B |θ - θ₀|`. -/
theorem norm_nbCoefScoreSum_sub_le (x : ℕ → Ω → κ → ℝ) (o : ℕ → Ω → ℝ) (y : ℕ → Ω → ℕ)
    (β₀ : κ → ℝ) (n : ℕ) (ω : Ω) {θ₀ δ B : ℝ} (hδθ : δ < θ₀)
    (hB : ∀ c ∈ Metric.closedBall θ₀ δ,
      ‖∑ i ∈ range n, nbCross c (y i ω) (x i ω ⬝ᵥ β₀ + o i ω) • WithLp.toLp 2 (x i ω)‖ ≤ B)
    {θ : ℝ} (hθ : θ ∈ Metric.closedBall θ₀ δ) :
    ‖nbCoefScoreSum x o y β₀ n ω θ - nbCoefScoreSum x o y β₀ n ω θ₀‖ ≤ B * |θ - θ₀| := by
  have hpos : ∀ c ∈ Metric.closedBall θ₀ δ, 0 < c := fun c hc => by
    rw [Metric.mem_closedBall, Real.dist_eq] at hc
    linarith [(abs_le.1 hc).1]
  have h0 : θ₀ ∈ Metric.closedBall θ₀ δ := Metric.mem_closedBall_self (dist_nonneg.trans hθ)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun c hc => (hasDerivAt_nbCoefScoreSum x o y β₀ n ω (hpos c hc)).hasDerivWithinAt) hB
    (convex_closedBall θ₀ δ) h0 hθ
  simpa [Real.norm_eq_abs] using h

omit [MeasurableSpace Ω] in
/-- The summed cross term is `n` times the averaged one. -/
theorem norm_nbCrossSum_le (x : ℕ → Ω → κ → ℝ) (o : ℕ → Ω → ℝ) (y : ℕ → Ω → ℕ)
    (β₀ : κ → ℝ) (n : ℕ) (ω : Ω) (c : ℝ) :
    ‖∑ i ∈ range n, nbCross c (y i ω) (x i ω ⬝ᵥ β₀ + o i ω) • WithLp.toLp 2 (x i ω)‖ ≤
      n * ‖nbCrossAvg x o y β₀ n ω c‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [nbCrossAvg, norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast, ← mul_assoc,
      mul_inv_cancel₀ (by positivity), one_mul]

private lemma inv_sqrt_mul_self {r : ℝ} (hr : 0 ≤ r) : (√r)⁻¹ * r = √r := by
  rcases hr.eq_or_lt with rfl | h
  · simp
  · rw [inv_mul_eq_div, div_eq_iff (Real.sqrt_pos.2 h).ne', Real.mul_self_sqrt hr]

/-- **The restricted shape does not move the coefficient score (orthogonality).** Let `θ̃ n` be
consistent for `θ₀ > 0` with `√n (θ̃ n - θ₀)` bounded in probability (`htight`), and let the
averaged cross term `nbCrossAvg` tend to zero uniformly on a closed ball `|θ - θ₀| ≤ δ < θ₀` in
probability (`hcross`). Then the scaled coefficient scores at `θ̃ n` and at `θ₀` differ by a term
tending to zero in probability:
`n^{-1/2} (S(θ̃ n) - S(θ₀)) → 0`.

The proof is the mean-value bound `norm_nbCoefScoreSum_sub_le`:
`‖n^{-1/2} (S(θ̃) - S(θ₀))‖ ≤ sup_{|c - θ₀| ≤ δ} ‖nbCrossAvg c‖ · √n |θ̃ - θ₀|`. The uniform law of
large numbers for the cross term is a hypothesis; its limit is zero because
`E[y - μ | x] = 0` under `H₀` for every shape (`hasSum_nbCross_mul_negBinomialReal`). -/
theorem tendstoInMeasure_nbCoefScore_restricted_sub (x : ℕ → Ω → κ → ℝ) (o : ℕ → Ω → ℝ)
    (y : ℕ → Ω → ℕ) (β₀ : κ → ℝ) {θ₀ δ : ℝ} (hδ : 0 < δ) (hδθ : δ < θ₀)
    {θtil : ℕ → Ω → ℝ} (hcons : TendstoInMeasure P θtil atTop (fun _ => θ₀))
    (htight : ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, P {ω | C < √(n : ℝ) * |θtil n ω - θ₀|} ≤ ε)
    (hcross : ∀ ε > 0, Tendsto (fun n : ℕ => P {ω | ∃ c ∈ Metric.closedBall θ₀ δ,
      ε ≤ ‖nbCrossAvg x o y β₀ n ω c‖}) atTop (𝓝 0)) :
    TendstoInMeasure P
      ((fun (n : ℕ) ω => (√(n : ℝ))⁻¹ • nbCoefScoreSum x o y β₀ n ω (θtil n ω)) -
        fun (n : ℕ) ω => (√(n : ℝ))⁻¹ • nbCoefScoreSum x o y β₀ n ω θ₀) atTop 0 := by
  rw [tendstoInMeasure_iff_norm]
  have hcons' := tendstoInMeasure_iff_dist.1 hcons
  intro η hη
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨C, hC⟩ := htight (ε / 2) (ENNReal.half_pos hε.ne')
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set γ := η / (C' + 1) with hγdef
  have hγ : 0 < γ := div_pos hη (by positivity)
  have h13 := (hcons' δ hδ).add (hcross γ hγ)
  rw [add_zero] at h13
  have h13' := (ENNReal.tendsto_nhds_zero.1 h13) (ε / 2) (ENNReal.half_pos hε.ne')
  filter_upwards [hC, h13'] with n hn2 hn13
  refine (measure_mono (t := ({ω | δ ≤ dist (θtil n ω) θ₀} ∪
      {ω | ∃ c ∈ Metric.closedBall θ₀ δ, γ ≤ ‖nbCrossAvg x o y β₀ n ω c‖}) ∪
      {ω | C < √(n : ℝ) * |θtil n ω - θ₀|}) ?_).trans ((measure_union_le _ _).trans ?_)
  · intro ω hω
    simp only [Set.mem_ofPred_eq, Pi.sub_apply, Pi.zero_apply, sub_zero] at hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le, not_lt, not_exists,
      not_and] at hcon
    obtain ⟨⟨h1, h3⟩, h2⟩ := hcon
    have hθ : θtil n ω ∈ Metric.closedBall θ₀ δ := Metric.mem_closedBall.2 h1.le
    have hB : ∀ c ∈ Metric.closedBall θ₀ δ,
        ‖∑ i ∈ range n, nbCross c (y i ω) (x i ω ⬝ᵥ β₀ + o i ω) • WithLp.toLp 2 (x i ω)‖ ≤
          n * γ := fun c hc =>
      (norm_nbCrossSum_le x o y β₀ n ω c).trans
        (mul_le_mul_of_nonneg_left (h3 c hc).le (Nat.cast_nonneg n))
    have hmv := norm_nbCoefScoreSum_sub_le x o y β₀ n ω hδθ hB hθ
    have hsq : 0 ≤ (√(n : ℝ))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
    have hle : ‖(√(n : ℝ))⁻¹ • nbCoefScoreSum x o y β₀ n ω (θtil n ω) -
        (√(n : ℝ))⁻¹ • nbCoefScoreSum x o y β₀ n ω θ₀‖ ≤ γ * C' := by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hsq]
      calc (√(n : ℝ))⁻¹ * ‖nbCoefScoreSum x o y β₀ n ω (θtil n ω) -
            nbCoefScoreSum x o y β₀ n ω θ₀‖
          ≤ (√(n : ℝ))⁻¹ * (n * γ * |θtil n ω - θ₀|) := mul_le_mul_of_nonneg_left hmv hsq
        _ = γ * ((√(n : ℝ))⁻¹ * n * |θtil n ω - θ₀|) := by ring
        _ = γ * (√(n : ℝ) * |θtil n ω - θ₀|) := by
          rw [inv_sqrt_mul_self (Nat.cast_nonneg n)]
        _ ≤ γ * C' := mul_le_mul_of_nonneg_left (h2.trans (le_max_left _ _)) hγ.le
    have hlt : γ * C' < η := by
      have : γ * (C' + 1) = η := by rw [hγdef]; field_simp
      nlinarith
    linarith
  · calc P ({ω | δ ≤ dist (θtil n ω) θ₀} ∪
          {ω | ∃ c ∈ Metric.closedBall θ₀ δ, γ ≤ ‖nbCrossAvg x o y β₀ n ω c‖}) +
          P {ω | C < √(n : ℝ) * |θtil n ω - θ₀|}
        ≤ (P {ω | δ ≤ dist (θtil n ω) θ₀} +
          P {ω | ∃ c ∈ Metric.closedBall θ₀ δ, γ ≤ ‖nbCrossAvg x o y β₀ n ω c‖}) +
          P {ω | C < √(n : ℝ) * |θtil n ω - θ₀|} := by
          gcongr
          exact measure_union_le _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add hn13 hn2
      _ = ε := ENNReal.add_halves ε

/-! ### Composite score and likelihood-ratio limits -/

/-- Two sequences tending to zero in probability have difference tending to zero in
probability. -/
private theorem tendstoInMeasure_sub_zero {U V : ℕ → Ω → ℝ} (hU : TendstoInMeasure P U atTop 0)
    (hV : TendstoInMeasure P V atTop 0) : TendstoInMeasure P (U - V) atTop 0 := by
  rw [tendstoInMeasure_iff_norm] at hU hV ⊢
  intro ε hε
  have h2 := (hU (ε / 2) (by positivity)).add (hV (ε / 2) (by positivity))
  rw [add_zero] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun _ => zero_le)
    fun i => (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  simp only [Set.mem_ofPred_eq, Pi.zero_apply, Pi.sub_apply, sub_zero, Real.norm_eq_abs]
    at hω ⊢
  by_contra h
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at h
  linarith [abs_sub (U i ω) (V i ω)]

variable [IsProbabilityMeasure P]
  {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {Ω'' : Type*} [MeasurableSpace Ω''] {P'' : Measure Ω''} [IsProbabilityMeasure P'']

/-- **Rao statistic with a perturbed score and an estimated information.** Let `A` be a
symmetric positive definite operator on a finite-dimensional real inner product space `E` of
dimension `d ≥ 1`, and `Tₙ →ᵈ V` with `V ~ N(0, A)`. If `T̃ₙ - Tₙ → 0` and `Âₙ → A` in
probability, then `⟪Âₙ⁻¹ T̃ₙ, T̃ₙ⟫ → χ²_d`. The inverse is `Ring.inverse` (`0` at singular
`Âₙ ω`, an event of probability tending to `0`). -/
theorem tendstoInDistribution_quadForm_of_sub {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {A : E →L[ℝ] E} (hA_symm : ∀ u v, ⟪A u, v⟫ = ⟪u, A v⟫)
    (hA_pos : ∀ u, u ≠ 0 → 0 < ⟪A u, u⟫) (hd : 0 < Module.finrank ℝ E)
    {V : Ω' → E} (hV_meas : AEMeasurable V P')
    (hV : ∀ t, HasLaw (fun ω => ⟪V ω, t⟫) (gaussianReal 0 (⟪A t, t⟫).toNNReal) P')
    {T Ttil : ℕ → Ω → E} (hT : TendstoInDistribution T atTop V (fun _ => P) P')
    (hsub : TendstoInMeasure P (Ttil - T) atTop 0) (hTtil_meas : ∀ n, AEMeasurable (Ttil n) P)
    {Ahat : ℕ → Ω → E →L[ℝ] E} (hAhat_meas : ∀ n, AEMeasurable (Ahat n) P)
    (hAhat : TendstoInMeasure P Ahat atTop (fun _ => A))
    {Q : Ω'' → ℝ} (hQ : HasLaw Q (chiSquareMeasure (Module.finrank ℝ E)) P'') :
    TendstoInDistribution (fun n ω => ⟪Ring.inverse (Ahat n ω) (Ttil n ω), Ttil n ω⟫) atTop Q
      (fun _ => P) P'' := by
  have h := tendstoInDistribution_of_tendstoInMeasure_sub Ttil V hT hsub hTtil_meas
  obtain ⟨u, hu⟩ := isUnit_of_inner_self_pos hA_pos
  have hK : TendstoInMeasure P (fun n ω => Ring.inverse (Ahat n ω)) atTop
      (fun _ => Ring.inverse A) :=
    hAhat.comp_const_of_continuousAt (hu ▸ NormedRing.inverse_continuousAt u)
  have hK_meas : ∀ n, AEMeasurable (fun ω => Ring.inverse (Ahat n ω)) P := fun n =>
    measurable_ring_inverse.comp_aemeasurable (hAhat_meas n)
  have hg : Continuous fun z : E × (E →L[ℝ] E) => ⟪z.2 z.1, z.1⟫ :=
    (isBoundedBilinearMap_apply.continuous.comp continuous_swap).inner continuous_fst
  have h2 := h.continuous_comp_prodMk_of_tendstoInMeasure_const hg hK hK_meas
  have hchi := hasLaw_inner_inverse_chiSquare hA_symm hA_pos hd hV_meas hV
  exact h2.of_map_eq hQ.aemeasurable (by rw [hQ.map_eq, ← hchi.map_eq])

/-- **Composite score test for `H₀ : β = β₀` with the shape estimated under `H₀`.** Let
`Tₙ = n^{-1/2} S(θ₀)` and `T̃ₙ = n^{-1/2} S(θ̃ n)` be the scaled coefficient scores
(`nbCoefScoreSum`) at the true shape and at the restricted estimate. Assume

* (T131, central limit theorem) `Tₙ →ᵈ V` with `V ~ N(0, A)`, `A` symmetric positive definite
  on `EuclideanSpace ℝ κ`, `κ` nonempty;
* (restricted estimate) `θ̃ n → θ₀ > 0` in probability with `√n (θ̃ n - θ₀)` bounded in
  probability, and the averaged cross term tends to zero uniformly on `|θ - θ₀| ≤ δ < θ₀` in
  probability (the hypotheses of `tendstoInMeasure_nbCoefScore_restricted_sub`);
* `Âₙ → A` in probability, `Âₙ` and `T̃ₙ` a.e.-measurable.

Then the Rao statistic `⟪Âₙ⁻¹ T̃ₙ, T̃ₙ⟫ → χ²_{|κ|}`. Only `θ` is estimated: the statistic needs
no fit of the unrestricted model. -/
theorem tendstoInDistribution_nbCompositeScoreStatistic [Nonempty κ] (x : ℕ → Ω → κ → ℝ)
    (o : ℕ → Ω → ℝ) (y : ℕ → Ω → ℕ) (β₀ : κ → ℝ) {θ₀ δ : ℝ} (hδ : 0 < δ) (hδθ : δ < θ₀)
    {θtil : ℕ → Ω → ℝ} (hcons : TendstoInMeasure P θtil atTop (fun _ => θ₀))
    (htight : ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, P {ω | C < √(n : ℝ) * |θtil n ω - θ₀|} ≤ ε)
    (hcross : ∀ ε > 0, Tendsto (fun n : ℕ => P {ω | ∃ c ∈ Metric.closedBall θ₀ δ,
      ε ≤ ‖nbCrossAvg x o y β₀ n ω c‖}) atTop (𝓝 0))
    {A : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ} (hA_symm : ∀ u v, ⟪A u, v⟫ = ⟪u, A v⟫)
    (hA_pos : ∀ u, u ≠ 0 → 0 < ⟪A u, u⟫)
    {V : Ω' → EuclideanSpace ℝ κ} (hV_meas : AEMeasurable V P')
    (hV : ∀ t, HasLaw (fun ω => ⟪V ω, t⟫) (gaussianReal 0 (⟪A t, t⟫).toNNReal) P')
    (hT : TendstoInDistribution (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ • nbCoefScoreSum x o y β₀ n ω θ₀)
      atTop V (fun _ => P) P')
    (hTtil_meas : ∀ n : ℕ, AEMeasurable
      (fun ω => (√(n : ℝ))⁻¹ • nbCoefScoreSum x o y β₀ n ω (θtil n ω)) P)
    {Ahat : ℕ → Ω → EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ}
    (hAhat_meas : ∀ n, AEMeasurable (Ahat n) P)
    (hAhat : TendstoInMeasure P Ahat atTop (fun _ => A))
    {Q : Ω'' → ℝ} (hQ : HasLaw Q (chiSquareMeasure (Fintype.card κ)) P'') :
    TendstoInDistribution (fun (n : ℕ) ω =>
        ⟪Ring.inverse (Ahat n ω) ((√(n : ℝ))⁻¹ • nbCoefScoreSum x o y β₀ n ω (θtil n ω)),
          (√(n : ℝ))⁻¹ • nbCoefScoreSum x o y β₀ n ω (θtil n ω)⟫)
      atTop Q (fun _ => P) P'' := by
  have hd : 0 < Module.finrank ℝ (EuclideanSpace ℝ κ) := by
    rw [finrank_euclideanSpace]; exact Fintype.card_pos
  rw [← finrank_euclideanSpace (𝕜 := ℝ) (ι := κ)] at hQ
  exact tendstoInDistribution_quadForm_of_sub hA_symm hA_pos hd hV_meas hV hT
    (tendstoInMeasure_nbCoefScore_restricted_sub x o y β₀ hδ hδθ hcons htight hcross)
    hTtil_meas hAhat_meas hAhat hQ

/-- The matrix quadratic form `Tᵀ A⁻¹ T` is the inner-product form `⟪S⁻¹ T, T⟫` of the operator
`S = toEuclideanCLM A` on `EuclideanSpace ℝ κ`, for invertible `A`. -/
theorem inner_ringInverse_toEuclideanCLM [DecidableEq κ] {A : Matrix κ κ ℝ} (hA : IsUnit A)
    (T : κ → ℝ) :
    ⟪Ring.inverse (toEuclideanCLM (𝕜 := ℝ) A) (WithLp.toLp 2 T), WithLp.toLp 2 T⟫ =
      T ⬝ᵥ (A⁻¹ *ᵥ T) := by
  rw [← hA.map_ringInverse (toEuclideanCLM (𝕜 := ℝ) (n := κ)), ← nonsing_inv_eq_ringInverse,
    real_inner_comm, inner_toEuclideanCLM]

/-- **Composite likelihood-ratio test for `H₀ : β = β₀` with the shape free.** Let `p̂ n` be the
joint estimate, `θ̃ n` the restricted estimate under `H₀`, and `Tₙ`, `Uₙ` the scaled coefficient
and shape scores at the truth `(β₀, θ₀)`. Assume, from the joint `(β, θ)` setup of T131:

* (block-diagonal information) the limit information is `I = [[A, 0], [0, D]]` with `A`
  positive definite and `D ≠ 0`;
* (Wilks expansion, joint MLE) `2 (ℓₙ(p̂) - ℓₙ(β₀, θ₀)) - sₙᵀ I⁻¹ sₙ → 0` in probability,
  `sₙ = (Tₙ, Uₙ)`;
* (Wilks expansion, restricted MLE) `2 (ℓₙ(β₀, θ̃) - ℓₙ(β₀, θ₀)) - Uₙ² / D → 0` in probability;
* (central limit theorem) `Tₙ →ᵈ V` with `V ~ N(0, A)`;
* the statistic is a.e.-measurable, and `κ` is nonempty.

Then `2 (ℓₙ(p̂) - ℓₙ(β₀, θ̃)) → χ²_{|κ|}`. The proof subtracts the two expansions
(`nbCompositeLRStat_eq_sub`); by block-diagonality the shape parts cancel
(`sumElim_dotProduct_inv_fromBlocks_mulVec`), leaving `Tₙᵀ A⁻¹ Tₙ + o_P(1)`. -/
theorem tendstoInDistribution_nbCompositeLRStat [DecidableEq κ] [Nonempty κ]
    (x : ℕ → Ω → κ → ℝ) (o : ℕ → Ω → ℝ) (y : ℕ → Ω → ℕ) (β₀ : κ → ℝ) (θ₀ : ℝ)
    {phat : ℕ → Ω → (κ → ℝ) × ℝ} {θtil : ℕ → Ω → ℝ}
    {A : Matrix κ κ ℝ} (hA : A.PosDef) {D : ℝ} (hD : D ≠ 0)
    {T : ℕ → Ω → κ → ℝ} {U : ℕ → Ω → ℝ}
    (hfull : TendstoInMeasure P (fun (n : ℕ) ω =>
      2 * (nbJointLogLik (of fun i : Fin n => x i ω) (fun i => o i ω) (fun i => y i ω)
          (phat n ω) -
        nbJointLogLik (of fun i : Fin n => x i ω) (fun i => o i ω) (fun i => y i ω) (β₀, θ₀)) -
      Sum.elim (T n ω) (fun _ : Unit => U n ω) ⬝ᵥ
        ((fromBlocks A 0 0 (of fun _ _ : Unit => D))⁻¹ *ᵥ
          Sum.elim (T n ω) (fun _ : Unit => U n ω))) atTop 0)
    (hres : TendstoInMeasure P (fun (n : ℕ) ω =>
      2 * (nbRestrictedLogLik (of fun i : Fin n => x i ω) (fun i => o i ω) (fun i => y i ω) β₀
          (θtil n ω) -
        nbJointLogLik (of fun i : Fin n => x i ω) (fun i => o i ω) (fun i => y i ω) (β₀, θ₀)) -
      U n ω ^ 2 / D) atTop 0)
    {V : Ω' → EuclideanSpace ℝ κ} (hV_meas : AEMeasurable V P')
    (hV : ∀ t, HasLaw (fun ω => ⟪V ω, t⟫)
      (gaussianReal 0 (⟪toEuclideanCLM (𝕜 := ℝ) A t, t⟫).toNNReal) P')
    (hT : TendstoInDistribution (fun n ω => WithLp.toLp 2 (T n ω)) atTop V (fun _ => P) P')
    (hLR_meas : ∀ n : ℕ, AEMeasurable (fun ω => nbCompositeLRStat (of fun i : Fin n => x i ω)
      (fun i => o i ω) (fun i => y i ω) (phat n ω) β₀ (θtil n ω)) P)
    {Q : Ω'' → ℝ} (hQ : HasLaw Q (chiSquareMeasure (Fintype.card κ)) P'') :
    TendstoInDistribution (fun (n : ℕ) ω => nbCompositeLRStat (of fun i : Fin n => x i ω)
        (fun i => o i ω) (fun i => y i ω) (phat n ω) β₀ (θtil n ω))
      atTop Q (fun _ => P) P'' := by
  set S := toEuclideanCLM (𝕜 := ℝ) (n := κ) A with hSdef
  have hAu : IsUnit A := hA.isUnit
  have hAt : Aᵀ = A := by
    have h := hA.isHermitian
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at h
  have hS_symm : ∀ u v, ⟪S u, v⟫ = ⟪u, S v⟫ := fun u v => by
    rw [real_inner_comm, inner_toEuclideanCLM, inner_toEuclideanCLM, dotProduct_mulVec,
      ← mulVec_transpose, hAt, dotProduct_comm]
  have hS_pos : ∀ u, u ≠ 0 → 0 < ⟪S u, u⟫ := fun u hu => by
    rw [real_inner_comm, inner_toEuclideanCLM]
    have hu' : (WithLp.ofLp u : κ → ℝ) ≠ 0 := by rwa [Ne, WithLp.ofLp_eq_zero]
    have := hA.dotProduct_mulVec_pos hu'
    simpa using this
  have hd : 0 < Module.finrank ℝ (EuclideanSpace ℝ κ) := by
    rw [finrank_euclideanSpace]; exact Fintype.card_pos
  rw [← finrank_euclideanSpace (𝕜 := ℝ) (ι := κ)] at hQ
  -- the quadratic form in the coefficient score is asymptotically chi-square
  have hchi := hasLaw_inner_inverse_chiSquare hS_symm hS_pos hd hV_meas hV
  have hQn := (hT.continuous_comp (g := fun v => ⟪Ring.inverse S v, v⟫)
    (by fun_prop)).of_map_eq hQ.aemeasurable (by rw [hQ.map_eq, ← hchi.map_eq]; rfl)
  -- the composite statistic differs from it by `o_P(1)`
  have hdiff := tendstoInMeasure_sub_zero hfull hres
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ Q hQn ?_ hLR_meas
  refine hdiff.congr_left fun n => ae_of_all _ fun ω => ?_
  simp only [Pi.sub_apply, Function.comp_apply]
  rw [nbCompositeLRStat_eq_sub _ _ _ _ _ _ θ₀, sumElim_dotProduct_inv_fromBlocks_mulVec hAu hD,
    inner_ringInverse_toEuclideanCLM hAu]
  simp only [nbRestrictedLogLik]
  ring

end Asymptotics

end MathlibExt.Probability.Statistics.GLM.NegativeBinomial
