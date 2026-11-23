/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.KMBootstrap
public import MathlibExt.Probability.Statistics.Survival.CoxAsymptotics
public import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Bootstrap validity for the Cox estimator on a finite grid

Observations are triples `o = (T, d, z) ∈ ℝ × ℝ × ℝ`: an observed time `T`, an event flag (`d = 1`
marks an observed event, any other value a censoring) and a scalar covariate `z`. The observed
times lie on a finite grid `t : Fin k → ℝ` and the covariates take finitely many levels
`c : Fin q → ℝ` (both injective). The Cox estimator `coxMPLE y n` of the first `n` observations
is the maximizer of Cox's scalar log partial likelihood `logPartialLikelihood₁` (Breslow ties),
when one exists (`mple`).

**The bootstrap procedure.** Given data `x`, draw a resample `ω n 0, …, ω n (n - 1)` iid from the
empirical law of `x 0, …, x (n - 1)` (row `ω n` of `ProbabilityTheory.Bootstrap.world x`) and
recompute the Cox estimator on it: `β̂*ₙ = coxMPLE (ω n) n`. Laws under `world x` are
conditional laws given the data.

Unlike the Kaplan–Meier estimator (`KMBootstrap`), the Cox estimator has no closed form. The
approach: the Cox score is `n Ψ(x̄ₙ, b)` for a fixed smooth map `Ψ = scoreMap` of the mean `x̄ₙ` of
the indicator encoding `obsVec` (event and at-risk indicators by grid time and covariate level),
so the estimator is the root of `Ψ(x̄ₙ, ·)`. The implicit function theorem turns that root into a
smooth function `g` of `x̄ₙ` near the limit `θ`, and concavity of the partial likelihood makes the
estimator equal `g(x̄ₙ)` whenever `x̄ₙ` is near `θ`. The bootstrap delta method of
`ProbabilityTheory.Bootstrap`, applied to `g`, then gives bootstrap validity once the bootstrap
mean is shown to stay near `θ` with conditional probability tending to one.

## Main results

* `coxScore_eq_mul_scoreMap`: on grid data, `Uₙ(b) = n Ψ(x̄ₙ, b)` for every `b`.
* `exists_rootChart`: if `Ψ(θ, β₀) = 0`, the risk-set sums at `(θ, β₀)` are nonzero and the
  information `v = coxInfo c θ β₀ = -∂Ψ/∂b (θ, β₀)` is nonzero, the root of `Ψ(μ, ·)` near `β₀`
  is a measurable function `g μ` of `μ` near `θ`, strictly differentiable at `θ` with derivative
  `coxLimitMap c θ β₀ = v⁻¹ ∂Ψ/∂μ (θ, β₀)`.
* `coxMPLE_eq_of_chart`: on grid data whose encoded mean is near `θ`, `β̂ₙ = g(x̄ₙ)`.
* `tendstoInDistribution_bootstrap_coxMPLE`: **bootstrap validity for fixed data**. Under the
  conditions of the bootstrap delta method for the indicator means, conditionally on the data,
  `√n (β̂*ₙ - β̂ₙ) ⇒ v⁻¹ ⟪∇_μ Ψ(θ, β₀), Z⟫`.
* `coxMPLE_bootstrap_consistent`: for iid observations, `√n (β̂ₙ - β₀)` converges in
  distribution to `coxLimitMap c θ β₀ Z` (with `θ` the mean indicator vector and `Z` Gaussian
  with the covariance of the encoding), and for almost every data sequence the conditional law
  of `√n (β̂*ₙ - β̂ₙ)` has the same limit.

## Scope

* A scalar covariate with finitely many levels and a fixed finite time grid containing every
  observed time; continuous covariates and continuous time are out of scope. The bootstrap
  resamples whole observations (the "pairs" bootstrap).
* `θ` must give every grid time a positive at-risk probability (`hpos`), `β₀` must be a root of
  the limiting score `Ψ(θ, ·)` and the limiting information must be nonzero (`hinfo`). With a
  single covariate level the score map vanishes identically and `hinfo` fails; the test file
  exhibits this.
* Build on `KMBootstrap` (`ae_resample_mem`) and `ProbabilityTheory.Bootstrap`; the
  Kaplan–Meier bootstrap itself is not reproved. Three private helpers of `KMBootstrap` are
  copied here because they are private there: `tendstoInDistribution_comp_of_map_eq` and
  `inv_sqrt_smul_sum_sub_eq` verbatim, and `map_world_obsVec` adapted to the `(T, d, z)`
  encoding. The public `ProbabilityTheory.Bootstrap.map_world` cannot replace the last one: it
  needs the encoding to fix `0`, and `obsVec t c 0` has at-risk entries `1` whenever some
  `t j ≤ 0` and some level `c a = 0`, so the unused row zero is sent to `0` by hand.

## References

* D. R. Cox, *Regression models and life-tables*, J. Roy. Statist. Soc. Ser. B 34 (1972),
  187–220.
* B. Efron, *Censored data and the bootstrap*, J. Amer. Statist. Assoc. 76 (1981), 312–319.
* A. W. van der Vaart, *Asymptotic Statistics* (1998), Chapters 5 and 23 (Z-estimators and the
  bootstrap delta method).
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Finset Real
open scoped Topology ENNReal NNReal RealInnerProductSpace
open ProbabilityTheory.Bootstrap
open MathlibExt.Probability.Statistics.CoxPartialLikelihood

namespace MathlibExt.Probability.Statistics.CoxBootstrap

variable {k q : ℕ}

/-- The coordinate space of the indicator encoding. Coordinate `Sum.inl (j, a)` is the indicator
of an observed event at `t j` with covariate `c a`; coordinate `Sum.inr (j, a)` the indicator of
being at risk at `t j` with covariate `c a`. -/
abbrev Coord (k q : ℕ) := EuclideanSpace ℝ ((Fin k × Fin q) ⊕ (Fin k × Fin q))

open Classical in
/-- The indicator encoding of one observation `o = (T, d, z)` (time, event flag, covariate) on
the time grid `t` and covariate levels `c`: `𝟙{o = (t j, 1, c a)}` and
`𝟙{t j ≤ T ∧ z = c a}`. -/
noncomputable def obsVec (t : Fin k → ℝ) (c : Fin q → ℝ) (o : ℝ × ℝ × ℝ) : Coord k q :=
  WithLp.toLp 2 (Sum.elim (fun p => if o = (t p.1, 1, c p.2) then 1 else 0)
    (fun p => if t p.1 ≤ o.1 ∧ o.2.2 = c p.2 then 1 else 0))

@[simp]
theorem obsVec_inl (t : Fin k → ℝ) (c : Fin q → ℝ) (o : ℝ × ℝ × ℝ) (p : Fin k × Fin q)
    [Decidable (o = (t p.1, 1, c p.2))] :
    obsVec t c o (Sum.inl p) = if o = (t p.1, 1, c p.2) then 1 else 0 := by
  simp only [obsVec, PiLp.toLp_apply, Sum.elim_inl]
  congr

@[simp]
theorem obsVec_inr (t : Fin k → ℝ) (c : Fin q → ℝ) (o : ℝ × ℝ × ℝ) (p : Fin k × Fin q)
    [Decidable (t p.1 ≤ o.1 ∧ o.2.2 = c p.2)] :
    obsVec t c o (Sum.inr p) = if t p.1 ≤ o.1 ∧ o.2.2 = c p.2 then 1 else 0 := by
  simp only [obsVec, PiLp.toLp_apply, Sum.elim_inr]
  congr

/-- The risk-set sum `S⁽⁰⁾(μ, b, j) = ∑ₐ exp (b cₐ) μ(inr (j, a))`. -/
noncomputable def riskSum0 (c : Fin q → ℝ) (μ : Coord k q) (b : ℝ) (j : Fin k) : ℝ :=
  ∑ a, exp (b * c a) * μ (Sum.inr (j, a))

/-- The risk-set sum `S⁽¹⁾(μ, b, j) = ∑ₐ cₐ exp (b cₐ) μ(inr (j, a))`. -/
noncomputable def riskSum1 (c : Fin q → ℝ) (μ : Coord k q) (b : ℝ) (j : Fin k) : ℝ :=
  ∑ a, c a * exp (b * c a) * μ (Sum.inr (j, a))

/-- The **Cox score map** on the indicator space:
`Ψ(μ, b) = ∑_{j, a} μ(inl (j, a)) (cₐ - S⁽¹⁾(μ, b, j) / S⁽⁰⁾(μ, b, j))`. At the mean `μ = x̄ₙ` of
the encoded sample it is the Cox score divided by `n` (`coxScore_eq_mul_scoreMap`). -/
noncomputable def scoreMap (c : Fin q → ℝ) (μ : Coord k q) (b : ℝ) : ℝ :=
  ∑ j, ∑ a, μ (Sum.inl (j, a)) * (c a - riskSum1 c μ b j / riskSum0 c μ b j)

/-- The limiting Cox information `-∂Ψ/∂b` at `(μ, b)`. -/
noncomputable def coxInfo (c : Fin q → ℝ) (μ : Coord k q) (b : ℝ) : ℝ :=
  -deriv (scoreMap c μ) b

/-- The derivative of the Cox root in the indicator means: `v⁻¹ ∂Ψ/∂μ (θ, β₀)` with
`v = coxInfo c θ β₀`. -/
noncomputable def coxLimitMap (c : Fin q → ℝ) (θ : Coord k q) (β₀ : ℝ) : Coord k q →L[ℝ] ℝ :=
  (coxInfo c θ β₀)⁻¹ • fderiv ℝ (fun μ => scoreMap c μ β₀) θ

open Classical in
/-- The Cox data `(T, δ, z)` of `n` observations `(Tᵢ, dᵢ, zᵢ)`; `δᵢ` records `dᵢ = 1`. -/
noncomputable def coxArrays {n : ℕ} (v : Fin n → ℝ × ℝ × ℝ) :
    (Fin n → ℝ) × (Fin n → Bool) × (Fin n → ℝ) :=
  (fun i => (v i).1, fun i => decide ((v i).2.1 = 1), fun i => (v i).2.2)

open Classical in
/-- The **maximum partial likelihood estimator** of Cox data: a maximizer of the scalar log
partial likelihood when one exists, `0` otherwise. -/
noncomputable def mple {n : ℕ} (D : (Fin n → ℝ) × (Fin n → Bool) × (Fin n → ℝ)) : ℝ :=
  if h : ∃ b, IsMaxOn (logPartialLikelihood₁ D.1 D.2.1 D.2.2) Set.univ b then h.choose else 0

/-- The Cox estimator of the first `n` observations `y 0, …, y (n - 1)`. -/
noncomputable def coxMPLE (y : ℕ → ℝ × ℝ × ℝ) (n : ℕ) : ℝ :=
  mple (coxArrays fun i : Fin n => y i)

/-! ### The score bridge -/

section Bridge

variable {t : Fin k → ℝ} {c : Fin q → ℝ}

theorem sampleMeanVec_apply (y : ℕ → ℝ × ℝ × ℝ) (n : ℕ) (p : (Fin k × Fin q) ⊕ (Fin k × Fin q)) :
    sampleMeanVec (fun i => obsVec t c (y i)) n p =
      (n : ℝ)⁻¹ * ∑ l ∈ range n, obsVec t c (y l) p := by
  simp [sampleMeanVec]

/-- A weighted sum over the risk set of an observation at `t j` is the matching weighted sum
of at-risk counts by covariate level. -/
theorem sum_riskSet_eq (hc : Function.Injective c) (y : ℕ → ℝ × ℝ × ℝ) (n : ℕ)
    (hcov : ∀ i < n, (y i).2.2 ∈ Set.range c) (w : ℝ → ℝ) (i : Fin n) (j : Fin k)
    (hj : (y i).1 = t j) :
    ∑ l ∈ riskSet (coxArrays fun i : Fin n => y i).1 i,
        w ((coxArrays fun i : Fin n => y i).2.2 l) =
      ∑ a, w (c a) * ∑ l ∈ range n, obsVec t c (y l) (Sum.inr (j, a)) := by
  classical
  rw [show (∑ a, w (c a) * ∑ l ∈ range n, obsVec t c (y l) (Sum.inr (j, a))) =
      ∑ l : Fin n, ∑ a, w (c a) * obsVec t c (y l) (Sum.inr (j, a)) by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact (Fin.sum_univ_eq_sum_range
      (fun l => ∑ a, w (c a) * obsVec t c (y l) (Sum.inr (j, a))) n).symm]
  simp only [riskSet, coxArrays, Finset.sum_filter, hj]
  refine Finset.sum_congr rfl fun l _ => ?_
  obtain ⟨a₀, ha₀⟩ := hcov l l.isLt
  rw [Finset.sum_eq_single a₀]
  · by_cases h : t j ≤ (y l).1 <;> simp [h, ha₀]
  · intro a _ ha
    rw [obsVec_inr, ite_eq_right, mul_zero]
    rintro ⟨-, h⟩
    exact ha (hc (h.symm.trans ha₀.symm))
  · simp

/-- **The Cox score is `n` times the score map at the encoded sample mean.** If the first `n`
observed times lie on the grid `t` and the covariates take the levels `c`, then for every `b`,
`Uₙ(b) = n Ψ(x̄ₙ, b)`. -/
theorem coxScore_eq_mul_scoreMap (ht : Function.Injective t) (hc : Function.Injective c)
    (y : ℕ → ℝ × ℝ × ℝ) (n : ℕ) (hgrid : ∀ i < n, (y i).1 ∈ Set.range t)
    (hcov : ∀ i < n, (y i).2.2 ∈ Set.range c) (b : ℝ) :
    coxScore (coxArrays fun i : Fin n => y i).1 (coxArrays fun i : Fin n => y i).2.1
        (coxArrays fun i : Fin n => y i).2.2 b =
      n * scoreMap c (sampleMeanVec (fun i => obsVec t c (y i)) n) b := by
  classical
  set μ := sampleMeanVec (fun i => obsVec t c (y i)) n with hμ
  set A := coxArrays fun i : Fin n => y i with hA
  rcases eq_or_ne n 0 with rfl | hn
  · simp [coxScore]
  have hninv : (n : ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 hn)
  have hscale : ∀ (j : Fin k) (f : Fin q → ℝ), ∑ a, f a * μ (Sum.inr (j, a)) =
      (n : ℝ)⁻¹ * ∑ a, f a * ∑ l ∈ range n, obsVec t c (y l) (Sum.inr (j, a)) := fun j f => by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hμ, sampleMeanVec_apply]
    ring
  have hR : ∀ (i : Fin n) (j : Fin k), (y i).1 = t j →
      riskMean A.1 A.2.2 b i = riskSum1 c μ b j / riskSum0 c μ b j := by
    intro i j hj
    have h1 := sum_riskSet_eq hc y n hcov (fun z => z * exp (b * z)) i j hj
    have h0 := sum_riskSet_eq hc y n hcov (fun z => exp (b * z)) i j hj
    simp only at h1 h0
    rw [riskMean, h1, h0, riskSum1, riskSum0, hscale j, hscale j, mul_div_mul_left _ _ hninv]
  have key : ∀ i : Fin n, (if A.2.1 i = true then A.2.2 i - riskMean A.1 A.2.2 b i else 0) =
      ∑ j, ∑ a, obsVec t c (y i) (Sum.inl (j, a)) *
        (c a - riskSum1 c μ b j / riskSum0 c μ b j) := by
    intro i
    obtain ⟨j₀, hj₀⟩ := hgrid i i.isLt
    obtain ⟨a₀, ha₀⟩ := hcov i i.isLt
    by_cases hd : (y i).2.1 = 1
    · have hind : ∀ j a, obsVec t c (y i) (Sum.inl (j, a)) = if j = j₀ ∧ a = a₀ then 1 else 0 := by
        intro j a
        rw [obsVec_inl]
        refine if_congr ?_ rfl rfl
        rw [Prod.ext_iff, Prod.ext_iff, ← hj₀, ← ha₀, ht.eq_iff, hc.eq_iff]
        simp only [hd, true_and]
        exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩⟩
      simp only [hind, ite_and, ite_mul, one_mul, zero_mul]
      have hδ : A.2.1 i = true := by simp [hA, coxArrays, hd]
      rw [ite_eq_left hδ, hR i j₀ hj₀.symm]
      simp [hA, coxArrays, ha₀]
    · have hδ : ¬ A.2.1 i = true := by simp [hA, coxArrays, hd]
      rw [ite_eq_right hδ]
      refine (Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun a _ => ?_).symm
      rw [obsVec_inl, ite_eq_right, zero_mul]
      intro h
      exact hd (by rw [h])
  unfold coxScore scoreMap
  rw [Finset.sum_filter, Finset.sum_congr rfl fun i _ => key i, Finset.sum_comm,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range (fun l => obsVec t c (y l) (Sum.inl (j, a))) n,
    hμ, sampleMeanVec_apply, ← mul_assoc, mul_inv_cancel_left₀ (Nat.cast_ne_zero.2 hn)]

end Bridge

/-! ### The Cox root as a smooth function of the indicator means -/

section Chart

variable {c : Fin q → ℝ}

/-- The score map is `C¹` jointly in `(μ, b)` wherever every risk-set sum is nonzero. -/
theorem contDiffAt_scoreMap {θ : Coord k q} {β₀ : ℝ} (hS : ∀ j, riskSum0 c θ β₀ j ≠ 0) :
    ContDiffAt ℝ 1 (fun p : Coord k q × ℝ => scoreMap c p.1 p.2) (θ, β₀) := by
  have hcoord : ∀ i, ContDiff ℝ 1 fun p : Coord k q × ℝ => p.1 i := fun i => by
    have : ContDiff ℝ 1 fun μ : Coord k q => μ i := by
      convert (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff using 1
      funext μ
      rfl
    exact this.comp contDiff_fst
  have hexp : ∀ a, ContDiff ℝ 1 fun p : Coord k q × ℝ => exp (p.2 * c a) := fun a =>
    (contDiff_snd.mul contDiff_const).exp
  have h0 : ∀ j, ContDiff ℝ 1 fun p : Coord k q × ℝ => riskSum0 c p.1 p.2 j := fun j => by
    unfold riskSum0
    exact ContDiff.sum fun a _ => (hexp a).mul (hcoord _)
  have h1 : ∀ j, ContDiff ℝ 1 fun p : Coord k q × ℝ => riskSum1 c p.1 p.2 j := fun j => by
    unfold riskSum1
    exact ContDiff.sum fun a _ => (contDiff_const.mul (hexp a)).mul (hcoord _)
  unfold scoreMap
  refine ContDiffAt.sum fun j _ => ContDiffAt.sum fun a _ => ?_
  exact (hcoord _).contDiffAt.mul
    (contDiffAt_const.sub (((h1 j).contDiffAt).div (h0 j).contDiffAt (hS j)))

/-- **The implicit-function chart of the Cox root.** If `Ψ(θ, β₀) = 0`, every risk-set sum at
`(θ, β₀)` is nonzero and the information `v = -∂Ψ/∂b (θ, β₀)` is nonzero, there are a
measurable `g` and `ε > 0` with `g θ = β₀`, `g` strictly differentiable at `θ` with derivative
`v⁻¹ ∂Ψ/∂μ (θ, β₀)`, and, for `μ` within `ε` of `θ`, `g μ` is the only root of `Ψ(μ, ·)` within
`ε` of `g μ`. -/
theorem exists_rootChart {θ : Coord k q} {β₀ : ℝ} (hS : ∀ j, riskSum0 c θ β₀ j ≠ 0)
    (hroot : scoreMap c θ β₀ = 0) (hinfo : coxInfo c θ β₀ ≠ 0) :
    ∃ g : Coord k q → ℝ, ∃ ε > 0, Measurable g ∧
      HasStrictFDerivAt g (coxLimitMap c θ β₀) θ ∧ g θ = β₀ ∧
      ∀ μ, dist μ θ < ε → scoreMap c μ (g μ) = 0 ∧
        ∀ b, dist b (g μ) < ε → scoreMap c μ b = 0 → b = g μ := by
  classical
  set f : Coord k q × ℝ → ℝ := fun p => scoreMap c p.1 p.2 with hf
  have cdf : ContDiffAt ℝ 1 f (θ, β₀) := contDiffAt_scoreMap hS
  have hdiff : DifferentiableAt ℝ f (θ, β₀) := cdf.differentiableAt (by norm_num)
  have hA₂ : fderiv ℝ f (θ, β₀) ∘L ContinuousLinearMap.inr ℝ (Coord k q) ℝ =
      fderiv ℝ (scoreMap c θ) β₀ := by
    have h : HasFDerivAt (scoreMap c θ)
        (fderiv ℝ f (θ, β₀) ∘L ContinuousLinearMap.inr ℝ (Coord k q) ℝ) β₀ :=
      HasFDerivAt.comp (g := f) β₀ hdiff.hasFDerivAt (hasFDerivAt_prodMk_right (𝕜 := ℝ) θ β₀)
    exact h.fderiv.symm
  have hA₁ : fderiv ℝ f (θ, β₀) ∘L ContinuousLinearMap.inl ℝ (Coord k q) ℝ =
      fderiv ℝ (fun μ => scoreMap c μ β₀) θ := by
    have h : HasFDerivAt (fun μ => scoreMap c μ β₀)
        (fderiv ℝ f (θ, β₀) ∘L ContinuousLinearMap.inl ℝ (Coord k q) ℝ) θ :=
      HasFDerivAt.comp (g := f) θ hdiff.hasFDerivAt (hasFDerivAt_prodMk_left (𝕜 := ℝ) θ β₀)
    exact h.fderiv.symm
  set d := deriv (scoreMap c θ) β₀ with hd_def
  have hd : d ≠ 0 := fun h => hinfo (by simp [coxInfo, ← hd_def, h])
  have hA₂x : ∀ x : ℝ, (fderiv ℝ f (θ, β₀) ∘L ContinuousLinearMap.inr ℝ (Coord k q) ℝ) x =
      x * d := fun x => by
    rw [hA₂, ← toSpanSingleton_deriv]
    simp [hd_def]
  have if₂ : (fderiv ℝ f (θ, β₀) ∘L ContinuousLinearMap.inr ℝ (Coord k q) ℝ).IsInvertible := by
    refine ContinuousLinearMap.IsInvertible.of_inverse
      (g := d⁻¹ • ContinuousLinearMap.id ℝ ℝ) ?_ ?_
    · ext
      simp only [ContinuousLinearMap.comp_apply, smul_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul, mul_one, hA₂x]
      field_simp
    · ext
      simp only [ContinuousLinearMap.comp_apply, smul_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul, one_mul, hA₂x]
      field_simp
  set g₀ := cdf.implicitFunction (by norm_num) if₂ with hg₀
  have hg₀θ : g₀ θ = β₀ := cdf.implicitFunction_apply_self _ if₂
  have hD : HasStrictFDerivAt g₀ (coxLimitMap c θ β₀) θ := by
    have h := cdf.hasStrictFDerivAt_implicitFunction (by norm_num) if₂
    convert h using 1
    ext v
    have hinv : (fderiv ℝ f (θ, β₀) ∘L ContinuousLinearMap.inr ℝ (Coord k q) ℝ).inverse
        (fderiv ℝ (fun μ => scoreMap c μ β₀) θ v) =
        fderiv ℝ (fun μ => scoreMap c μ β₀) θ v / d :=
      if₂.inverse_apply_eq.2 (by rw [hA₂x]; field_simp)
    simp only [neg_apply, ContinuousLinearMap.comp_apply, hA₁,
      coxLimitMap, smul_apply, smul_eq_mul, coxInfo, ← hd_def]
    rw [hinv]
    field_simp
  -- local uniqueness of the root
  obtain ⟨r, hr, hrball⟩ := Metric.eventually_nhds_iff.1
    (cdf.eventually_apply_eq_iff_implicitFunction (by norm_num) if₂)
  have hbox : ∀ μ b, dist μ θ < r → dist b β₀ < r → (scoreMap c μ b = 0 ↔ g₀ μ = b) := by
    intro μ b hμ hb
    have h := hrball (y := (μ, b)) (by rw [Prod.dist_eq]; exact max_lt hμ hb)
    simpa [hf, hroot] using h
  obtain ⟨ε₁, hε₁, hg₁⟩ := Metric.continuousAt_iff.1 hD.continuousAt (r / 2) (half_pos hr)
  have hcd : ContDiffAt ℝ 1 g₀ θ := cdf.contDiffAt_implicitFunction (by norm_num) if₂
  obtain ⟨ρ, hρ, hρball⟩ := Metric.eventually_nhds_iff.1
    ((hcd.eventually (by simp)).mono fun y hy => hy.continuousAt)
  set s := Metric.closedBall θ (ρ / 2) with hs
  set g : Coord k q → ℝ := s.piecewise g₀ 0 with hg
  have hgs : ∀ μ, dist μ θ < ρ / 2 → g μ = g₀ μ := fun μ h =>
    Set.piecewise_eq_of_mem _ _ _ (Metric.mem_closedBall.2 h.le)
  refine ⟨g, min (min (r / 2) ε₁) (ρ / 2), by positivity, ?_, ?_, ?_, ?_⟩
  · refine ContinuousOn.measurable_piecewise ?_ continuousOn_const
      Metric.isClosed_closedBall.measurableSet
    intro μ hμ
    exact (hρball (lt_of_le_of_lt (Metric.mem_closedBall.1 hμ)
      (half_lt_self hρ))).continuousWithinAt
  · refine hD.congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds θ (half_pos hρ)] with μ hμ
    exact (hgs μ hμ).symm
  · rw [hgs θ (by simpa using half_pos hρ), hg₀θ]
  · intro μ hμ
    have hμ' : dist μ θ < r / 2 ∧ dist μ θ < ε₁ ∧ dist μ θ < ρ / 2 := by
      simp only [lt_min_iff] at hμ
      exact ⟨hμ.1.1, hμ.1.2, hμ.2⟩
    have hε : min (min (r / 2) ε₁) (ρ / 2) ≤ r / 2 := (min_le_left _ _).trans (min_le_left _ _)
    rw [hgs μ hμ'.2.2]
    have hgμ : dist (g₀ μ) β₀ < r / 2 := by simpa [hg₀θ] using hg₁ hμ'.2.1
    refine ⟨(hbox μ (g₀ μ) (by linarith [hμ'.1]) (by linarith)).2 rfl, fun b hb hb0 => ?_⟩
    have hb' : dist b β₀ < r := calc
      dist b β₀ ≤ dist b (g₀ μ) + dist (g₀ μ) β₀ := dist_triangle _ _ _
      _ < r / 2 + r / 2 := add_lt_add (hb.trans_le hε) hgμ
      _ = r := add_halves r
    exact ((hbox μ b (by linarith [hμ'.1]) hb').1 hb0).symm

end Chart

/-! ### The maximum partial likelihood estimator is the chart root -/

section Unique

/-- If the Cox score has the same roots as `Ψ`, `s` is a root of `Ψ` and no other root of `Ψ`
lies within `ε` of `s`, then the maximum partial likelihood estimator is `s`: by concavity
the roots of the score form an interval, so a second root would put roots arbitrarily close
to `s`. -/
theorem mple_eq_of_unique {n : ℕ} (D : (Fin n → ℝ) × (Fin n → Bool) × (Fin n → ℝ))
    {Ψ : ℝ → ℝ} {s ε : ℝ} (hε : 0 < ε) (hD : ∀ b, coxScore D.1 D.2.1 D.2.2 b = 0 ↔ Ψ b = 0)
    (hs : Ψ s = 0) (huniq : ∀ b, dist b s < ε → Ψ b = 0 → b = s) : mple D = s := by
  have hsU : coxScore D.1 D.2.1 D.2.2 s = 0 := (hD s).2 hs
  have hex : ∃ b, IsMaxOn (logPartialLikelihood₁ D.1 D.2.1 D.2.2) Set.univ b :=
    ⟨s, CoxAsymptotics.isMaxOn_of_coxScore_eq_zero _ _ _ hsU⟩
  rw [mple, dite_eq_left hex]
  have hb' : coxScore D.1 D.2.1 D.2.2 hex.choose = 0 :=
    CoxAsymptotics.coxScore_eq_zero_of_isMaxOn _ _ _ hex.choose_spec
  by_contra hne
  set b' := hex.choose
  set d := b' - s with hd_def
  have hd : d ≠ 0 := sub_ne_zero.2 hne
  have hdabs : 0 < |d| := abs_pos.2 hd
  set τ := min 1 (ε / (2 * |d|)) with hτ_def
  have hτ0 : 0 < τ := lt_min one_pos (div_pos hε (by positivity))
  have hτ1 : τ ≤ 1 := min_le_left _ _
  have hτd : |τ * d| < ε := by
    rw [abs_mul, abs_of_pos hτ0]
    calc τ * |d| ≤ ε / (2 * |d|) * |d| := mul_le_mul_of_nonneg_right (min_le_right _ _) hdabs.le
      _ = ε / 2 := by field_simp
      _ < ε := half_lt_self hε
  have hanti := CoxAsymptotics.antitone_coxScore D.1 D.2.1 D.2.2
  have hb''0 : coxScore D.1 D.2.1 D.2.2 (s + τ * d) = 0 := by
    rcases le_total 0 d with h | h
    · have h1 : s ≤ s + τ * d := le_add_of_nonneg_right (mul_nonneg hτ0.le h)
      have h2 : s + τ * d ≤ b' := by
        have : τ * d ≤ d := mul_le_of_le_one_left h hτ1
        linarith
      exact le_antisymm (hsU ▸ hanti h1) (hb' ▸ hanti h2)
    · have h1 : s + τ * d ≤ s := add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos hτ0.le h)
      have h2 : b' ≤ s + τ * d := by
        have : d ≤ τ * d := by nlinarith
        linarith
      exact le_antisymm (hb' ▸ hanti h2) (hsU ▸ hanti h1)
  have heq := huniq (s + τ * d) (by rw [Real.dist_eq]; simpa using hτd) ((hD _).1 hb''0)
  exact mul_ne_zero hτ0.ne' hd (by linarith)

/-- On data on the grid with at least one observation whose encoded mean lies within the chart
radius of `θ`, the Cox estimator is the chart root of the mean. -/
theorem coxMPLE_eq_of_chart {t : Fin k → ℝ} {c : Fin q → ℝ} (ht : Function.Injective t)
    (hc : Function.Injective c) (y : ℕ → ℝ × ℝ × ℝ) {n : ℕ} (hn : n ≠ 0)
    (hgrid : ∀ i < n, (y i).1 ∈ Set.range t) (hcov : ∀ i < n, (y i).2.2 ∈ Set.range c)
    {θ : Coord k q} {g : Coord k q → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hchart : ∀ μ, dist μ θ < ε → scoreMap c μ (g μ) = 0 ∧
      ∀ b, dist b (g μ) < ε → scoreMap c μ b = 0 → b = g μ)
    (hμ : dist (sampleMeanVec (fun i => obsVec t c (y i)) n) θ < ε) :
    coxMPLE y n = g (sampleMeanVec (fun i => obsVec t c (y i)) n) :=
  mple_eq_of_unique _ hε (fun b => by
      rw [coxScore_eq_mul_scoreMap ht hc y n hgrid hcov]
      simp [hn]) (hchart _ hμ).1 (hchart _ hμ).2

end Unique

/-! ### Measurability -/

section Measurability

theorem measurable_obsVec (t : Fin k → ℝ) (c : Fin q → ℝ) : Measurable (obsVec t c) := by
  classical
  refine (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.2 fun i => ?_)
  rcases i with p | p
  · exact Measurable.ite (measurableSet_singleton _) measurable_const measurable_const
  · exact Measurable.ite ((measurableSet_le measurable_const measurable_fst).inter
      (measurable_snd.snd (measurableSet_singleton _))) measurable_const measurable_const

/-- Every encoded coordinate is `0` or `1`, so the encoding is bounded. -/
theorem norm_obsVec_le (t : Fin k → ℝ) (c : Fin q → ℝ) (o : ℝ × ℝ × ℝ) :
    ‖obsVec t c o‖ ≤ √(∑ _i : (Fin k × Fin q) ⊕ (Fin k × Fin q), (1 : ℝ)) := by
  classical
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  rcases i with p | p <;> simp only [obsVec_inl, obsVec_inr] <;> split_ifs <;> norm_num

/-- A function of a random element that almost surely lies in a finite set is almost everywhere
measurable, whatever the function. -/
theorem aemeasurable_comp_of_ae_mem_finite {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    [MeasurableSingletonClass β] {μ : Measure Ω} {V : Ω → β} (hV : AEMeasurable V μ)
    {A : Set β} (hA : A.Finite) (hmem : ∀ᵐ ω ∂μ, V ω ∈ A) (f : β → ℝ) :
    AEMeasurable (fun ω => f (V ω)) μ := by
  classical
  set f' : β → ℝ := fun v => if v ∈ A then f v else 0 with hf'
  have hmeas : Measurable f' := by
    intro B _
    have h : f' ⁻¹' B = (A ∩ f ⁻¹' B) ∪ (Aᶜ ∩ {_v | (0 : ℝ) ∈ B}) := by
      ext v
      by_cases hv : v ∈ A <;> simp [hf', hv]
    rw [h]
    exact (hA.subset Set.inter_subset_left).measurableSet.union
      (hA.measurableSet.compl.inter (MeasurableSet.const _))
  exact (hmeas.comp_aemeasurable hV).congr (hmem.mono fun ω h => by simp [hf', h])

/-- The event flag `d = 1` is a measurable function of an observation. -/
theorem measurable_decide_event : Measurable fun o : ℝ × ℝ × ℝ => decide (o.2.1 = 1) := by
  refine measurable_to_countable' fun b => ?_
  have h1 : MeasurableSet {o : ℝ × ℝ × ℝ | o.2.1 = 1} :=
    measurable_snd.fst (measurableSet_singleton 1)
  cases b
  · have h : (fun o : ℝ × ℝ × ℝ => decide (o.2.1 = 1)) ⁻¹' {false} =
        {o : ℝ × ℝ × ℝ | o.2.1 = 1}ᶜ := by
      ext o
      simp
    rw [h]
    exact h1.compl
  · have h : (fun o : ℝ × ℝ × ℝ => decide (o.2.1 = 1)) ⁻¹' {true} =
        {o : ℝ × ℝ × ℝ | o.2.1 = 1} := by
      ext o
      simp
    rw [h]
    exact h1

theorem measurable_coxArrays (n : ℕ) :
    Measurable (coxArrays : (Fin n → ℝ × ℝ × ℝ) → (Fin n → ℝ) × (Fin n → Bool) × (Fin n → ℝ)) :=
  (Measurable.of_eval fun i => measurable_fst.comp (measurable_pi_apply i)).prodMk
    ((Measurable.of_eval fun i => measurable_decide_event.comp (measurable_pi_apply i)).prodMk
      (Measurable.of_eval fun i => measurable_snd.snd.comp (measurable_pi_apply i)))

end Measurability

/-! ### Limits of the encoded means -/

section Limits

variable {t : Fin k → ℝ} {c : Fin q → ℝ}

/-- A limit of encoded sample means has nonnegative at-risk coordinates. -/
theorem nonneg_of_tendsto {x : ℕ → ℝ × ℝ × ℝ} {θ : Coord k q}
    (hθ : Tendsto (sampleMeanVec fun i => obsVec t c (x i)) atTop (𝓝 θ)) (p : Fin k × Fin q) :
    0 ≤ θ (Sum.inr p) := by
  classical
  refine ge_of_tendsto (((PiLp.continuous_apply 2 _ (Sum.inr p)).tendsto θ).comp hθ)
    (Eventually.of_forall fun n => ?_)
  simp only [Function.comp_apply, sampleMeanVec_apply]
  refine mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (Finset.sum_nonneg fun l _ => ?_)
  rw [obsVec_inr]
  split_ifs <;> norm_num

/-- Nonnegative at-risk coordinates with a positive total at every grid time give positive
risk-set sums. -/
theorem riskSum0_pos {θ : Coord k q} (hnn : ∀ p, 0 ≤ θ (Sum.inr p))
    (hpos : ∀ j, 0 < ∑ a, θ (Sum.inr (j, a))) (b : ℝ) (j : Fin k) : 0 < riskSum0 c θ b j := by
  obtain ⟨a, -, ha⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ) (f := fun _ => (0 : ℝ))
    (g := fun a => θ (Sum.inr (j, a))) (by simpa using hpos j)
  exact Finset.sum_pos' (fun a _ => mul_nonneg (exp_pos _).le (hnn _))
    ⟨a, Finset.mem_univ _, mul_pos (exp_pos _) ha⟩

end Limits

/-! ### Transfer from the encoded bootstrap world -/

section Transfer

/-- Transfer convergence in distribution along a measure-preserving map.

Copy of the private `KMBootstrap.tendstoInDistribution_comp_of_map_eq` (also private in
`ProbabilityTheory.Bootstrap`). -/
private theorem tendstoInDistribution_comp_of_map_eq {Ω₁ Ω₂ Ω' F : Type*} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] [MeasurableSpace Ω'] [TopologicalSpace F] [MeasurableSpace F]
    [OpensMeasurableSpace F] {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂}
    {μ' : Measure Ω'} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    [IsProbabilityMeasure μ'] {Φ : Ω₁ → Ω₂} (hΦ : Measurable Φ) (hmap : μ₁.map Φ = μ₂)
    {Y : ℕ → Ω₂ → F} (hY : ∀ n, Measurable (Y n)) {Z : Ω' → F}
    (h : TendstoInDistribution Y atTop Z (fun _ => μ₂) μ') :
    TendstoInDistribution (fun n ω => Y n (Φ ω)) atTop Z (fun _ => μ₁) μ' := by
  refine ⟨fun n => ((hY n).comp hΦ).aemeasurable, h.aemeasurable_limit, ?_⟩
  refine h.tendsto.congr fun n => Subtype.ext ?_
  change μ₂.map (Y n) = μ₁.map (Y n ∘ Φ)
  rw [← hmap, Measure.map_map (hY n) hΦ]

/-- Encoding every positive row of the bootstrap world of `x` gives the bootstrap world of the
encoded data; the unused row zero is sent to `0`.

Adapted from the private `KMBootstrap.map_world_obsVec` to the `(T, d, z)` encoding. -/
private theorem map_world_obsVec (t : Fin k → ℝ) (c : Fin q → ℝ) (x : ℕ → ℝ × ℝ × ℝ) :
    (world x).map (fun ω n m => if n = 0 then (0 : Coord k q) else obsVec t c (ω n m)) =
      world (fun i => obsVec t c (x i)) := by
  have hg : ∀ n : ℕ, Measurable fun o : ℝ × ℝ × ℝ =>
      if n = 0 then (0 : Coord k q) else obsVec t c o :=
    fun n => Measurable.ite (MeasurableSet.const _) measurable_const (measurable_obsVec t c)
  unfold world
  refine (Measure.infinitePi_map_pi
    (μ := fun n => Measure.infinitePi fun _ : ℕ => empirical x n)
    (f := fun n (row : ℕ → ℝ × ℝ × ℝ) m => if n = 0 then (0 : Coord k q) else obsVec t c (row m))
    (fun n => measurable_pi_iff.2 fun m => (hg n).comp (measurable_pi_apply m))).trans ?_
  congr 1; funext n
  rw [Measure.infinitePi_map_pi (fun _ : ℕ => empirical x n)
    (f := fun _ o => if n = 0 then (0 : Coord k q) else obsVec t c o) (fun _ => hg n)]
  congr 1; funext m
  rcases eq_or_ne n 0 with rfl | hn
  · simp [empirical]
  · simp only [hn, ↓reduceIte]
    rw [empirical_of_ne_zero hn, empirical_of_ne_zero hn,
      Measure.map_smul _ (measurable_obsVec t c).aemeasurable,
      Measure.map_finset_sum (measurable_obsVec t c).aemeasurable]
    simp [Measure.map_dirac' (measurable_obsVec t c)]

/-- Conditional consistency of the bootstrap mean: if `√n (x̄*ₙ - x̄ₙ)` converges in distribution
under the bootstrap world, then `x̄*ₙ - x̄ₙ → 0` in probability. -/
theorem tendstoInMeasure_bootMeanVec_sub {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (x : ℕ → E) {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {Z : Ω' → E}
    (h : TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) • (bootMeanVec n ω - sampleMeanVec x n))
      atTop Z (fun _ => world x) μ') :
    TendstoInMeasure (world x) (fun (n : ℕ) ω => bootMeanVec n ω - sampleMeanVec x n) atTop
      (fun _ => 0) := by
  have hsc : TendstoInMeasure (world x) (fun (n : ℕ) (_ : ℕ → ℕ → E) => (√(n : ℝ))⁻¹) atTop
      (fun _ => (0 : ℝ)) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const) (ae_of_all _ fun _ =>
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
  have h2 := h.smul_of_tendstoInMeasure_const hsc fun _ => aemeasurable_const
  have h3 : TendstoInDistribution (fun (n : ℕ) ω => bootMeanVec n ω - sampleMeanVec x n) atTop
      (fun _ => (0 : E)) (fun _ => world x) μ' := by
    refine h2.congr (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun ω => zero_smul _ _)
    rcases eq_or_ne n 0 with rfl | hn
    · simp [bootMeanVec, sampleMeanVec]
    · have hs : (√(n : ℝ)) ≠ 0 := (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn))).ne'
      simp only [smul_smul, inv_mul_cancel₀ hs, one_smul]
  exact tendstoInMeasure_of_tendstoInDistribution_const h3

variable {t : Fin k → ℝ} {c : Fin q → ℝ}

/-- The core transfer: under a chart of the Cox root around the limit `θ` of the encoded sample
means, convergence in distribution of the smooth bootstrap statistic `√n (g(x̄*ₙ) - g(x̄ₙ))` on the
encoded bootstrap world gives the same limit for the bootstrap Cox estimator
`√n (β̂*ₙ - β̂ₙ)` on the bootstrap world of the data. -/
private theorem tendstoInDistribution_coxMPLE_of_chart (ht : Function.Injective t)
    (hc : Function.Injective c) (x : ℕ → ℝ × ℝ × ℝ) (hgrid : ∀ i, (x i).1 ∈ Set.range t)
    (hcov : ∀ i, (x i).2.2 ∈ Set.range c) {θ : Coord k q}
    (hθ : Tendsto (sampleMeanVec fun i => obsVec t c (x i)) atTop (𝓝 θ))
    {g : Coord k q → ℝ} {ε : ℝ} (hε : 0 < ε) (hgm : Measurable g)
    (hchart : ∀ μ, dist μ θ < ε → scoreMap c μ (g μ) = 0 ∧
      ∀ b, dist b (g μ) < ε → scoreMap c μ b = 0 → b = g μ)
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {Z : Ω' → Coord k q} {W : Ω' → ℝ}
    (hmean : TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) •
        (bootMeanVec n ω - sampleMeanVec (fun i => obsVec t c (x i)) n))
      atTop Z (fun _ => world (fun i => obsVec t c (x i))) μ')
    (hdelta : TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) •
        (g (bootMeanVec n ω) - g (sampleMeanVec (fun i => obsVec t c (x i)) n)))
      atTop W (fun _ => world (fun i => obsVec t c (x i))) μ') :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) * (coxMPLE (ω n) n - coxMPLE x n))
      atTop W (fun _ => world x) μ' := by
  classical
  set xe : ℕ → Coord k q := fun i => obsVec t c (x i) with hxe
  set Φ : (ℕ → ℕ → ℝ × ℝ × ℝ) → ℕ → ℕ → Coord k q :=
    fun ω n m => if n = 0 then 0 else obsVec t c (ω n m) with hΦdef
  have hΦ : Measurable Φ := measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun m =>
    Measurable.ite (MeasurableSet.const _) measurable_const
      ((measurable_obsVec t c).comp ((measurable_pi_apply m).comp (measurable_pi_apply n)))
  have hmap : (world x).map Φ = world xe := map_world_obsVec t c x
  -- the smooth statistic, on the bootstrap world of the data
  have hY : ∀ n : ℕ, Measurable fun ω : ℕ → ℕ → Coord k q =>
      √(n : ℝ) • (g (bootMeanVec n ω) - g (sampleMeanVec xe n)) :=
    fun n => by
      have h := ((hgm.comp (measurable_bootMeanVec n)).sub
        (measurable_const (a := g (sampleMeanVec xe n)))).const_smul (√(n : ℝ))
      exact h
  have h1 := tendstoInDistribution_comp_of_map_eq hΦ hmap hY hdelta
  -- the bootstrap mean leaves the chart with vanishing probability
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hθ (ε / 2) (half_pos hε)
  have hfar : Tendsto (fun n : ℕ => world x {ω | ε ≤ dist (bootMeanVec n (Φ ω)) θ}) atTop
      (𝓝 0) := by
    have hc' := (tendstoInMeasure_iff_dist.1 (tendstoInMeasure_bootMeanVec_sub xe hmean))
      (ε / 2) (half_pos hε)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc'
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    have hm : MeasurableSet {ω : ℕ → ℕ → Coord k q |
        ε / 2 ≤ dist (bootMeanVec n ω - sampleMeanVec xe n) 0} :=
      measurableSet_le measurable_const
        (((measurable_bootMeanVec n).sub measurable_const).dist measurable_const)
    rw [← hmap, Measure.map_apply hΦ hm]
    refine measure_mono fun ω hω => ?_
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hω ⊢
    have h := dist_triangle (bootMeanVec n (Φ ω)) (sampleMeanVec xe n) θ
    have hNn := hN n hn
    rw [dist_eq_norm (bootMeanVec n (Φ ω)) (sampleMeanVec xe n)] at h
    rw [dist_zero_right]
    linarith
  -- the data estimator is eventually the chart root of the data mean
  have hdata : ∀ n ≥ max N 1, coxMPLE x n = g (sampleMeanVec xe n) := fun n hn =>
    coxMPLE_eq_of_chart ht hc x (by omega) (fun i _ => hgrid i) (fun i _ => hcov i) hε hchart
      ((hN n (le_of_max_le_left hn)).trans (half_lt_self hε))
  -- the bootstrap estimator is the chart root of the bootstrap mean, inside the chart
  have hS : MeasurableSet {o : ℝ × ℝ × ℝ | o.1 ∈ Set.range t ∧ o.2.2 ∈ Set.range c} :=
    (measurable_fst (Set.finite_range t).measurableSet).inter
      (measurable_snd.snd (Set.finite_range c).measurableSet)
  have hboot : ∀ n ≠ 0, ∀ᵐ ω ∂world x, dist (bootMeanVec n (Φ ω)) θ < ε →
      coxMPLE (ω n) n = g (bootMeanVec n (Φ ω)) := by
    intro n hn
    filter_upwards [KMBootstrap.ae_resample_mem x hS (n := n) fun i _ => ⟨hgrid i, hcov i⟩]
      with ω hω hd
    have heq : bootMeanVec n (Φ ω) = sampleMeanVec (fun i => obsVec t c (ω n i)) n := by
      simp [bootMeanVec, sampleMeanVec, hΦdef, hn]
    rw [heq] at hd ⊢
    exact coxMPLE_eq_of_chart ht hc (ω n) hn (fun i hi => (hω i hi).1) (fun i hi => (hω i hi).2)
      hε hchart hd
  have hdiff : TendstoInMeasure (world x)
      ((fun (n : ℕ) ω => √(n : ℝ) * (coxMPLE (ω n) n - coxMPLE x n)) -
        fun (n : ℕ) ω => √(n : ℝ) • (g (bootMeanVec n (Φ ω)) - g (sampleMeanVec xe n)))
      atTop 0 := by
    rw [tendstoInMeasure_iff_dist]
    intro δ hδ
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hfar
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have hn0 : n ≠ 0 := by omega
    refine measure_mono_ae ?_
    filter_upwards [hboot n hn0] with ω hω hmem
    by_contra hlt
    push Not at hlt
    simp only [Pi.sub_apply, Pi.zero_apply, hω hlt, hdata n hn, smul_eq_mul, sub_self,
      dist_self] at hmem
    linarith
  -- the bootstrap estimator is almost everywhere measurable: the resample is finite-valued
  have hmeasY : ∀ n : ℕ, AEMeasurable (fun ω => √(n : ℝ) * (coxMPLE (ω n) n - coxMPLE x n))
      (world x) := by
    intro n
    have hfin : (Set.pi Set.univ fun _ : Fin n => x '' Set.Iio n).Finite :=
      Set.Finite.pi fun _ => (Set.finite_Iio n).image x
    have hV : Measurable fun (ω : ℕ → ℕ → ℝ × ℝ × ℝ) (i : Fin n) => ω n i :=
      measurable_pi_iff.2 fun i => (measurable_pi_apply (i : ℕ)).comp (measurable_pi_apply n)
    have hmem : ∀ᵐ ω ∂world x, (fun i : Fin n => ω n i) ∈
        Set.pi Set.univ fun _ : Fin n => x '' Set.Iio n := by
      filter_upwards [KMBootstrap.ae_resample_mem x (S := x '' Set.Iio n)
        ((Set.finite_Iio n).image x).measurableSet (n := n) fun i hi => ⟨i, hi, rfl⟩] with ω hω
      exact fun i _ => hω i i.isLt
    exact aemeasurable_comp_of_ae_mem_finite hV.aemeasurable hfin hmem
      fun v => √(n : ℝ) * (mple (coxArrays v) - coxMPLE x n)
  exact tendstoInDistribution_of_tendstoInMeasure_sub _ W h1 hdiff hmeasY

end Transfer

/-! ### Bootstrap validity -/

section Deterministic

variable {t : Fin k → ℝ} {c : Fin q → ℝ}

/-- **Bootstrap validity for the grid Cox estimator, fixed data.** Let the data `x` have every
observed time on the grid `t` and every covariate among the levels `c`, and let `Z` be a random
vector in the indicator space whose projections are `N(0, v s)`. Suppose that, in every direction
`s`, the plug-in variances of the encoded data converge to `v s` and satisfy the Lindeberg
condition, that the encoded sample means converge to `θ`, that every grid time has positive total
at-risk mass under `θ`, that `β₀` is a root of the limiting score `Ψ(θ, ·)` and that the limiting
information `coxInfo c θ β₀` is nonzero. Then, conditionally on the data (under `world x`),
`√n (β̂*ₙ - β̂ₙ)` converges in distribution to `coxLimitMap c θ β₀ Z`. -/
theorem tendstoInDistribution_bootstrap_coxMPLE (ht : Function.Injective t)
    (hc : Function.Injective c) (x : ℕ → ℝ × ℝ × ℝ) (hgrid : ∀ i, (x i).1 ∈ Set.range t)
    (hcov : ∀ i, (x i).2.2 ∈ Set.range c) {Ω' : Type*} [MeasurableSpace Ω']
    {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {Z : Ω' → Coord k q} (hZ : AEMeasurable Z μ')
    (v : Coord k q → ℝ≥0) (hZlaw : ∀ s, HasLaw (fun ω => ⟪Z ω, s⟫) (gaussianReal 0 (v s)) μ')
    (hvar : ∀ s, Tendsto (empiricalVar (fun i => ⟪obsVec t c (x i), s⟫)) atTop (𝓝 (v s)))
    (hLind : ∀ s, ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n,
        if ε * √n < |⟪obsVec t c (x i), s⟫ -
            MathlibExt.Probability.Causality.sampleMean (fun i => ⟪obsVec t c (x i), s⟫) (range n)|
        then (⟪obsVec t c (x i), s⟫ -
            MathlibExt.Probability.Causality.sampleMean (fun i => ⟪obsVec t c (x i), s⟫)
              (range n)) ^ 2
        else 0) atTop (𝓝 0))
    {θ : Coord k q} (hθ : Tendsto (sampleMeanVec fun i => obsVec t c (x i)) atTop (𝓝 θ))
    (hpos : ∀ j, 0 < ∑ a, θ (Sum.inr (j, a))) {β₀ : ℝ} (hroot : scoreMap c θ β₀ = 0)
    (hinfo : coxInfo c θ β₀ ≠ 0) :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) * (coxMPLE (ω n) n - coxMPLE x n))
      atTop (fun ω => coxLimitMap c θ β₀ (Z ω)) (fun _ => world x) μ' := by
  obtain ⟨g, ε, hε, hgm, hg, -, hchart⟩ := exists_rootChart
    (fun j => (riskSum0_pos (nonneg_of_tendsto hθ) hpos β₀ j).ne') hroot hinfo
  exact tendstoInDistribution_coxMPLE_of_chart ht hc x hgrid hcov hθ hε hgm hchart
    (tendstoInDistribution_bootMeanVec _ hZ v hZlaw hvar hLind)
    (tendstoInDistribution_bootstrapVec_of_hasStrictFDerivAt _ hZ v hZlaw hvar hLind hθ hg hgm)

end Deterministic

/-- `(√n)⁻¹ (S - n θ) = √n (S / n - θ)`, including `n = 0`.

Copy of the private `KMBootstrap.inv_sqrt_smul_sum_sub_eq`. -/
private theorem inv_sqrt_smul_sum_sub_eq {E : Type*} [AddCommGroup E] [Module ℝ E] (S θ : E)
    (n : ℕ) : (√(n : ℝ))⁻¹ • (S - n • θ) = √(n : ℝ) • ((n : ℝ)⁻¹ • S - θ) := by
  have h1 : (√(n : ℝ))⁻¹ = √(n : ℝ) * (n : ℝ)⁻¹ := by
    rw [← div_eq_mul_inv, Real.sqrt_div_self', one_div]
  have h2 : (√(n : ℝ))⁻¹ * (n : ℝ) = √(n : ℝ) := by
    rw [← div_eq_inv_mul, Real.div_sqrt]
  rw [smul_sub, smul_sub, smul_smul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, h2, h1]

section IID

variable {t : Fin k → ℝ} {c : Fin q → ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Bootstrap consistency for the grid Cox estimator.** Let `X 0, X 1, …` be iid observations
whose observed times lie almost surely on the grid `t` and whose covariates lie almost surely
among the levels `c`; let `θ = E[obsVec t c (X 0)]`, assume every grid time has positive at-risk
probability, that `β₀` is a root of the limiting score `Ψ(θ, ·)` and that the limiting
information is nonzero. Let `Z` be a centred Gaussian vector with the covariance of
`obsVec t c (X 0)` and `L = coxLimitMap c θ β₀`. Then

* the Cox estimator satisfies `√n (β̂ₙ - β₀) ⇒ L Z`;
* for almost every data sequence, the conditional law of `√n (β̂*ₙ - β̂ₙ)` given the data
  converges to the same limit `L Z`. -/
theorem coxMPLE_bootstrap_consistent (ht : Function.Injective t) (hc : Function.Injective c)
    (X : ℕ → Ω → ℝ × ℝ × ℝ) (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hgrid : ∀ i, ∀ᵐ ω ∂P, (X i ω).1 ∈ Set.range t)
    (hcov : ∀ i, ∀ᵐ ω ∂P, (X i ω).2.2 ∈ Set.range c)
    (hpos : ∀ j, 0 < ∑ a, (∫ ω, obsVec t c (X 0 ω) ∂P) (Sum.inr (j, a)))
    {β₀ : ℝ} (hroot : scoreMap c (∫ ω, obsVec t c (X 0 ω) ∂P) β₀ = 0)
    (hinfo : coxInfo c (∫ ω, obsVec t c (X 0 ω) ∂P) β₀ ≠ 0)
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {Z : Ω' → Coord k q} (hZ : AEMeasurable Z μ')
    (hZlaw : ∀ s, HasLaw (fun ω => ⟪Z ω, s⟫)
      (gaussianReal 0 (Var[fun ω => ⟪obsVec t c (X 0 ω), s⟫; P]).toNNReal) μ') :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) * (coxMPLE (fun i => X i ω) n - β₀))
        atTop (fun ω => coxLimitMap c (∫ ω, obsVec t c (X 0 ω) ∂P) β₀ (Z ω)) (fun _ => P) μ' ∧
      ∀ᵐ ω ∂P, TendstoInDistribution
        (fun (n : ℕ) ω' => √(n : ℝ) * (coxMPLE (ω' n) n - coxMPLE (fun i => X i ω) n))
        atTop (fun ω' => coxLimitMap c (∫ ω, obsVec t c (X 0 ω) ∂P) β₀ (Z ω'))
        (fun _ => world (fun i => X i ω)) μ' := by
  classical
  set θ := ∫ ω, obsVec t c (X 0 ω) ∂P with hθdef
  have hYm : ∀ i, AEMeasurable (fun ω => obsVec t c (X i ω)) P := fun i =>
    (measurable_obsVec t c).comp_aemeasurable (hident i).aemeasurable_fst
  have hmem : MemLp (fun ω => obsVec t c (X 0 ω)) 2 P :=
    MemLp.of_bound (hYm 0).aestronglyMeasurable _ (ae_of_all _ fun ω => norm_obsVec_le t c _)
  have hindep' : iIndepFun (fun i ω => obsVec t c (X i ω)) P :=
    hindep.comp (fun _ => obsVec t c) fun _ => measurable_obsVec t c
  have hident' : ∀ i, IdentDistrib (fun ω => obsVec t c (X i ω)) (fun ω => obsVec t c (X 0 ω))
      P P := fun i => (hident i).comp (measurable_obsVec t c)
  have hslln : ∀ᵐ ω ∂P, Tendsto (sampleMeanVec fun i => obsVec t c (X i ω)) atTop (𝓝 θ) :=
    strong_law_ae (fun i ω => obsVec t c (X i ω)) (hmem.integrable one_le_two)
      (fun _ _ hij => hindep'.indepFun hij) hident'
  obtain ⟨ω₀, hω₀⟩ := hslln.exists
  obtain ⟨g, ε, hε, hgm, hg, hgθ, hchart⟩ := exists_rootChart
    (fun j => (riskSum0_pos (nonneg_of_tendsto hω₀) hpos β₀ j).ne') hroot hinfo
  have hgridω : ∀ᵐ ω ∂P, ∀ i, (X i ω).1 ∈ Set.range t := ae_all_iff.2 hgrid
  have hcovω : ∀ᵐ ω ∂P, ∀ i, (X i ω).2.2 ∈ Set.range c := ae_all_iff.2 hcov
  refine ⟨?_, ?_⟩
  · -- sampling law: multivariate CLT, the delta method for the chart root, then the chart
    have hclt := tendstoInDistribution_inv_sqrt_smul_sum_sub
      (X := fun i ω => obsVec t c (X i ω)) hZ hZlaw hmem hindep' hident'
    have hclt' : TendstoInDistribution
        (fun (n : ℕ) ω => √(n : ℝ) • (sampleMeanVec (fun i => obsVec t c (X i ω)) n - θ))
        atTop Z (fun _ => P) μ' :=
      hclt.congr (fun n => ae_of_all _ fun ω => inv_sqrt_smul_sum_sub_eq _ _ n)
        (ae_of_all _ fun _ => rfl)
    have hmeanm : ∀ n : ℕ, AEMeasurable
        (fun ω => sampleMeanVec (fun i => obsVec t c (X i ω)) n) P := fun n => by
      have h := (Finset.aemeasurable_fun_sum (range n) fun i _ => hYm i).const_smul ((n : ℝ)⁻¹)
      exact h
    have hdelta := TendstoInDistribution.delta_method_of_hasStrictFDerivAt hclt'
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop) tendsto_const_nhds hg
      hmeanm (fun n => hgm.comp_aemeasurable (hmeanm n))
    rw [hgθ] at hdelta
    have hfar := (tendstoInMeasure_iff_dist.1 (tendstoInMeasure_of_tendsto_ae
      (fun n => (hmeanm n).aestronglyMeasurable) hslln)) ε hε
    have hdiff : TendstoInMeasure P
        ((fun (n : ℕ) ω => √(n : ℝ) * (coxMPLE (fun i => X i ω) n - β₀)) -
          fun (n : ℕ) ω => √(n : ℝ) • (g (sampleMeanVec (fun i => obsVec t c (X i ω)) n) - β₀))
        atTop 0 := by
      rw [tendstoInMeasure_iff_dist]
      intro δ hδ
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hfar
        (Eventually.of_forall fun _ => zero_le) ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      refine measure_mono_ae ?_
      filter_upwards [hgridω, hcovω] with ω hgω hcω hmem'
      by_contra hlt
      push Not at hlt
      simp only [Pi.sub_apply, Pi.zero_apply, coxMPLE_eq_of_chart ht hc (fun i => X i ω)
        (by omega) (fun i _ => hgω i) (fun i _ => hcω i) hε hchart hlt, smul_eq_mul, sub_self,
        dist_self] at hmem'
      linarith
    have hmeasY : ∀ n : ℕ, AEMeasurable
        (fun ω => √(n : ℝ) * (coxMPLE (fun i => X i ω) n - β₀)) P := by
      intro n
      have hfin : ((Set.pi Set.univ fun _ : Fin n => Set.range t) ×ˢ
          ((Set.univ : Set (Fin n → Bool)) ×ˢ
            (Set.pi Set.univ fun _ : Fin n => Set.range c))).Finite :=
        (Set.Finite.pi fun _ => Set.finite_range t).prod
          (Set.finite_univ.prod (Set.Finite.pi fun _ => Set.finite_range c))
      have hV : AEMeasurable (fun ω => coxArrays fun i : Fin n => X i ω) P :=
        (measurable_coxArrays n).comp_aemeasurable
          (AEMeasurable.of_eval fun i => (hident i).aemeasurable_fst)
      have hmemA : ∀ᵐ ω ∂P, (coxArrays fun i : Fin n => X i ω) ∈
          (Set.pi Set.univ fun _ : Fin n => Set.range t) ×ˢ
            ((Set.univ : Set (Fin n → Bool)) ×ˢ
              (Set.pi Set.univ fun _ : Fin n => Set.range c)) := by
        filter_upwards [hgridω, hcovω] with ω hgω hcω
        simp [coxArrays, Set.mem_prod, Set.mem_pi, hgω, hcω]
      exact aemeasurable_comp_of_ae_mem_finite hV hfin hmemA fun D => √(n : ℝ) * (mple D - β₀)
    exact tendstoInDistribution_of_tendstoInMeasure_sub _ _ hdelta hdiff hmeasY
  · -- bootstrap law: almost-sure bootstrap CLT and delta method, then the transfer
    filter_upwards [ae_tendstoInDistribution_bootMeanVec (fun i ω => obsVec t c (X i ω)) hmem
        (fun _ _ hij => hindep'.indepFun hij) hident' hZ hZlaw,
      ae_tendstoInDistribution_bootstrapVec_of_hasStrictFDerivAt (fun i ω => obsVec t c (X i ω))
        hmem (fun _ _ hij => hindep'.indepFun hij) hident' hZ hZlaw hg hgm,
      hslln, hgridω, hcovω] with ω h1 h2 h3 h4 h5
    exact tendstoInDistribution_coxMPLE_of_chart ht hc (fun i => X i ω) h4 h5 h3 hε hgm hchart
      h1 h2

end IID

end MathlibExt.Probability.Statistics.CoxBootstrap
