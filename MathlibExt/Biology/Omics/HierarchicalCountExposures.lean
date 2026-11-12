/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Omics.HierarchicalCount
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.HasLaw

import MathlibExt.Probability.Distributions.GammaMoments
import MathlibExt.Probability.Distributions.PoissonKernel
import MathlibExt.Probability.PairwiseIndepSLLN

/-!
# Pooled Gamma–Poisson counts with different exposures: posterior consistency

One gene has rate `λ ~ Gamma(a, b)` shared by cells `i` with size factors (exposures) `sᵢ`, and
the cell counts are conditionally independent, `kᵢ ∣ λ ~ Po(sᵢ λ)`, the hierarchy of
`MathlibExt.Biology.Omics.HierarchicalCount`. The pooled posterior is `Gamma(a + K, b + S)` with
`K = ∑ᵢ kᵢ` and `S = ∑ᵢ sᵢ`. This file proves that the pooled posterior is consistent, almost
surely, when the exposures differ from cell to cell. The cell counts are then not identically
distributed, so the i.i.d. strong law does not give `K / S → r₀`; a strong law for
non-identically distributed nonnegative variables is proved here for that purpose.

## Source

* Pooled posterior with exposures: A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson,
  A. Vehtari, D. B. Rubin, *Bayesian Data Analysis*, 3rd ed., CRC Press (2013), §2.6, "Poisson
  model parameterized in terms of rate and exposure": for `yᵢ ∼ Po(xᵢ θ)` and
  `θ ∼ Gamma(α, β)`, the posterior is `θ ∣ y ∼ Gamma(α + ∑ᵢ yᵢ, β + ∑ᵢ xᵢ)`
  (`pooledPosterior_eq_gammaPDFReal`).
* Posterior consistency: the same book, Appendix B (large-sample theory): the posterior
  concentrates at the true parameter as data accumulate (`tendsto_pooledPosterior_of_tendsto`,
  `ae_tendsto_pooledPosterior_exposures`, `ae_tendsto_pooledPosterior_poisson`).
* Strong law: the subsequence-and-bracketing argument for nonnegative pairwise independent
  variables of N. Etemadi, *On the laws of large numbers for nonnegative random variables*,
  J. Multivariate Anal. 13 (1983), 187–193; here with the hypotheses `Var Yᵢ ≤ C E Yᵢ` and
  `E Yᵢ ≤ B` and normalization by `E ∑_{i<n} Yᵢ` (`ae_tendsto_sum_div_sum_integral`).

## Main results

* `prod_poissonExposureLik`: the joint likelihood factors as a rate-free constant times
  `r^K e^{-S r}`.
* `pooledPosterior_eq_gammaPDFReal`: **pooled conjugacy with exposures.** The posterior is
  `Gamma(a + ∑ᵢ kᵢ, b + ∑ᵢ sᵢ)`.
* `tendsto_pooledPosterior_of_tendsto`: **deterministic core.** If `S → ∞` and `K / S → r₀`, the
  posterior mean tends to `r₀`, the posterior variance to `0`, and the posterior mass outside
  every neighbourhood of `r₀` to `0`.
* `ae_tendsto_sum_div_sum_integral`: **strong law for different means.** Pairwise independent,
  nonnegative, square-integrable `Yᵢ` with bounded means, `Var Yᵢ ≤ C E Yᵢ` and divergent total
  mean satisfy `∑_{i<n} Yᵢ / E ∑_{i<n} Yᵢ → 1` a.s.
* `ae_tendsto_pooledPosterior_exposures`: **a.s. posterior consistency with exposures.** For
  pairwise independent counts with `E Xᵢ = sᵢ r₀`, `Var Xᵢ ≤ C sᵢ`, bounded exposures and
  `∑ sᵢ = ∞`, the conclusions of the deterministic core hold almost surely.
* `ae_tendsto_pooledPosterior_poisson`: the same for `Xᵢ ∼ Po(sᵢ r₀)`.

## Implementation notes

The pooled posterior is restated without new definitions, as the product of the one-cell
likelihoods `HierarchicalCount.poissonExposureLik`; its mean and variance are
`HierarchicalCount.integral_id_posterior` and `HierarchicalCount.variance_posterior` at count
`K` and exposure `S`. `HierarchicalCountPooled` (PR #1608, open) is not imported, and two results
here overlap it: `pooledPosterior_eq_gammaPDFReal` duplicates
`HierarchicalCountPooled.pooledPosterior_eq_gammaPDFReal` (same name, sibling namespace), and
`tendsto_pooledPosterior_of_tendsto` is #1608's `tendsto_posteriorMean_of_tendsto` plus the
concentration conclusion. Follow-up: after #1608 merges, derive both from #1608's versions and
remove the duplicate names. The new content with exposures is the strong law and the two a.s.
theorems.

`ae_tendsto_sum_div_sum_integral` and its private helpers `exists_subseq_ratio` and
`tendsto_div_of_subseq` are pure probability results, candidates to move to
`MathlibExt/Probability` next to `PairwiseIndepSLLN`; the indicator law
`ProbabilityTheory.pairwise_indep_slln` is the special case with variance at most mean and means
at most `1`.

Reuse (search of Mathlib, `MathlibExt`, `CSLibExt` and `WantedExt` on 2026-11-12 for strong
laws, Kronecker/Kolmogorov criteria and Poisson moments): Mathlib's
`ProbabilityTheory.strong_law_ae` needs identically distributed variables, and
`ProbabilityTheory.pairwise_indep_slln` covers indicators only; no strong law for
non-identically distributed real variables existed. Reused: `pairwise_indep_slln`'s helper
`ProbabilityTheory.ae_tendsto_of_ae_eventually_abs_sub_lt`, Mathlib's Chebyshev inequality
`ProbabilityTheory.meas_ge_le_variance_div_sq`, `ProbabilityTheory.IndepFun.variance_sum`, the
Borel–Cantelli lemma `MeasureTheory.ae_eventually_notMem`, the Gamma moments
`ProbabilityTheory.memLp_id_gammaMeasure`, and the Poisson moments
`ProbabilityTheory.integral_natCast_poissonMeasure` and
`ProbabilityTheory.variance_natCast_poissonMeasure`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology Function
open scoped Nat NNReal
open MathlibExt.Biology.Omics.HierarchicalCount

namespace MathlibExt.Biology.Omics.HierarchicalCountExposures


variable {ι : Type*} [Fintype ι]

/-! ### The pooled posterior with per-cell exposures -/

/-- **Factorization of the joint likelihood.** For cells `i` with size factors `sᵢ` and counts
`kᵢ`, `∏ᵢ e^{-sᵢ r} (sᵢ r)^{kᵢ} / kᵢ! = (∏ᵢ sᵢ^{kᵢ} / kᵢ!) · r^K e^{-S r}` with `K = ∑ᵢ kᵢ`
and `S = ∑ᵢ sᵢ`: the dependence on the rate is through `(K, S)` only. -/
theorem prod_poissonExposureLik (s : ι → ℝ) (k : ι → ℕ) (r : ℝ) :
    ∏ i, poissonExposureLik (s i) (k i) r =
      (∏ i, s i ^ k i / (k i)!) * (r ^ (∑ i, k i) * exp (-((∑ i, s i) * r))) := by
  have h : ∀ i, poissonExposureLik (s i) (k i) r =
      s i ^ k i / (k i)! * (r ^ k i * exp (-(s i * r))) := fun i => by
    rw [poissonExposureLik, mul_pow]; ring
  simp_rw [h, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← Real.exp_sum,
    Finset.sum_mul, ← Finset.sum_neg_distrib]

/-- **Pooled Gamma–Poisson conjugacy with different exposures.** With prior `λ ~ Gamma(a, b)`
(`a, b > 0`) and conditionally independent cell counts `kᵢ ~ Po(sᵢ λ)` with size factors
`sᵢ > 0`, the posterior density (joint likelihood times prior density over
the joint marginal likelihood) is the `Gamma(a + ∑ᵢ kᵢ, b + ∑ᵢ sᵢ)` density: the one-cell
posterior `HierarchicalCount.posterior_eq_gammaPDFReal` at count `K = ∑ᵢ kᵢ` and exposure
`S = ∑ᵢ sᵢ`. Its mean `(a + K) / (b + S)` and variance `(a + K) / (b + S)²` are then
`HierarchicalCount.integral_id_posterior` and `HierarchicalCount.variance_posterior`. -/
theorem pooledPosterior_eq_gammaPDFReal {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {s : ι → ℝ} (hs : ∀ i, 0 < s i) (k : ι → ℕ) (r : ℝ) :
    (∏ i, poissonExposureLik (s i) (k i) r) * gammaPDFReal a b r /
        (∫ x, ∏ i, poissonExposureLik (s i) (k i) x ∂gammaMeasure a b) =
      gammaPDFReal (a + (∑ i, k i : ℕ)) (b + ∑ i, s i) r := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have := isProbabilityMeasure_gammaMeasure ha hb
    simp [Finset.univ_eq_empty]
  set K := ∑ i, k i
  set S := ∑ i, s i
  have hS : 0 < S := Finset.sum_pos (fun i _ => hs i) Finset.univ_nonempty
  have hc : (∏ i, s i ^ k i / (k i)!) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ =>
    div_ne_zero (pow_ne_zero _ (hs i).ne') (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
  have hd : S ^ K / (K)! ≠ 0 :=
    div_ne_zero (pow_ne_zero _ hS.ne') (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
  have h1 : ∀ x, poissonExposureLik S K x = S ^ K / (K)! * (x ^ K * exp (-(S * x))) :=
    fun x => by rw [poissonExposureLik, mul_pow]; ring
  have hone := posterior_eq_gammaPDFReal ha hb hS K r
  rw [marginalLik] at hone
  simp_rw [h1] at hone
  rw [integral_const_mul, mul_assoc, mul_div_mul_left _ _ hd] at hone
  simp_rw [prod_poissonExposureLik]
  rw [integral_const_mul, mul_assoc, mul_div_mul_left _ _ hc]
  exact hone

/-! ### Posterior consistency: deterministic core -/

/-- **Posterior consistency, deterministic core.** Along any filter, if the pooled exposure
`S → ∞` and the pooled rate `K / S → r₀`, then for a prior `Gamma(a, b)` with `a, b > 0` the
pooled posterior `Gamma(a + K, b + S)` has mean `(a + K) / (b + S) → r₀`, variance
`(a + K) / (b + S)² → 0`, and assigns vanishing mass to the complement of every neighbourhood
`(r₀ - ε, r₀ + ε)` of `r₀`: the posterior concentrates at `r₀`. -/
theorem tendsto_pooledPosterior_of_tendsto {α : Type*} {l : Filter α} {a b r₀ : ℝ}
    (ha : 0 < a) (hb : 0 < b) {S : α → ℝ} {K : α → ℕ} (hS : Tendsto S l atTop)
    (hK : Tendsto (fun i => (K i : ℝ) / S i) l (𝓝 r₀)) :
    Tendsto (fun i => posteriorMean a b (S i) (K i)) l (𝓝 r₀) ∧
      Tendsto (fun i => (a + K i) / (b + S i) ^ 2) l (𝓝 0) ∧
      ∀ ε : ℝ, 0 < ε →
        Tendsto (fun i => gammaMeasure (a + K i) (b + S i) {x | ε ≤ |x - r₀|}) l (𝓝 0) := by
  have h0 : ∀ c : ℝ, Tendsto (fun i => c / S i) l (𝓝 0) := fun c =>
    tendsto_const_nhds.div_atTop hS
  have hmean : Tendsto (fun i => posteriorMean a b (S i) (K i)) l (𝓝 r₀) := by
    have h := ((h0 a).add hK).div ((h0 b).add tendsto_const_nhds) (by norm_num : (0 : ℝ) + 1 ≠ 0)
    rw [zero_add, zero_add, div_one] at h
    refine h.congr' ?_
    filter_upwards [hS.eventually_gt_atTop 0] with i hi
    change (a / S i + K i / S i) / (b / S i + 1) = (a + K i) / (b + S i)
    rw [← add_div, div_add_one hi.ne', div_div_div_cancel_right₀ hi.ne']
  have hvar : Tendsto (fun i => (a + K i) / (b + S i) ^ 2) l (𝓝 0) := by
    have hinv : Tendsto (fun i => (b + S i)⁻¹) l (𝓝 0) :=
      (tendsto_atTop_add_const_left l b hS).inv_tendsto_atTop
    have h := hmean.mul hinv
    rw [mul_zero] at h
    refine h.congr' (Eventually.of_forall fun i => ?_)
    change (a + K i) / (b + S i) * (b + S i)⁻¹ = (a + K i) / (b + S i) ^ 2
    rw [sq, ← div_div]
    exact (div_eq_mul_inv _ _).symm
  refine ⟨hmean, hvar, fun ε hε => ?_⟩
  have hε2 : 0 < ε / 2 := by linarith
  have hup : Tendsto (fun i => ENNReal.ofReal ((a + K i) / (b + S i) ^ 2 / (ε / 2) ^ 2)) l
      (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (hvar.div_const ((ε / 2) ^ 2))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hS.eventually_ge_atTop 0, (Metric.tendsto_nhds.1 hmean) _ hε2] with i hSi hmi
  have haK : 0 < a + K i := by positivity
  have hbS : 0 < b + S i := by linarith
  have := isProbabilityMeasure_gammaMeasure haK hbS
  have hsub : {x : ℝ | ε ≤ |x - r₀|} ⊆
      {x | ε / 2 ≤ |id x - ∫ y, id y ∂gammaMeasure (a + K i) (b + S i)|} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, id] at hx ⊢
    rw [integral_id_posterior ha hb hSi]
    rw [Real.dist_eq] at hmi
    have := abs_sub_abs_le_abs_sub (x - r₀) (x - posteriorMean a b (S i) (K i))
    have h2 : x - r₀ - (x - posteriorMean a b (S i) (K i)) =
        posteriorMean a b (S i) (K i) - r₀ := by ring
    rw [h2] at this
    linarith
  refine (measure_mono hsub).trans ?_
  have := meas_ge_le_variance_div_sq (μ := gammaMeasure (a + K i) (b + S i))
    (memLp_id_gammaMeasure haK hbS) hε2
  rwa [variance_posterior ha hb hSi] at this

/-! ### A strong law for independent counts with different means -/

/-- Deterministic subsequence for the ratio strong law: if `M` starts at `0`, is monotone with
increments at most `B` and tends to `∞`, there is a strictly increasing `σ` with
`(k + 1)² ≤ M (σ k)` along which consecutive ratios `M (σ (k + 1)) / M (σ k)` tend to `1`. -/
private lemma exists_subseq_ratio {M : ℕ → ℝ} {B : ℝ} (hM0 : M 0 = 0) (hmono : Monotone M)
    (hstep : ∀ n, M (n + 1) ≤ M n + B) (htop : Tendsto M atTop atTop) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ (∀ k : ℕ, ((k : ℝ) + 1) ^ 2 ≤ M (σ k)) ∧
      Tendsto (fun k => M (σ (k + 1)) / M (σ k)) atTop (𝓝 1) := by
  set c := |B| + 1 with hc
  have hc1 : 1 ≤ c := by have := abs_nonneg B; linarith
  have hex : ∀ k : ℕ, ∃ n, ((k : ℝ) + c) ^ 2 ≤ M n := fun k =>
    (htop.eventually_ge_atTop _).exists
  classical
  let σ : ℕ → ℕ := fun k => Nat.find (hex k)
  have hkc : ∀ k : ℕ, 0 < (k : ℝ) + c := fun k => by
    have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hlow : ∀ k : ℕ, ((k : ℝ) + c) ^ 2 ≤ M (σ k) := fun k => Nat.find_spec (hex k)
  have hup : ∀ k : ℕ, M (σ k) ≤ ((k : ℝ) + c) ^ 2 + B := by
    intro k
    have hpos : σ k ≠ 0 := by
      intro h0
      have := hlow k
      rw [h0, hM0] at this
      linarith [pow_pos (hkc k) 2]
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hpos
    have hmin : ¬ ((k : ℝ) + c) ^ 2 ≤ M j := Nat.find_min (hex k)
      (show j < Nat.find (hex k) by have : Nat.find (hex k) = j + 1 := hj; omega)
    rw [hj]
    linarith [hstep j, not_le.1 hmin]
  have hMpos : ∀ k, 0 < M (σ k) := fun k => lt_of_lt_of_le (pow_pos (hkc k) 2) (hlow k)
  have hσ : StrictMono σ := by
    refine strictMono_nat_of_lt_succ fun k => ?_
    by_contra h
    have h1 := hmono (not_lt.1 h)
    have h2 := hlow (k + 1)
    have h3 := hup k
    have hB : B < 2 * ((k : ℝ) + c) + 1 := by
      have := le_abs_self B; have := Nat.cast_nonneg (α := ℝ) k; linarith
    push_cast at h2
    have e : ((k : ℝ) + 1 + c) ^ 2 = ((k : ℝ) + c) ^ 2 + (2 * ((k : ℝ) + c) + 1) := by ring
    linarith
  refine ⟨σ, hσ, fun k => le_trans ?_ (hlow k), ?_⟩
  · have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  set u : ℕ → ℝ := fun k => 1 / ((k : ℝ) + c)
  have hu : Tendsto u atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ c tendsto_natCast_atTop_atTop)
  have hlim : Tendsto (fun k => (1 + u k) ^ 2 + B * u k ^ 2) atTop (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).add hu).pow 2 |>.add
      ((tendsto_const_nhds (x := B)).mul (hu.pow 2))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun k => ?_)
    (fun k => ?_)
  · exact (one_le_div (hMpos k)).2 (hmono (hσ.monotone (Nat.le_succ k)))
  · have h1 := hup (k + 1)
    have hk0 := hkc k
    push_cast at h1
    rw [div_le_iff₀ (hMpos k)]
    have h2 : ((1 + u k) ^ 2 + B * u k ^ 2) * ((k : ℝ) + c) ^ 2 =
        ((k : ℝ) + 1 + c) ^ 2 + B := by
      simp only [u]; field_simp; ring
    have h3 : (0 : ℝ) ≤ (1 + u k) ^ 2 + B * u k ^ 2 := by
      have hu0 : 0 ≤ u k := (one_div_pos.2 (hkc k)).le
      have : 0 ≤ (1 + u k) ^ 2 + B * u k ^ 2 - 1 := by
        have e : (1 + u k) ^ 2 + B * u k ^ 2 - 1 = u k * (2 + (1 + B) * u k) := by ring
        rw [e]
        refine mul_nonneg hu0 ?_
        have hBc : -B ≤ |B| := neg_le_abs B
        have huc : u k * ((k : ℝ) + c) = 1 := by simp only [u]; field_simp
        nlinarith [Nat.cast_nonneg (α := ℝ) k]
      linarith
    calc M (σ (k + 1)) ≤ ((k : ℝ) + 1 + c) ^ 2 + B := h1
      _ = ((1 + u k) ^ 2 + B * u k ^ 2) * ((k : ℝ) + c) ^ 2 := h2.symm
      _ ≤ ((1 + u k) ^ 2 + B * u k ^ 2) * M (σ k) := mul_le_mul_of_nonneg_left (hlow k) h3

/-- Deterministic bracketing: for nonnegative monotone `T` and monotone `M`, convergence of
`T / M` to `1` along a strictly increasing `σ` with consecutive ratios of `M ∘ σ` tending to `1`
gives convergence along the whole sequence. -/
private lemma tendsto_div_of_subseq {T M : ℕ → ℝ} {σ : ℕ → ℕ} (hT0 : ∀ n, 0 ≤ T n)
    (hTmono : Monotone T) (hMmono : Monotone M) (hσ : StrictMono σ) (hMpos : ∀ k, 0 < M (σ k))
    (hsub : Tendsto (fun k => T (σ k) / M (σ k)) atTop (𝓝 1))
    (hratio : Tendsto (fun k => M (σ (k + 1)) / M (σ k)) atTop (𝓝 1)) :
    Tendsto (fun n => T n / M n) atTop (𝓝 1) := by
  classical
  let κ : ℕ → ℕ := fun n => Nat.findGreatest (fun k => σ k ≤ n) n
  have hκ1 : ∀ n, σ 0 ≤ n → σ (κ n) ≤ n := fun n hn =>
    Nat.findGreatest_spec (P := fun k => σ k ≤ n) (Nat.zero_le n) hn
  have hκ2 : ∀ n, n < σ (κ n + 1) := fun n => by
    by_contra h
    have h' : σ (κ n + 1) ≤ n := not_lt.1 h
    have : κ n + 1 ≤ κ n := Nat.le_findGreatest (P := fun k => σ k ≤ n) ((hσ.id_le _).trans h') h'
    omega
  have hκ : Tendsto κ atTop atTop := tendsto_atTop.2 fun K => eventually_atTop.2
    ⟨σ K, fun n hn => Nat.le_findGreatest (P := fun k => σ k ≤ n) ((hσ.id_le K).trans hn) hn⟩
  have hL : Tendsto (fun k => T (σ k) / M (σ k) * (M (σ (k + 1)) / M (σ k))⁻¹) atTop (𝓝 1) := by
    simpa using hsub.mul (hratio.inv₀ one_ne_zero)
  have hU : Tendsto (fun k => T (σ (k + 1)) / M (σ (k + 1)) * (M (σ (k + 1)) / M (σ k))) atTop
      (𝓝 1) := by
    simpa using ((tendsto_add_atTop_iff_nat 1).2 hsub).mul hratio
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hL.comp hκ) (hU.comp hκ) ?_ ?_
  · filter_upwards [eventually_ge_atTop (σ 0)] with n hn
    have h1 := hκ1 n hn
    have hk := hMpos (κ n)
    have hk1 := hMpos (κ n + 1)
    have hMn : M (σ (κ n)) ≤ M n := hMmono h1
    have hMn' : M n ≤ M (σ (κ n + 1)) := hMmono (hκ2 n).le
    have e : T (σ (κ n)) / M (σ (κ n)) * (M (σ (κ n + 1)) / M (σ (κ n)))⁻¹ =
        T (σ (κ n)) / M (σ (κ n + 1)) := by field_simp
    simp only [Function.comp]
    rw [e]
    exact div_le_div₀ (hT0 n) (hTmono h1) (hk.trans_le hMn) hMn'
  · filter_upwards [eventually_ge_atTop (σ 0)] with n hn
    have h1 := hκ1 n hn
    have hk := hMpos (κ n)
    have hk1 := hMpos (κ n + 1)
    have hMn : M (σ (κ n)) ≤ M n := hMmono h1
    have e : T (σ (κ n + 1)) / M (σ (κ n + 1)) * (M (σ (κ n + 1)) / M (σ (κ n))) =
        T (σ (κ n + 1)) / M (σ (κ n)) := by field_simp
    simp only [Function.comp]
    rw [e]
    exact div_le_div₀ (hT0 _) (hTmono (hκ2 n).le) hk hMn

section SLLN

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Strong law for nonnegative, non-identically distributed variables.** Let `Y₀, Y₁, …` be
pairwise independent, a.e. nonnegative, square-integrable real random variables whose means
`mᵢ = E Yᵢ` are bounded by `B`, whose variances satisfy `Var Yᵢ ≤ C mᵢ`, and whose total mean
`Mₙ = ∑_{i<n} mᵢ` diverges. Then almost surely `(∑_{i<n} Yᵢ) / Mₙ → 1`.

For Poisson counts `Yᵢ ~ Po(mᵢ)` the variance hypothesis holds with `C = 1`. The proof is the
Chebyshev–Borel–Cantelli argument along a subsequence with `M_{σ(k)} ≈ k²`, followed by
bracketing, as in `ProbabilityTheory.pairwise_indep_slln` (the indicator case, `C = B = 1`).
This is a pure probability result, a candidate to move to `MathlibExt/Probability` next to
`PairwiseIndepSLLN` together with its two private helpers. -/
theorem ae_tendsto_sum_div_sum_integral {Y : ℕ → Ω → ℝ} {B C : ℝ}
    (hL2 : ∀ i, MemLp (Y i) 2 μ) (hnonneg : ∀ i, 0 ≤ᵐ[μ] Y i)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on Y)) (hbdd : ∀ i, μ[Y i] ≤ B)
    (hvar : ∀ i, Var[Y i; μ] ≤ C * μ[Y i])
    (htop : Tendsto (fun n => ∑ i ∈ Finset.range n, μ[Y i]) atTop atTop) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => (∑ i ∈ Finset.range n, Y i ω) / ∑ i ∈ Finset.range n, μ[Y i])
      atTop (𝓝 1) := by
  set M : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, μ[Y i] with hMdef
  have hm0 : ∀ i, 0 ≤ μ[Y i] := fun i => integral_nonneg_of_ae (hnonneg i)
  have hMmono : Monotone M := fun m n hmn =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn) fun i _ _ => hm0 i
  have hstep : ∀ n, M (n + 1) ≤ M n + B := fun n => by
    simp only [M, Finset.sum_range_succ]; linarith [hbdd n]
  obtain ⟨σ, hσ, hlow, hratio⟩ := exists_subseq_ratio (by simp [M]) hMmono hstep htop
  have hMpos : ∀ k, 0 < M (σ k) := fun k => lt_of_lt_of_le (by positivity) (hlow k)
  -- Chebyshev along the subsequence
  have hcheb : ∀ ε : ℝ, 0 < ε → ∀ k, μ {ω | ε ≤ |(∑ i ∈ Finset.range (σ k), Y i ω) / M (σ k) - 1|}
      ≤ ENNReal.ofReal (|C| / (ε ^ 2 * ((k : ℝ) + 1) ^ 2)) := by
    intro ε hε k
    set Tf : Ω → ℝ := ∑ i ∈ Finset.range (σ k), Y i with hTf
    have hTfω : ∀ ω, Tf ω = ∑ i ∈ Finset.range (σ k), Y i ω := fun ω => Finset.sum_apply _ _ _
    have hmem : MemLp Tf 2 μ := memLp_finsetSum' _ fun i _ => hL2 i
    have hint : μ[Tf] = M (σ k) := by
      simp only [hTfω]; exact integral_finsetSum _ fun i _ => (hL2 i).integrable one_le_two
    have hvarT : Var[Tf; μ] ≤ C * M (σ k) := by
      rw [IndepFun.variance_sum (fun i _ => hL2 i) (fun i _ j _ hij => hindep hij),
        show M (σ k) = ∑ i ∈ Finset.range (σ k), μ[Y i] from rfl, Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => hvar i
    have hMk := hMpos k
    have hsub : {ω | ε ≤ |(∑ i ∈ Finset.range (σ k), Y i ω) / M (σ k) - 1|} ⊆
        {ω | ε * M (σ k) ≤ |Tf ω - μ[Tf]|} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      rw [hint, hTfω]
      rw [div_sub_one hMk.ne', abs_div, abs_of_pos hMk, le_div_iff₀ hMk] at hω
      exact hω
    refine (measure_mono hsub).trans ((meas_ge_le_variance_div_sq hmem (by positivity)).trans ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    have hk1 : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
    calc Var[Tf; μ] / (ε * M (σ k)) ^ 2 ≤ |C| * M (σ k) / (ε * M (σ k)) ^ 2 := by
          gcongr
          exact hvarT.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hMk.le)
      _ = |C| / (ε ^ 2 * M (σ k)) := by field_simp
      _ ≤ |C| / (ε ^ 2 * ((k : ℝ) + 1) ^ 2) := by
          gcongr
          exact hlow k
  have hsumm : ∀ ε : ℝ, 0 < ε →
      Summable fun k : ℕ => |C| / (ε ^ 2 * ((k : ℝ) + 1) ^ 2) := by
    intro ε hε
    have hshift : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
      have h2 := (Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num : 1 < 2)
      have heq : (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) =
          (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) ∘ (· + 1) := by
        ext n; simp only [Function.comp, one_div]; push_cast; ring
      rw [heq]
      exact h2.comp_injective (fun a b hab => by omega)
    exact (hshift.mul_left (|C| / ε ^ 2)).congr fun k => by
      have hk : ((k : ℝ) + 1) ^ 2 ≠ 0 := by positivity
      field_simp
  have hae_sub : ∀ᵐ ω ∂μ, Tendsto (fun k => (∑ i ∈ Finset.range (σ k), Y i ω) / M (σ k)) atTop
      (𝓝 1) := by
    refine ae_tendsto_of_ae_eventually_abs_sub_lt fun m => ?_
    have hε : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    have hfin : ∑' k, μ {ω | 1 / ((m : ℝ) + 1) ≤
        |(∑ i ∈ Finset.range (σ k), Y i ω) / M (σ k) - 1|} ≠ ⊤ :=
      ne_top_of_le_ne_top ((hsumm _ hε).tsum_ofReal_lt_top).ne
        (ENNReal.tsum_le_tsum fun k => hcheb _ hε k)
    filter_upwards [ae_eventually_notMem hfin] with ω hω
    exact hω.mono fun k hk => not_le.1 hk
  filter_upwards [hae_sub, ae_all_iff.2 hnonneg] with ω hω hnn
  refine tendsto_div_of_subseq (T := fun n => ∑ i ∈ Finset.range n, Y i ω)
    (fun n => Finset.sum_nonneg fun i _ => hnn i) (fun m n hmn =>
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn) fun i _ _ => hnn i)
    hMmono hσ hMpos hω hratio

end SLLN

/-! ### Almost-sure posterior consistency with different exposures -/

/-- **Almost-sure posterior consistency of the pooled posterior with different exposures.**
Let cells `i = 0, 1, …` have size factors (exposures) `sᵢ ≤ B` with divergent total
exposure `Sₙ = ∑_{i<n} sᵢ → ∞` (`sᵢ ≥ 0` is not assumed; for `r₀ > 0` it follows from
`E Xᵢ = sᵢ r₀ ≥ 0`), and let the cell counts `X₀, X₁, …` (natural numbers) be pairwise
independent and square-integrable with mean `E Xᵢ = sᵢ r₀` at a true rate `r₀ ≥ 0` and variance
`Var Xᵢ ≤ C sᵢ` (for `Xᵢ ~ Po(sᵢ r₀)`, `C = r₀`; see `ae_tendsto_pooledPosterior_poisson`).
Then almost surely, for the prior `Gamma(a, b)` (`a, b > 0`), the pooled posterior
`Gamma(a + Kₙ, b + Sₙ)` over the first `n` cells (`Kₙ = ∑_{i<n} Xᵢ`) has mean tending to `r₀`,
variance tending to `0`, and mass outside every neighbourhood `(r₀ - ε, r₀ + ε)` tending to `0`.

Unlike the common-exposure case, the counts are not identically distributed, so Mathlib's
`ProbabilityTheory.strong_law_ae` does not apply; the pooled rate `Kₙ / Sₙ → r₀` comes from
`ae_tendsto_sum_div_sum_integral`. -/
theorem ae_tendsto_pooledPosterior_exposures {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → ℕ} {s : ℕ → ℝ} {a b r₀ B C : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr₀ : 0 ≤ r₀) (hsB : ∀ i, s i ≤ B)
    (hS : Tendsto (fun n => ∑ i ∈ Finset.range n, s i) atTop atTop)
    (hL2 : ∀ i, MemLp (fun ω => (X i ω : ℝ)) 2 μ) (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hmean : ∀ i, μ[fun ω => (X i ω : ℝ)] = s i * r₀)
    (hvar : ∀ i, Var[fun ω => (X i ω : ℝ); μ] ≤ C * s i) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n => posteriorMean a b (∑ i ∈ Finset.range n, s i)
          (∑ i ∈ Finset.range n, X i ω)) atTop (𝓝 r₀) ∧
        Tendsto (fun n => (a + (∑ i ∈ Finset.range n, X i ω : ℕ)) /
          (b + ∑ i ∈ Finset.range n, s i) ^ 2) atTop (𝓝 0) ∧
        ∀ ε : ℝ, 0 < ε → Tendsto (fun n => gammaMeasure (a + (∑ i ∈ Finset.range n, X i ω : ℕ))
          (b + ∑ i ∈ Finset.range n, s i) {x | ε ≤ |x - r₀|}) atTop (𝓝 0) := by
  have hnonneg : ∀ i, 0 ≤ᵐ[μ] fun ω => (X i ω : ℝ) := fun i =>
    Eventually.of_forall fun ω => Nat.cast_nonneg _
  suffices h : ∀ᵐ ω ∂μ, Tendsto (fun n => ((∑ i ∈ Finset.range n, X i ω : ℕ) : ℝ) /
      ∑ i ∈ Finset.range n, s i) atTop (𝓝 r₀) by
    filter_upwards [h] with ω hω
    exact tendsto_pooledPosterior_of_tendsto ha hb hS hω
  rcases hr₀.eq_or_lt with h0 | hpos
  · -- `r₀ = 0`: every count vanishes almost surely.
    have hzero : ∀ i, ∀ᵐ ω ∂μ, X i ω = 0 := fun i => by
      have h := (integral_eq_zero_iff_of_nonneg_ae (hnonneg i)
        ((hL2 i).integrable one_le_two)).1 (by rw [hmean, ← h0, mul_zero])
      filter_upwards [h] with ω hω
      have h' : (X i ω : ℝ) = 0 := hω
      exact_mod_cast h'
    filter_upwards [ae_all_iff.2 hzero] with ω hω
    rw [← h0]
    refine tendsto_const_nhds.congr fun n => ?_
    simp [hω]
  · have hcast : Measurable (fun x : ℕ => (x : ℝ)) := Measurable.of_discrete
    have hlaw := ae_tendsto_sum_div_sum_integral (μ := μ) (Y := fun i ω => (X i ω : ℝ))
      (B := B * r₀) (C := C / r₀)
      hL2 hnonneg (fun i j hij => (hindep hij).comp hcast hcast)
      (fun i => by rw [hmean]; exact mul_le_mul_of_nonneg_right (hsB i) hr₀)
      (fun i => by rw [hmean, div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_right₀ _ hpos.ne'];
                   exact hvar i)
      (by simpa [hmean, ← Finset.sum_mul] using hS.atTop_mul_const hpos)
    filter_upwards [hlaw] with ω hω
    simp only [hmean, ← Finset.sum_mul] at hω
    have h := hω.const_mul r₀
    rw [mul_one] at h
    refine h.congr fun n => ?_
    rw [Nat.cast_sum, ← div_div, mul_div_cancel₀ _ hpos.ne']

/-- **Poisson counts with different exposures.** If the cell counts are pairwise independent with
`Xᵢ ~ Po(sᵢ r₀)` for size factors `sᵢ ∈ [0, B]` with divergent total exposure, then almost surely
the pooled posterior `Gamma(a + Kₙ, b + Sₙ)` has mean tending to the true rate `r₀`, variance
tending to `0`, and concentrates at `r₀`. -/
theorem ae_tendsto_pooledPosterior_poisson {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → ℕ} {s : ℕ → ℝ≥0} {r₀ : ℝ≥0}
    {a b B : ℝ} (ha : 0 < a) (hb : 0 < b) (hsB : ∀ i, (s i : ℝ) ≤ B)
    (hS : Tendsto (fun n => ∑ i ∈ Finset.range n, (s i : ℝ)) atTop atTop)
    (hlaw : ∀ i, HasLaw (X i) (poissonMeasure (s i * r₀)) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X)) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n => posteriorMean a b (∑ i ∈ Finset.range n, (s i : ℝ))
          (∑ i ∈ Finset.range n, X i ω)) atTop (𝓝 r₀) ∧
        Tendsto (fun n => (a + (∑ i ∈ Finset.range n, X i ω : ℕ)) /
          (b + ∑ i ∈ Finset.range n, (s i : ℝ)) ^ 2) atTop (𝓝 0) ∧
        ∀ ε : ℝ, 0 < ε → Tendsto (fun n => gammaMeasure (a + (∑ i ∈ Finset.range n, X i ω : ℕ))
          (b + ∑ i ∈ Finset.range n, (s i : ℝ)) {x | ε ≤ |x - r₀|}) atTop (𝓝 0) := by
  have hcast : Measurable (fun x : ℕ => (x : ℝ)) := Measurable.of_discrete
  have hmem : ∀ r : ℝ≥0, MemLp (fun n : ℕ => (n : ℝ)) 2 (poissonMeasure r) := fun r =>
    (memLp_two_iff_integrable_sq hcast.aestronglyMeasurable).2
      (integrable_natCast_sq_poissonMeasure r)
  refine ae_tendsto_pooledPosterior_exposures (C := r₀) ha hb r₀.2 hsB hS
    (fun i => (hlaw i).memLp_comp (hmem _)) hindep (fun i => ?_) (fun i => ?_)
  · have h := (hlaw i).integral_comp (f := fun n : ℕ => (n : ℝ)) hcast.aestronglyMeasurable
    rw [integral_natCast_poissonMeasure, NNReal.coe_mul] at h
    exact h
  · have h := variance_map (μ := μ) (X := fun n : ℕ => (n : ℝ)) (Y := X i)
      ((hlaw i).map_eq ▸ hcast.aemeasurable) (hlaw i).aemeasurable
    rw [(hlaw i).map_eq, variance_natCast_poissonMeasure, NNReal.coe_mul] at h
    rw [← Function.comp_def, ← h, mul_comm]

end MathlibExt.Biology.Omics.HierarchicalCountExposures
