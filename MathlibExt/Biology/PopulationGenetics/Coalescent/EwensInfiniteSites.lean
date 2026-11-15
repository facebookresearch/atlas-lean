/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.Mutation
public import MathlibExt.Probability.ProbabilityGeneratingFunction
import MathlibExt.Biology.PopulationGenetics.Haldane
import MathlibExt.Probability.Distributions.Gamma
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Probability.Independence.Integration

/-!
# The infinite-sites sampling formula: the law of the number of segregating sites

Under the neutral infinite-sites model, a sample of `n ≥ 2` genes has a Kingman genealogy and
mutations fall on its branches at rate `θ / 2` per lineage, each at a new site, so the number of
segregating sites `S_n` is the total number of mutation events. The infinite-alleles analogue,
the Ewens sampling formula for allele counts, is in
`MathlibExt.Biology.PopulationGenetics.Coalescent.Ewens`; this file gives the infinite-sites
counterpart, the exact law of `S_n` (Watterson 1975, Tavaré 1984):

`P(S_n = m) = (n - 1) ∑_{j=0}^{n-2} (-1)^j C(n-2, j) θ^m / (θ + j + 1)^{m+1}`,

with probability generating function

`E[s^{S_n}] = ∏_{k=1}^{n-1} k / (k + θ (1 - s))`, for `|s| ≤ 1`.

The model is the marked Kingman genealogy of `Mutation.lean`: holding times `T_k ~ Exp(C(k,2))`
(`KingmanTimes`) and, given them, independent `Po((θ/2) ℓ_b)` mutation counts on the branches
(`kingmanMutationKernel`). That file proves that `S_n` is conditionally `Po((θ/2) L_n)` given the
genealogy and derives the first two moments; here the full law is computed.

* **Generating function.** Conditioning on the genealogy, `E[s^S] = E[exp(-(θ/2)(1 - s) L_n)]`
  (`pgf_of_hasCondDistrib_poisson`). Since `L_n = ∑_k k T_k` with independent
  exponential `T_k`, this Laplace transform factorizes, and the factor of epoch `k` is
  `C(k,2) / (C(k,2) + k u) = (k - 1) / (k - 1 + 2u)`
  (`KingmanTimes.integral_exp_neg_mul_totalLength`). Hence
  `KingmanTimes.pgf_segSites_of_mutation`.
* **Tavaré's closed form.** `segSitesProb θ n m` is the displayed mass function. Its generating
  function is the same product (`hasSum_segSitesProb_mul_pow`): each summand is geometric in `m`,
  and the resulting partial fractions sum to the product by the identity
  `∑_{j=0}^{N} (-1)^j C(N, j) / (x + j + 1) = N! / ∏_{k=0}^{N} (x + k + 1)`.
* **The law.** Two bounded sequences whose power series agree on `(-1, 1)` are equal (uniqueness
  of power series coefficients), so `P(S_n = m) = segSitesProb θ n m`
  (`KingmanTimes.measureReal_segSites_eq_of_mutation`). In particular
  `P(S_n = 0) = ∏_{k=1}^{n-1} k / (k + θ)` and, for `n = 2`, `S_2` is geometric,
  `P(S_2 = m) = θ^m / (1 + θ)^{m+1}` (`segSitesProb_two`).
* **A concrete model.** In `kingmanMutationMeasure n θ` the law holds with no hypotheses
  (`measureReal_segSites_kingmanMutationMeasure`), which also shows that `segSitesProb θ n` is a
  probability mass function (`segSitesProb_nonneg`, `hasSum_segSitesProb`).

The expected site frequency spectrum `E[ξ_i] = θ / i` is
`SiteFrequencySpectrum.integral_sfs`; its joint law is not treated here.

## References

* G. A. Watterson, *On the number of segregating sites in genetical models without
  recombination*, Theor. Popul. Biol. 7 (1975), 256–276.
* S. Tavaré, *Line-of-descent and genealogical processes, and their applications in population
  genetics models*, Theor. Popul. Biol. 26 (1984), 119–164.
* R. Durrett, *Probability Models for DNA Sequence Evolution*, 2nd ed. (2008), §1.4.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset MathlibExt.Probability
open scoped NNReal Nat

noncomputable section

namespace MathlibExt.Biology.PopulationGenetics.Coalescent

/-! ### Tavaré's closed form and its generating function -/

/-- **Tavaré's formula** for the law of the number of segregating sites in a sample of `n ≥ 2`
genes under the infinite-sites model with scaled mutation rate `θ`:
`P(S_n = m) = (n - 1) ∑_{j=0}^{n-2} (-1)^j C(n-2, j) θ^m / (θ + j + 1)^{m+1}`. -/
def segSitesProb (θ : ℝ) (n m : ℕ) : ℝ :=
  (n - 1 : ℝ) * ∑ j ∈ range (n - 1),
    (-1) ^ j * ((n - 2).choose j : ℝ) * θ ^ m / (θ + j + 1) ^ (m + 1)

/-- The alternating partial-fraction sum `∑_{j=0}^{N} (-1)^j C(N, j) / (x + j + 1)`. -/
private def altSum (N : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range (N + 1), (-1) ^ j * (N.choose j : ℝ) / (x + j + 1)

/-- Pascal's rule for the alternating sum: `A_{N+1}(x) = A_N(x) - A_N(x + 1)`. -/
private lemma altSum_succ (N : ℕ) (x : ℝ) : altSum (N + 1) x = altSum N x - altSum N (x + 1) := by
  have hA : altSum N x = ∑ j ∈ range (N + 2), (-1) ^ j * (N.choose j : ℝ) / (x + j + 1) := by
    rw [altSum, sum_range_succ _ (N + 1), Nat.choose_succ_self]
    simp
  have hterm : ∀ j ∈ range (N + 1),
      (-1 : ℝ) ^ (j + 1) * ((N + 1).choose (j + 1) : ℝ) / (x + ((j + 1 : ℕ) : ℝ) + 1) =
        (-1 : ℝ) ^ (j + 1) * (N.choose (j + 1) : ℝ) / (x + ((j + 1 : ℕ) : ℝ) + 1) -
          (-1 : ℝ) ^ j * (N.choose j : ℝ) / (x + 1 + j + 1) := by
    intro j _
    rw [Nat.choose_succ_succ, Nat.cast_add]
    push_cast
    ring
  rw [hA, altSum, altSum, sum_range_succ', sum_range_succ' _ (N + 1), sum_congr rfl hterm,
    sum_sub_distrib]
  simp only [Nat.choose_zero_right]
  ring

/-- **The partial-fraction identity**
`∑_{j=0}^{N} (-1)^j C(N, j) / (x + j + 1) = N! / ∏_{k=0}^{N} (x + k + 1)` for `x ≥ 0`. -/
private lemma altSum_eq (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    altSum N x = N ! / ∏ k ∈ range (N + 1), (x + k + 1) := by
  induction N generalizing x with
  | zero => simp [altSum]
  | succ N ih =>
    rw [altSum_succ, ih hx, ih (by linarith)]
    set Q := ∏ k ∈ range (N + 1), (x + (k : ℝ) + 1)
    set Q' := ∏ k ∈ range (N + 1), (x + 1 + (k : ℝ) + 1)
    have hc : x + ((N : ℝ) + 1) + 1 ≠ 0 := by positivity
    have hR1 : ∏ k ∈ range (N + 1 + 1), (x + (k : ℝ) + 1) = Q * (x + ((N : ℝ) + 1) + 1) := by
      rw [prod_range_succ]
      push_cast
      ring
    have hR2 : ∏ k ∈ range (N + 1 + 1), (x + (k : ℝ) + 1) = Q' * (x + 1) := by
      rw [prod_range_succ']
      congr 1
      · exact prod_congr rfl fun k _ => by push_cast; ring
      · simp
    have h1 : (N ! : ℝ) / Q =
        N ! * (x + ((N : ℝ) + 1) + 1) / ∏ k ∈ range (N + 1 + 1), (x + (k : ℝ) + 1) := by
      rw [hR1, mul_div_mul_right _ _ hc]
    have h2 : (N ! : ℝ) / Q' = N ! * (x + 1) / ∏ k ∈ range (N + 1 + 1), (x + (k : ℝ) + 1) := by
      rw [hR2, mul_div_mul_right _ _ (by positivity)]
    rw [h1, h2, div_sub_div_same, Nat.factorial_succ]
    push_cast
    congr 1
    ring

/-- The partial-fraction identity in product form:
`(N + 1) ∑_{j=0}^{N} (-1)^j C(N, j) / (x + j + 1) = ∏_{k=1}^{N+1} k / (k + x)`. -/
private lemma succ_mul_altSum (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ((N : ℝ) + 1) * altSum N x = ∏ k ∈ range (N + 1), ((k : ℝ) + 1) / (k + 1 + x) := by
  rw [altSum_eq N hx, prod_div_distrib, ← mul_div_assoc]
  congr 1
  · have h := congrArg (fun t : ℕ => (t : ℝ)) (prod_range_add_one_eq_factorial (N + 1))
    simp only [Nat.cast_prod, Nat.cast_add, Nat.cast_one] at h
    rw [h, Nat.factorial_succ]
    push_cast
    ring
  · exact prod_congr rfl fun k _ => by ring

/-- **Generating function of Tavaré's formula**: for `θ ≥ 0`, `|s| ≤ 1` and `n ≥ 2`,
`∑_m P(S_n = m) s^m = ∏_{k=1}^{n-1} k / (k + θ (1 - s))`. -/
theorem hasSum_segSitesProb_mul_pow {θ s : ℝ} (hθ : 0 ≤ θ) (hs : |s| ≤ 1) {n : ℕ} (hn : 2 ≤ n) :
    HasSum (fun m => segSitesProb θ n m * s ^ m)
      (∏ k ∈ range (n - 1), ((k : ℝ) + 1) / (k + 1 + θ * (1 - s))) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 2 := ⟨n - 2, by omega⟩
  have e1 : N + 2 - 1 = N + 1 := by omega
  have e2 : N + 2 - 2 = N := by omega
  have hx : 0 ≤ θ * (1 - s) := mul_nonneg hθ (by linarith [le_abs_self s])
  have hterm : ∀ j ∈ range (N + 1), HasSum
      (fun m : ℕ => (-1 : ℝ) ^ j * (N.choose j : ℝ) * θ ^ m / (θ + j + 1) ^ (m + 1) * s ^ m)
      ((-1) ^ j * (N.choose j : ℝ) / (θ * (1 - s) + j + 1)) := by
    intro j _
    have hj : (0 : ℝ) ≤ j := j.cast_nonneg
    have hd : 0 < θ + j + 1 := by linarith
    have hθs : θ * |s| ≤ θ := mul_le_of_le_one_right hθ hs
    have hr : |θ * s / (θ + j + 1)| < 1 := by
      rw [abs_div, abs_of_pos hd, div_lt_one hd, abs_mul, abs_of_nonneg hθ]
      linarith
    have hden : 1 - θ * s / (θ + j + 1) = (θ * (1 - s) + j + 1) / (θ + j + 1) := by
      field_simp
      ring
    have hd' : θ * (1 - s) + j + 1 ≠ 0 := by positivity
    have h := (hasSum_geometric_of_abs_lt_one hr).mul_left
      ((-1) ^ j * (N.choose j : ℝ) / (θ + j + 1))
    convert h using 1
    · funext m
      rw [div_pow, mul_pow, pow_succ]
      field_simp
    · rw [hden, inv_div]
      field_simp
  have h := (hasSum_sum hterm).mul_left ((N : ℝ) + 1)
  convert h using 1
  · funext m
    rw [segSitesProb, e1, e2, mul_assoc, sum_mul]
    push_cast
    congr 1
    ring
  · rw [e1, ← succ_mul_altSum N hx, altSum]

/-- At `s = 0` the generating function gives the probability of no segregating sites:
`segSitesProb θ n 0 = ∏_{k=1}^{n-1} k / (k + θ)`. -/
theorem segSitesProb_zero {θ : ℝ} (hθ : 0 ≤ θ) {n : ℕ} (hn : 2 ≤ n) :
    segSitesProb θ n 0 = ∏ k ∈ range (n - 1), ((k : ℝ) + 1) / (k + 1 + θ) := by
  have h := hasSum_segSitesProb_mul_pow (s := 0) hθ (by simp) hn
  have h0 := hasSum_single (f := fun m => segSitesProb θ n m * (0 : ℝ) ^ m) 0
    fun m hm => by simp only [zero_pow hm, mul_zero]
  simp only [pow_zero, mul_one] at h0
  rw [h0.unique h]
  simp only [sub_zero, mul_one]

/-- For a sample of two genes, `S_2` is geometric: `P(S_2 = m) = θ^m / (θ + 1)^{m+1}`. -/
theorem segSitesProb_two (θ : ℝ) (m : ℕ) : segSitesProb θ 2 m = θ ^ m / (θ + 1) ^ (m + 1) := by
  simp [segSitesProb]
  norm_num

/-- Tavaré's formula is bounded uniformly in `m` for `θ ≥ 0`. -/
private lemma abs_segSitesProb_le {θ : ℝ} (hθ : 0 ≤ θ) (n m : ℕ) :
    |segSitesProb θ n m| ≤ |(n : ℝ) - 1| * ∑ j ∈ range (n - 1), ((n - 2).choose j : ℝ) := by
  rw [segSitesProb, abs_mul]
  gcongr
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
  have hj : (0 : ℝ) ≤ j := j.cast_nonneg
  have h1 : 1 ≤ θ + j + 1 := by linarith
  have hle : θ ^ m / (θ + j + 1) ^ (m + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    calc θ ^ m ≤ (θ + j + 1) ^ m := pow_le_pow_left₀ hθ (by linarith) m
      _ ≤ (θ + j + 1) ^ (m + 1) := pow_le_pow_right₀ h1 (Nat.le_succ m)
  rw [mul_div_assoc, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
  exact mul_le_of_le_one_right (Nat.cast_nonneg _) hle

/-! ### Uniqueness of power series coefficients -/

/-- Two bounded real sequences whose power series agree on `(-1, 1)` are equal. -/
private lemma eq_of_tsum_pow_eq {a b : ℕ → ℝ} {C : ℝ} (ha : ∀ m, |a m| ≤ C)
    (hb : ∀ m, |b m| ≤ C) (h : ∀ s : ℝ, |s| < 1 → ∑' m, a m * s ^ m = ∑' m, b m * s ^ m) :
    a = b := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (ha 0)
  have hsum : ∀ {c : ℕ → ℝ}, (∀ m, |c m| ≤ C) → ∀ s : ℝ, |s| < 1 →
      Summable fun m => c m * s ^ m := by
    intro c hc s hs
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one (abs_nonneg s) hs).mul_left C) fun m => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_right (hc m) (pow_nonneg (abs_nonneg s) m)
  set d := a - b with hd_def
  have hd : ∀ m, ‖d m‖ ≤ 2 * C := fun m => by
    rw [Real.norm_eq_abs, hd_def, Pi.sub_apply]
    linarith [abs_sub (a m) (b m), ha m, hb m]
  set p := FormalMultilinearSeries.ofScalars ℝ d
  have hrad : (((1 / 2 : ℝ≥0)) : ENNReal) ≤ p.radius :=
    p.le_radius_of_bound (2 * C) fun m => by
      rw [FormalMultilinearSeries.ofScalars_norm]
      have : ((1 / 2 : ℝ≥0) : ℝ) ^ m ≤ 1 := pow_le_one₀ (by positivity) (by norm_num)
      nlinarith [hd m, norm_nonneg (d m)]
  have hpos : 0 < p.radius := lt_of_lt_of_le (by norm_num) hrad
  have hp := (p.hasFPowerSeriesOnBall hpos).hasFPowerSeriesAt
  have hzero : p.sum =ᶠ[nhds 0] 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with s hs
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hs
    change p.sum s = 0
    rw [FormalMultilinearSeries.sum]
    simp_rw [p, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, hd_def, Pi.sub_apply,
      sub_mul]
    rw [(hsum ha s hs).tsum_sub (hsum hb s hs), h s hs, sub_self]
  have h0 := hp.eq_zero_of_eventually hzero
  rw [FormalMultilinearSeries.ofScalars_series_eq_zero] at h0
  funext m
  exact sub_eq_zero.1 (congrFun h0 m)

/-! ### Generating functions of the mutation model -/

/-- The Poisson generating function `E[s^N] = exp (-r (1 - s))`, from
`Haldane.pgf_poissonMeasure`. -/
private lemma integral_pow_poissonMeasure (r : ℝ≥0) (s : ℝ) :
    ∫ m, s ^ m ∂poissonMeasure r = Real.exp (-((r : ℝ) * (1 - s))) := by
  have h := Haldane.pgf_poissonMeasure r s
  rw [pgf_def] at h
  simp only [id_eq] at h
  rw [h]
  ring_nf

section CondPoisson

variable {Ω 𝓧 : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {X : Ω → 𝓧} {N : Ω → ℕ} {ρ : 𝓧 → ℝ≥0} {hρ : Measurable ρ}

/-- **Generating function of a conditionally Poisson count**: if `N ~ Po(ρ(X))` given `X`, then
`E[s^N] = E[exp(-ρ(X) (1 - s))]` for `|s| ≤ 1`. -/
theorem pgf_of_hasCondDistrib_poisson
    (h : HasCondDistrib N X (poissonMeasureKernel.comap ρ hρ) μ) {s : ℝ} (hs : |s| ≤ 1) :
    pgf N μ s = ∫ ω, Real.exp (-((ρ (X ω) : ℝ) * (1 - s))) ∂μ := by
  rw [pgf_def]
  have hX := h.aemeasurable_fst
  have hf : Measurable fun p : 𝓧 × ℕ => s ^ p.2 :=
    (measurable_of_countable (fun m : ℕ => s ^ m)).comp measurable_snd
  have hbound : ∀ p : 𝓧 × ℕ, ‖s ^ p.2‖ ≤ 1 := fun p => by
    rw [norm_pow, Real.norm_eq_abs]
    exact pow_le_one₀ (abs_nonneg s) hs
  have hg : Measurable fun x => Real.exp (-((ρ x : ℝ) * (1 - s))) :=
    Real.measurable_exp.comp ((measurable_coe_nnreal_real.comp hρ).mul_const _).neg
  calc ∫ ω, s ^ N ω ∂μ = ∫ p, s ^ p.2 ∂(μ.map fun ω => (X ω, N ω)) :=
        (integral_map h.aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ p, s ^ p.2 ∂(μ.map X ⊗ₘ poissonMeasureKernel.comap ρ hρ) := by rw [h.map_eq]
    _ = ∫ x, ∫ m, s ^ m ∂(poissonMeasureKernel.comap ρ hρ x) ∂(μ.map X) :=
        Measure.integral_compProd
          ((integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable (ae_of_all _ hbound))
    _ = ∫ x, Real.exp (-((ρ x : ℝ) * (1 - s))) ∂(μ.map X) := by
        simp only [Kernel.comap_apply, poissonMeasureKernel_apply, integral_pow_poissonMeasure]
    _ = ∫ ω, Real.exp (-((ρ (X ω) : ℝ) * (1 - s))) ∂μ := integral_map hX hg.aestronglyMeasurable

end CondPoisson

namespace KingmanTimes

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : ℕ} (K : KingmanTimes μ n)

/-- The Laplace transform of an exponential law: `E[exp(-c T)] = b / (b + c)` for `T ~ Exp(b)`. -/
private lemma integral_exp_neg_mul_expMeasure {b c : ℝ} (hb : 0 < b) (hc : 0 ≤ c) :
    ∫ x, Real.exp (-(c * x)) ∂expMeasure b = b / (b + c) := by
  have h := integral_pow_mul_exp_neg_mul_gammaMeasure one_pos hb (by linarith) 0
  simp only [pow_zero, one_mul, Nat.cast_zero, add_zero, Real.rpow_one, ascPochhammer_zero,
    Polynomial.eval_one] at h
  exact h

/-- **Laplace transform of the total branch length**: for `u ≥ 0`,
`E[exp(-u L_n)] = ∏_{k=2}^{n} C(k,2) / (C(k,2) + k u) = ∏_{k=1}^{n-1} k / (k + 2u)`. -/
theorem integral_exp_neg_mul_totalLength [IsProbabilityMeasure μ] {u : ℝ} (hu : 0 ≤ u) :
    ∫ ω, Real.exp (-(u * K.totalLength ω)) ∂μ =
      ∏ k ∈ range (n - 1), ((k : ℝ) + 1) / (k + 1 + 2 * u) := by
  have hfac : ∀ k : Icc 2 n, ∫ ω, Real.exp (-(u * (k : ℕ)) * K.T k ω) ∂μ =
      ((k : ℕ) - 1 : ℝ) / ((k : ℕ) - 1 + 2 * u) := by
    intro k
    have hk2 : (2 : ℝ) ≤ (k : ℕ) := by exact_mod_cast (mem_Icc.1 k.2).1
    have hb := choose_two_pos k.2
    have hc : 0 ≤ u * (k : ℕ) := mul_nonneg hu (Nat.cast_nonneg _)
    have h := (K.hasLaw k k.2).integral_comp (f := fun x => Real.exp (-(u * (k : ℕ)) * x))
      (by fun_prop)
    simp only [Function.comp_def] at h
    rw [h]
    simp_rw [neg_mul]
    rw [integral_exp_neg_mul_expMeasure hb hc, Nat.cast_choose_two]
    have hk1 : (0 : ℝ) < (k : ℕ) - 1 := by linarith
    field_simp
  have hmeas : ∀ k : Icc 2 n, AEMeasurable (K.T k) μ := fun k => (K.hasLaw k k.2).aemeasurable
  have hprod := K.indep.integral_fun_prod_comp hmeas
    (f := fun (k : Icc 2 n) (x : ℝ) => Real.exp (-(u * (k : ℕ)) * x)) fun k => by fun_prop
  have hL : ∀ ω, Real.exp (-(u * K.totalLength ω)) =
      ∏ k : Icc 2 n, Real.exp (-(u * (k : ℕ)) * K.T k ω) := by
    intro ω
    rw [← Real.exp_sum, totalLength, mul_sum, ← sum_neg_distrib, ← sum_coe_sort (Icc 2 n)]
    congr 1
    exact sum_congr rfl fun k _ => by ring
  simp_rw [hL]
  rw [hprod]
  simp_rw [hfac]
  rw [prod_coe_sort (Icc 2 n) (fun k : ℕ => ((k : ℝ) - 1) / ((k : ℝ) - 1 + 2 * u)),
    ← Finset.Ico_add_one_right_eq_Icc, prod_Ico_eq_prod_range]
  rw [show n + 1 - 2 = n - 1 by omega]
  exact prod_congr rfl fun k _ => by push_cast; ring

variable {θ : ℝ≥0} {N : Ω → KingmanBranch n → ℕ}

/-- **Probability generating function of the number of segregating sites**: under
infinite-sites mutation at rate `θ / 2` per lineage on a Kingman genealogy,
`E[s^{S_n}] = ∏_{k=1}^{n-1} k / (k + θ (1 - s))` for `|s| ≤ 1`. -/
theorem pgf_segSites_of_mutation [IsProbabilityMeasure μ]
    (hN : HasCondDistrib N K.epochs (kingmanMutationKernel n θ) μ) {s : ℝ} (hs : |s| ≤ 1) :
    pgf (fun ω => ∑ b, N ω b) μ s =
      ∏ k ∈ range (n - 1), ((k : ℝ) + 1) / (k + 1 + θ * (1 - s)) := by
  have hu : 0 ≤ (θ : ℝ) / 2 * (1 - s) :=
    mul_nonneg (by positivity) (by linarith [le_abs_self s])
  rw [pgf_of_hasCondDistrib_poisson (K.hasCondDistrib_segSites_of_mutation hN) hs,
    show (θ : ℝ) * (1 - s) = 2 * ((θ : ℝ) / 2 * (1 - s)) by ring,
    ← K.integral_exp_neg_mul_totalLength hu]
  refine integral_congr_ae ?_
  filter_upwards [K.sum_kingmanBranchLength_epochs] with ω h
  rw [NNReal.coe_mul, h, NNReal.coe_div, NNReal.coe_two]
  ring_nf

/-- **The infinite-sites sampling formula** (Watterson 1975, Tavaré 1984): under infinite-sites
mutation at rate `θ / 2` per lineage on the Kingman genealogy of `n ≥ 2` genes, the number of
segregating sites has law
`P(S_n = m) = (n - 1) ∑_{j=0}^{n-2} (-1)^j C(n-2, j) θ^m / (θ + j + 1)^{m+1}`. -/
theorem measureReal_segSites_eq_of_mutation [IsProbabilityMeasure μ]
    (hN : HasCondDistrib N K.epochs (kingmanMutationKernel n θ) μ) (hn : 2 ≤ n) (m : ℕ) :
    μ.real {ω | ∑ b, N ω b = m} = segSitesProb θ n m := by
  have hS : AEMeasurable (fun ω => ∑ b, N ω b) μ :=
    (K.hasCondDistrib_segSites_of_mutation hN).aemeasurable_snd
  have hlaw : ∀ s : ℝ, |s| ≤ 1 →
      ∑' m, μ.real {ω | ∑ b, N ω b = m} * s ^ m = pgf (fun ω => ∑ b, N ω b) μ s := by
    intro s hs
    rw [pgf_def]
    have hint : Integrable (fun m : ℕ => s ^ m) (μ.map fun ω => ∑ b, N ω b) :=
      (integrable_const (1 : ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
        (ae_of_all _ fun m => by
          rw [norm_pow, Real.norm_eq_abs]
          exact pow_le_one₀ (abs_nonneg s) hs)
    rw [← integral_map hS (measurable_of_countable (fun m : ℕ => s ^ m)).aestronglyMeasurable,
      integral_countable hint]
    congr 1
    funext m
    rw [smul_eq_mul, measureReal_def, measureReal_def,
      Measure.map_apply_of_aemeasurable hS (measurableSet_singleton m)]
    rfl
  have hθ : (0 : ℝ) ≤ θ := θ.coe_nonneg
  set B := |(n : ℝ) - 1| * ∑ j ∈ range (n - 1), ((n - 2).choose j : ℝ)
  have hB : 0 ≤ B := (abs_nonneg _).trans (abs_segSitesProb_le hθ n 0)
  have hpb : ∀ m, |μ.real {ω | ∑ b, N ω b = m}| ≤ max 1 B := fun m => by
    rw [abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one.trans (le_max_left _ _)
  have hqb : ∀ m, |segSitesProb θ n m| ≤ max 1 B := fun m =>
    (abs_segSitesProb_le hθ n m).trans (le_max_right _ _)
  have heq := eq_of_tsum_pow_eq hpb hqb fun s hs => by
    rw [hlaw s hs.le, K.pgf_segSites_of_mutation hN hs.le,
      (hasSum_segSitesProb_mul_pow hθ hs.le hn).tsum_eq]
  exact congrFun heq m

/-- **No segregating sites**: `P(S_n = 0) = ∏_{k=1}^{n-1} k / (k + θ)`. -/
theorem measureReal_segSites_eq_zero_of_mutation [IsProbabilityMeasure μ]
    (hN : HasCondDistrib N K.epochs (kingmanMutationKernel n θ) μ) (hn : 2 ≤ n) :
    μ.real {ω | ∑ b, N ω b = 0} = ∏ k ∈ range (n - 1), ((k : ℝ) + 1) / (k + 1 + θ) := by
  rw [K.measureReal_segSites_eq_of_mutation hN hn, segSitesProb_zero θ.coe_nonneg hn]

end KingmanTimes

/-! ### The concrete marked Kingman model -/

/-- **The infinite-sites sampling formula in the marked Kingman model**, with no remaining
hypotheses: `P(S_n = m) = segSitesProb θ n m` for `n ≥ 2`. -/
theorem measureReal_segSites_kingmanMutationMeasure (θ : ℝ≥0) {n : ℕ} (hn : 2 ≤ n) (m : ℕ) :
    (kingmanMutationMeasure n θ).real {p | ∑ b, p.2 b = m} = segSitesProb θ n m :=
  (KingmanTimes.ofMutationModel n θ).measureReal_segSites_eq_of_mutation
    (hasCondDistrib_kingmanMutationMeasure n θ) hn m

/-- **Generating function in the marked Kingman model**:
`E[s^{S_n}] = ∏_{k=1}^{n-1} k / (k + θ (1 - s))` for `|s| ≤ 1`. -/
theorem pgf_segSites_kingmanMutationMeasure (θ : ℝ≥0) (n : ℕ) {s : ℝ} (hs : |s| ≤ 1) :
    pgf (fun p => ∑ b, p.2 b) (kingmanMutationMeasure n θ) s =
      ∏ k ∈ range (n - 1), ((k : ℝ) + 1) / (k + 1 + θ * (1 - s)) :=
  (KingmanTimes.ofMutationModel n θ).pgf_segSites_of_mutation
    (hasCondDistrib_kingmanMutationMeasure n θ) hs

/-- Tavaré's formula is nonnegative for `θ ≥ 0`: it is a probability in the marked model. -/
theorem segSitesProb_nonneg (θ : ℝ≥0) {n : ℕ} (hn : 2 ≤ n) (m : ℕ) :
    0 ≤ segSitesProb θ n m := by
  rw [← measureReal_segSites_kingmanMutationMeasure θ hn m]
  exact measureReal_nonneg

/-- Tavaré's formula sums to `1` for `θ ≥ 0` and `n ≥ 2`. -/
theorem hasSum_segSitesProb {θ : ℝ} (hθ : 0 ≤ θ) {n : ℕ} (hn : 2 ≤ n) :
    HasSum (segSitesProb θ n) 1 := by
  have h := hasSum_segSitesProb_mul_pow hθ (s := 1) (by simp) hn
  simp only [one_pow, mul_one, sub_self, mul_zero, add_zero] at h
  convert h using 1
  rw [eq_comm]
  exact prod_eq_one fun k _ => div_self (by positivity)

end MathlibExt.Biology.PopulationGenetics.Coalescent
