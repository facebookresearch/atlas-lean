/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Contiguity
public import MathlibExt.Probability.Statistics.LikelihoodRatioTests
public import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.StrongLaw

/-!
# Local power of the likelihood-ratio test

Let row `n` of a triangular array `X n 0, X n 1, …` be i.i.d. with law `p θₙ ν`, where
`θₙ = θ₀ + h / √n` is a local alternative to the simple null `θ = θ₀`. Under the Cramér
conditions at `θ₀` (the hypotheses of Wilks' theorem
`LikelihoodRatioTests.tendstoInDistribution_two_mul_logLikelihood_sub`, all stated under the
null law `p θ₀ ν`), the likelihood-ratio statistic `2 (ℓₙ(θ̂ₙ) - ℓₙ(θ₀))` of a consistent root
`θ̂ₙ` of the likelihood equation converges in distribution to the noncentral chi-square law
with one degree of freedom and noncentrality `h² I(θ₀)`: the law of `(Z + h √I(θ₀))²`,
`Z ~ N(0, 1)`.

The proof follows van der Vaart (1998), ch. 6–7 and 16:

1. *Local asymptotic normality.* On the infinite product space `(p θ₀ ν)^ℕ`, the
   log-likelihood ratio `Λₙ = ∑_{i<n} (log p θₙ (xᵢ) - log p θ₀ (xᵢ))` satisfies
   `Λₙ - h Sₙ → -h² I(θ₀) / 2` in probability, where `Sₙ = n^{-1/2} ∑_{i<n} ∂_θ log p θ₀ (xᵢ)`
   (`tendstoInMeasure_logLikelihoodRatio_sub`, a second-order Taylor expansion with the
   third-derivative envelope).
2. *Change of measure.* Reweighting the product measure by `exp Λₙ` gives a measure whose first
   `n` coordinates are i.i.d. `p θₙ ν` (`map_withDensity_infinitePi_prod`), so every statistic of
   row `n` has the same law under the alternative as on the reweighted product space.
3. *Le Cam's lemmas.* By Le Cam's first lemma the reweighted measures are contiguous to the null
   product measure, so the laws of large numbers for `∂²_θ log p θ₀` and the envelope `M` carry
   over; by Le Cam's third lemma `Sₙ → N(h I(θ₀), I(θ₀))` under the alternative
   (`Contiguity`).
4. *Quadratic expansion.* With these inputs the deterministic expansion of the null case gives
   `2 (ℓₙ(θ̂ₙ) - ℓₙ(θ₀)) = Sₙ² / I(θ₀) + o_P(1)`
   (`tendstoInDistribution_two_mul_logLikelihood_sub_of_triangular`).

## Main results

* `tendstoInDistribution_two_mul_logLikelihood_sub_local`: the local-power theorem.
* `tendstoInDistribution_two_mul_logLikelihood_sub_of_triangular`: Wilks' expansion for a
  triangular array, with the law of large numbers and the central limit theorem as hypotheses.
* `tendstoInMeasure_logLikelihoodRatio_sub`: local asymptotic normality of the log-likelihood
  ratio under the Cramér conditions.
* `map_withDensity_infinitePi_prod`: reweighting an infinite product measure by a product
  density in the first `n` coordinates.

## References

* S. S. Wilks, "The large-sample distribution of the likelihood ratio for testing composite
  hypotheses", Ann. Math. Statist. 9 (1938) 60–62.
* L. Le Cam, "Locally asymptotically normal families of distributions", Univ. California
  Publ. Statist. 3 (1960) 37–98.
* A. W. van der Vaart, *Asymptotic Statistics* (1998), ch. 6, 7 and 16.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open MathlibExt.Probability.Statistics.FisherInformation
open MathlibExt.Probability.Statistics.MLEAsymptoticNormality
open MathlibExt.Probability.Statistics.Contiguity

namespace MathlibExt.Probability.Statistics.LikelihoodRatioLocalPower

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- **Reweighting an infinite product measure by a product density.** If `μ.withDensity r` is a
probability measure, then reweighting the product measure `μ^ℕ` by `∏_{i<n} r (xᵢ)` and
projecting onto the first `n` coordinates gives the product measure `(μ.withDensity r)^n`. -/
theorem map_withDensity_infinitePi_prod {μ : Measure 𝓧} [IsProbabilityMeasure μ]
    {r : 𝓧 → ℝ≥0∞} (hr : Measurable r) [IsProbabilityMeasure (μ.withDensity r)] (n : ℕ) :
    ((Measure.infinitePi fun _ : ℕ => μ).withDensity
        fun x => ∏ i ∈ Finset.range n, r (x i)).map (fun x (i : Fin n) => x i) =
      Measure.pi fun _ : Fin n => μ.withDensity r := by
  classical
  have hπ : Measurable fun (x : ℕ → 𝓧) (i : Fin n) => x i :=
    measurable_pi_iff.2 fun i => measurable_pi_apply _
  refine (Measure.pi_eq fun s hs => ?_).symm
  have hS : MeasurableSet ((fun (x : ℕ → 𝓧) (i : Fin n) => x i) ⁻¹' Set.univ.pi s) :=
    hπ (MeasurableSet.univ_pi hs)
  rw [Measure.map_apply hπ (MeasurableSet.univ_pi hs), withDensity_apply _ hS,
    ← lintegral_indicator hS]
  have e : ((fun (x : ℕ → 𝓧) (i : Fin n) => x i) ⁻¹' Set.univ.pi s).indicator
      (fun x => ∏ i ∈ Finset.range n, r (x i)) =
        fun x => ∏ i : Fin n, (s i).indicator r (x i) := by
    funext x
    by_cases hx : ∀ i : Fin n, x i ∈ s i
    · rw [Set.indicator_of_mem (by simpa [Set.mem_univ_pi] using hx), Finset.prod_range]
      exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hx i) _).symm
    · obtain ⟨i, hi⟩ := not_forall.1 hx
      rw [Set.indicator_of_notMem (by simpa [Set.mem_univ_pi] using ⟨i, hi⟩)]
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  have hind : iIndepFun (fun (i : Fin n) (x : ℕ → 𝓧) => (s i).indicator r (x i))
      (Measure.infinitePi fun _ : ℕ => μ) :=
    ((iIndepFun_infinitePi (P := fun _ : ℕ => μ) (X := fun _ => id)
      fun _ => measurable_id).precomp Fin.val_injective).comp (fun i => (s i).indicator r)
      (fun i => hr.indicator (hs i))
  rw [e, lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hind
    (fun i => (hr.indicator (hs i)).comp (measurable_pi_apply _))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), ← lintegral_indicator (hs i)]
  calc ∫⁻ x, (s i).indicator r (x i) ∂Measure.infinitePi (fun _ : ℕ => μ)
      = ∫⁻ y, (s i).indicator r y ∂((Measure.infinitePi fun _ : ℕ => μ).map fun x => x i) :=
        (lintegral_map (hr.indicator (hs i)) (measurable_pi_apply _)).symm
    _ = _ := by rw [Measure.infinitePi_map_eval]

open Set in
/-- First-order Taylor bound from a bound `m` on the second derivative on a ball. -/
private theorem abs_sub_sub_mul_deriv_le' {f : ℝ → ℝ} {θ₀ δ θ m : ℝ}
    (hf : ∀ t ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ f t)
    (hf' : ∀ t ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (deriv f) t)
    (hm : ∀ t ∈ Metric.ball θ₀ δ, |deriv (deriv f) t| ≤ m) (hθ : θ ∈ Metric.ball θ₀ δ) :
    |f θ - f θ₀ - (θ - θ₀) * deriv f θ₀| ≤ m * (θ - θ₀) ^ 2 := by
  have h0 : θ₀ ∈ Metric.ball θ₀ δ := Metric.mem_ball_self (lt_of_le_of_lt dist_nonneg hθ)
  have hsub : uIcc θ₀ θ ⊆ Metric.ball θ₀ δ := by
    rw [Real.ball_eq_Ioo] at h0 hθ ⊢
    exact ordConnected_Ioo.uIcc_subset h0 hθ
  have h1 : ∀ t ∈ uIcc θ₀ θ, |deriv f t - deriv f θ₀| ≤ m * |θ - θ₀| := fun t ht => by
    have := (convex_ball θ₀ δ).norm_image_sub_le_of_norm_deriv_le hf' (fun s hs => by
      rw [Real.norm_eq_abs]; exact hm s hs) h0 (hsub ht)
    simp only [Real.norm_eq_abs] at this
    exact this.trans (mul_le_mul_of_nonneg_left (abs_sub_left_of_mem_uIcc ht)
      ((abs_nonneg _).trans (hm θ₀ h0)))
  set g : ℝ → ℝ := fun t => f t - (t - θ₀) * deriv f θ₀
  have hg : ∀ t ∈ uIcc θ₀ θ, HasDerivAt g (deriv f t - deriv f θ₀) t := fun t ht => by
    have := ((hf t (hsub ht)).hasDerivAt.fun_sub
      (((hasDerivAt_id t).sub_const θ₀).mul_const (deriv f θ₀)))
    simpa only [id, one_mul] using this
  have key := (convex_uIcc θ₀ θ).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hg t ht).hasDerivWithinAt) (fun t ht => by
      rw [Real.norm_eq_abs]; exact h1 t ht) left_mem_uIcc right_mem_uIcc
  simp only [Real.norm_eq_abs, g, sub_self, zero_mul, sub_zero] at key
  calc |f θ - f θ₀ - (θ - θ₀) * deriv f θ₀| = |f θ - (θ - θ₀) * deriv f θ₀ - f θ₀| := by
        ring_nf
    _ ≤ m * |θ - θ₀| * |θ - θ₀| := key
    _ = m * (θ - θ₀) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

open Set in
/-- Second-order Taylor bound at the fixed point `θ₀` with a third-derivative bound `m`:
`|f θ₀ - f θ - (θ₀ - θ) f'(θ) - (θ₀ - θ)² / 2 · f''(θ₀)| ≤ m |θ - θ₀|³`. -/
private theorem abs_taylor_two_le' {f f₁ f₂ f₃ : ℝ → ℝ} {θ₀ δ θ m : ℝ}
    (hf : ∀ t ∈ Metric.ball θ₀ δ, HasDerivAt f (f₁ t) t)
    (hf₁ : ∀ t ∈ Metric.ball θ₀ δ, HasDerivAt f₁ (f₂ t) t)
    (hf₂ : ∀ t ∈ Metric.ball θ₀ δ, HasDerivAt f₂ (f₃ t) t)
    (hm : ∀ t ∈ Metric.ball θ₀ δ, |f₃ t| ≤ m) (hθ : θ ∈ Metric.ball θ₀ δ) :
    |f θ₀ - f θ - (θ₀ - θ) * f₁ θ - (θ₀ - θ) ^ 2 / 2 * f₂ θ₀| ≤ m * |θ - θ₀| ^ 3 := by
  have h0 : θ₀ ∈ Metric.ball θ₀ δ := Metric.mem_ball_self (lt_of_le_of_lt dist_nonneg hθ)
  have hsub : uIcc θ₀ θ ⊆ Metric.ball θ₀ δ := by
    rw [Real.ball_eq_Ioo] at h0 hθ ⊢
    exact ordConnected_Ioo.uIcc_subset h0 hθ
  have hm0 : 0 ≤ m := (abs_nonneg _).trans (hm θ₀ h0)
  have h2 : ∀ t ∈ uIcc θ₀ θ, |f₂ θ₀ - f₂ t| ≤ m * |θ - θ₀| := fun t ht => by
    have := (convex_ball θ₀ δ).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s hs => (hf₂ s hs).hasDerivWithinAt) (fun s hs => by
        rw [Real.norm_eq_abs]; exact hm s hs) (hsub ht) h0
    simp only [Real.norm_eq_abs] at this
    exact this.trans (mul_le_mul_of_nonneg_left (by
      rw [abs_sub_comm]; exact abs_sub_left_of_mem_uIcc ht) hm0)
  set φ : ℝ → ℝ := fun t => f θ₀ - f t - (θ₀ - t) * f₁ t - (θ₀ - t) * (θ₀ - t) / 2 * f₂ θ₀
    with hφ_def
  have hφ : ∀ t ∈ uIcc θ₀ θ, HasDerivAt φ ((θ₀ - t) * (f₂ θ₀ - f₂ t)) t := fun t ht => by
    have hl : HasDerivAt (fun t : ℝ => θ₀ - t) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub θ₀
    have := (((hasDerivAt_const t (f θ₀)).sub (hf t (hsub ht))).sub
      (hl.mul (hf₁ t (hsub ht)))).sub (((hl.mul hl).div_const 2).mul_const (f₂ θ₀))
    convert this using 1
    ring
  have hφ' : ∀ t ∈ uIcc θ₀ θ, ‖(θ₀ - t) * (f₂ θ₀ - f₂ t)‖ ≤ m * |θ - θ₀| ^ 2 := fun t ht => by
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |θ₀ - t| ≤ |θ - θ₀| := by rw [abs_sub_comm]; exact abs_sub_left_of_mem_uIcc ht
    calc |θ₀ - t| * |f₂ θ₀ - f₂ t| ≤ |θ - θ₀| * (m * |θ - θ₀|) :=
          mul_le_mul h1 (h2 t ht) (abs_nonneg _) (abs_nonneg _)
      _ = m * |θ - θ₀| ^ 2 := by ring
  have key := (convex_uIcc θ₀ θ).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hφ t ht).hasDerivWithinAt) hφ' left_mem_uIcc right_mem_uIcc
  have hφ0 : φ θ₀ = 0 := by simp [hφ_def]
  rw [hφ0, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at key
  have e : f θ₀ - f θ - (θ₀ - θ) * f₁ θ - (θ₀ - θ) ^ 2 / 2 * f₂ θ₀ = φ θ := by
    simp only [hφ_def]; ring
  rw [e]
  calc |φ θ| ≤ m * |θ - θ₀| ^ 2 * |θ - θ₀| := key
    _ = m * |θ - θ₀| ^ 3 := by ring

open Set in
/-- Second-order Taylor bound at the center `θ₀` with a third-derivative bound `m` on a ball:
`|f θ - f θ₀ - (θ - θ₀) f'(θ₀) - (θ - θ₀)² / 2 · f''(θ₀)| ≤ m |θ - θ₀|³`. -/
private theorem abs_taylor_center_le {f : ℝ → ℝ} {θ₀ δ θ m : ℝ}
    (hf : ∀ t ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ f t)
    (hf' : ∀ t ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (deriv f) t)
    (hf'' : ∀ t ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (deriv (deriv f)) t)
    (hm : ∀ t ∈ Metric.ball θ₀ δ, |deriv (deriv (deriv f)) t| ≤ m)
    (hθ : θ ∈ Metric.ball θ₀ δ) :
    |f θ - f θ₀ - (θ - θ₀) * deriv f θ₀ - (θ - θ₀) ^ 2 / 2 * deriv (deriv f) θ₀| ≤
      m * |θ - θ₀| ^ 3 := by
  have h0 : θ₀ ∈ Metric.ball θ₀ δ := Metric.mem_ball_self (lt_of_le_of_lt dist_nonneg hθ)
  have hsub : uIcc θ₀ θ ⊆ Metric.ball θ₀ δ := by
    rw [Real.ball_eq_Ioo] at h0 hθ ⊢
    exact ordConnected_Ioo.uIcc_subset h0 hθ
  have hm0 : 0 ≤ m := (abs_nonneg _).trans (hm θ₀ h0)
  set φ : ℝ → ℝ := fun t => f t - f θ₀ - (t - θ₀) * deriv f θ₀ -
    (t - θ₀) * (t - θ₀) / 2 * deriv (deriv f) θ₀ with hφ_def
  have hφ : ∀ t ∈ uIcc θ₀ θ,
      HasDerivAt φ (deriv f t - deriv f θ₀ - (t - θ₀) * deriv (deriv f) θ₀) t := fun t ht => by
    have hl : HasDerivAt (fun t : ℝ => t - θ₀) 1 t := (hasDerivAt_id t).sub_const θ₀
    have := (((hf t (hsub ht)).hasDerivAt.sub_const (f θ₀)).sub
      (hl.mul_const (deriv f θ₀))).sub (((hl.mul hl).div_const 2).mul_const (deriv (deriv f) θ₀))
    convert this using 1
    ring
  have hφ' : ∀ t ∈ uIcc θ₀ θ, ‖deriv f t - deriv f θ₀ - (t - θ₀) * deriv (deriv f) θ₀‖ ≤
      m * |θ - θ₀| ^ 2 := fun t ht => by
    rw [Real.norm_eq_abs]
    have h1 := abs_sub_sub_mul_deriv_le' (f := deriv f) hf' hf'' hm (hsub ht)
    have h2 : (t - θ₀) ^ 2 ≤ |θ - θ₀| ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_sub_left_of_mem_uIcc ht) 2
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hm0)
  have key := (convex_uIcc θ₀ θ).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hφ t ht).hasDerivWithinAt) hφ' left_mem_uIcc right_mem_uIcc
  have hφ0 : φ θ₀ = 0 := by simp [hφ_def]
  rw [hφ0, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at key
  have e : f θ - f θ₀ - (θ - θ₀) * deriv f θ₀ - (θ - θ₀) ^ 2 / 2 * deriv (deriv f) θ₀ = φ θ := by
    simp only [hφ_def]; ring
  rw [e]
  calc |φ θ| ≤ m * |θ - θ₀| ^ 2 * |θ - θ₀| := key
    _ = m * |θ - θ₀| ^ 3 := by ring

omit [MeasurableSpace 𝓧] [IsProbabilityMeasure P] in
/-- **Local asymptotic normality of the log-likelihood ratio.** Suppose that on the ball of
radius `δ > 0` about `θ₀` the log-likelihood `log p θ x` is differentiable in `θ`, the score
`∂_θ log p θ x` is twice differentiable in `θ`, and `|∂³_θ log p θ x| ≤ M x`. Let `Y 0, Y 1, …`
be random variables such that `-(n⁻¹ ∑_{i<n} ∂²_θ log p θ₀ (Y i)) → I` and
`n⁻¹ ∑_{i<n} M (Y i) → c` in probability (laws of large numbers). Then, for the local
parameters `θₙ = θ₀ + h / √n`,
`∑_{i<n} (log p θₙ (Y i) - log p θ₀ (Y i)) - h n^{-1/2} ∑_{i<n} ∂_θ log p θ₀ (Y i)`
converges to `-h² I / 2` in probability.

Source: van der Vaart (1998), Theorem 7.2 (local asymptotic normality), here under Cramér's
third-derivative envelope instead of differentiability in quadratic mean. -/
theorem tendstoInMeasure_logLikelihoodRatio_sub {p : ℝ → 𝓧 → ℝ} {θ₀ δ h I c : ℝ}
    (hδ : 0 < δ)
    (hℓ_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => Real.log (p t x)) θ)
    (hs_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => score p t x) θ)
    (hs'_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      DifferentiableAt ℝ (fun t => deriv (fun s => score p s x) t) θ)
    {M : 𝓧 → ℝ} (hM : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      |deriv (fun t => deriv (fun s => score p s x) t) θ| ≤ M x)
    {Y : ℕ → Ω → 𝓧}
    (hB : TendstoInMeasure P
      (fun (n : ℕ) ω => -((∑ i ∈ Finset.range n, deriv (fun t => score p t (Y i ω)) θ₀) / n))
      atTop (fun _ => I))
    (hMb : TendstoInMeasure P (fun (n : ℕ) ω => (∑ i ∈ Finset.range n, M (Y i ω)) / n)
      atTop (fun _ => c)) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => ∑ i ∈ Finset.range n,
          (Real.log (p (θ₀ + h / √n) (Y i ω)) - Real.log (p θ₀ (Y i ω))) -
        h * ((√n)⁻¹ * ∑ i ∈ Finset.range n, score p θ₀ (Y i ω)))
      atTop (fun _ => -(h ^ 2 * I / 2)) := by
  have hθ₀ : θ₀ ∈ Metric.ball θ₀ δ := Metric.mem_ball_self hδ
  have hM0 : ∀ x, 0 ≤ M x := fun x => (abs_nonneg _).trans (hM x θ₀ hθ₀)
  set ψ' : 𝓧 → ℝ := fun x => deriv (fun t => score p t x) θ₀ with hψ'_def
  set B : ℕ → Ω → ℝ := fun n ω => -((∑ i ∈ Finset.range n, ψ' (Y i ω)) / n) with hB_def
  set Mb : ℕ → Ω → ℝ := fun n ω => (∑ i ∈ Finset.range n, M (Y i ω)) / n with hMb_def
  set F : ℕ → Ω → ℝ := fun n ω => ∑ i ∈ Finset.range n,
      (Real.log (p (θ₀ + h / √n) (Y i ω)) - Real.log (p θ₀ (Y i ω))) -
    h * ((√n)⁻¹ * ∑ i ∈ Finset.range n, score p θ₀ (Y i ω)) with hF_def
  -- the deterministic bound for large `n`
  have hbound : ∀ n : ℕ, 0 < n → h / √n ∈ Metric.ball (0 : ℝ) δ → ∀ ω,
      |F n ω + h ^ 2 * I / 2| ≤ h ^ 2 / 2 * |B n ω - I| + |h| ^ 3 * ((√n)⁻¹ * Mb n ω) := by
    intro n hn hd ω
    have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hball : θ₀ + h / √n ∈ Metric.ball θ₀ δ := by
      rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left]
      rwa [Metric.mem_ball, Real.dist_eq, sub_zero] at hd
    have htay : |∑ i ∈ Finset.range n,
          (Real.log (p (θ₀ + h / √n) (Y i ω)) - Real.log (p θ₀ (Y i ω))) -
        h / √n * ∑ i ∈ Finset.range n, score p θ₀ (Y i ω) -
        (h / √n) ^ 2 / 2 * ∑ i ∈ Finset.range n, ψ' (Y i ω)| ≤
          (∑ i ∈ Finset.range n, M (Y i ω)) * |h / √n| ^ 3 := by
      have e : ∑ i ∈ Finset.range n,
          (Real.log (p (θ₀ + h / √n) (Y i ω)) - Real.log (p θ₀ (Y i ω))) -
          h / √n * ∑ i ∈ Finset.range n, score p θ₀ (Y i ω) -
          (h / √n) ^ 2 / 2 * ∑ i ∈ Finset.range n, ψ' (Y i ω) =
          ∑ i ∈ Finset.range n, (Real.log (p (θ₀ + h / √n) (Y i ω)) - Real.log (p θ₀ (Y i ω)) -
            (θ₀ + h / √n - θ₀) * score p θ₀ (Y i ω) -
            (θ₀ + h / √n - θ₀) ^ 2 / 2 * ψ' (Y i ω)) := by
        simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, add_sub_cancel_left]
      rw [e, Finset.sum_mul]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      have := abs_taylor_center_le (f := fun t => Real.log (p t (Y i ω)))
        (hℓ_diff (Y i ω)) (hs_diff (Y i ω)) (hs'_diff (Y i ω)) (hM (Y i ω)) hball
      rw [add_sub_cancel_left] at this ⊢
      exact this
    have hSM : 0 ≤ ∑ i ∈ Finset.range n, M (Y i ω) := Finset.sum_nonneg fun i _ => hM0 _
    have hB' : B n ω = -(∑ i ∈ Finset.range n, ψ' (Y i ω)) / n := by
      simp only [hB_def]; ring
    have hMb' : Mb n ω = (∑ i ∈ Finset.range n, M (Y i ω)) / n := rfl
    simp only [hF_def]
    rw [hB', hMb']
    generalize ∑ i ∈ Finset.range n,
      (Real.log (p (θ₀ + h / √n) (Y i ω)) - Real.log (p θ₀ (Y i ω))) = L at htay ⊢
    generalize ∑ i ∈ Finset.range n, score p θ₀ (Y i ω) = S at htay ⊢
    generalize ∑ i ∈ Finset.range n, ψ' (Y i ω) = T at htay ⊢
    generalize ∑ i ∈ Finset.range n, M (Y i ω) = SM at htay hSM ⊢
    obtain ⟨r, hr_def⟩ : ∃ r, r = √(n : ℝ) := ⟨_, rfl⟩
    have hn' : (n : ℝ) = r ^ 2 := by rw [hr_def, Real.sq_sqrt (Nat.cast_nonneg n)]
    rw [← hr_def] at hs htay ⊢
    rw [hn']
    have e1 : L - h * (r⁻¹ * S) + h ^ 2 * I / 2 =
        (L - h / r * S - (h / r) ^ 2 / 2 * T) - h ^ 2 / 2 * (-T / r ^ 2 - I) := by
      field_simp; ring
    have e2 : SM * |h / r| ^ 3 = |h| ^ 3 * (r⁻¹ * (SM / r ^ 2)) := by
      rw [abs_div, abs_of_pos hs]; field_simp
    rw [e1]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ h ^ 2 / 2), ← e2]
    linarith
  -- convergence
  have hd : Tendsto (fun n : ℕ => h / √n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hinv : Tendsto (fun n : ℕ => (√n)⁻¹) atTop (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  set K : ℝ := h ^ 2 / 2 + |h| ^ 3 + 1 with hK_def
  have hK : 0 < K := by positivity
  have hε' : 0 < ε / (3 * K) := by positivity
  have h1 := (tendstoInMeasure_iff_norm.1 hB) _ hε'
  have h2 := (tendstoInMeasure_iff_norm.1 hMb) _ hε'
  have hev1 : ∀ᶠ n : ℕ in atTop, h / √n ∈ Metric.ball (0 : ℝ) δ := hd (Metric.ball_mem_nhds 0 hδ)
  have hev2 : ∀ᶠ n : ℕ in atTop, (√n)⁻¹ * (K * |c|) < ε / 3 := by
    have := hinv.mul_const (K * |c|)
    rw [zero_mul] at this
    exact this.eventually (gt_mem_nhds (by positivity))
  have hev3 : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have hev4 : ∀ᶠ n : ℕ in atTop, (√n)⁻¹ ≤ 1 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 (by exact_mod_cast hn))
  have h12 := h1.add h2
  rw [add_zero] at h12
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h12
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hev1, hev2, hev3, hev4] with n hn1 hn2 hn3 hn4
  refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  simp only [Set.mem_ofPred_eq, Real.norm_eq_abs, sub_neg_eq_add] at hω ⊢
  by_contra hc
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hc
  obtain ⟨hc1, hc2⟩ := hc
  have hb := hbound n hn3 hn1 ω
  have hs0 : 0 ≤ (√(n : ℝ))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  have hMb_le : Mb n ω ≤ |Mb n ω - c| + |c| := by
    have := abs_sub_abs_le_abs_sub (Mb n ω) c
    linarith [le_abs_self (Mb n ω)]
  have hMb0 : 0 ≤ Mb n ω := div_nonneg (Finset.sum_nonneg fun i _ => hM0 _) (Nat.cast_nonneg n)
  have hA : (√(n : ℝ))⁻¹ * Mb n ω ≤ |Mb n ω - c| + (√(n : ℝ))⁻¹ * |c| := by
    calc (√(n : ℝ))⁻¹ * Mb n ω ≤ (√(n : ℝ))⁻¹ * (|Mb n ω - c| + |c|) :=
          mul_le_mul_of_nonneg_left hMb_le hs0
      _ ≤ |Mb n ω - c| + (√(n : ℝ))⁻¹ * |c| := by
          nlinarith [abs_nonneg (Mb n ω - c)]
  have hh2 : h ^ 2 / 2 ≤ K := by
    simp only [hK_def]; linarith [pow_nonneg (abs_nonneg h) 3]
  have hh3 : |h| ^ 3 ≤ K := by
    simp only [hK_def]; nlinarith [sq_nonneg h]
  have hh30 : 0 ≤ |h| ^ 3 := pow_nonneg (abs_nonneg h) 3
  have hBK : h ^ 2 / 2 * |B n ω - I| ≤ K * (ε / (3 * K)) :=
    mul_le_mul hh2 hc1.le (abs_nonneg _) hK.le
  have hMK : |h| ^ 3 * ((√(n : ℝ))⁻¹ * Mb n ω) ≤
      K * (ε / (3 * K)) + (√(n : ℝ))⁻¹ * (K * |c|) := by
    calc |h| ^ 3 * ((√(n : ℝ))⁻¹ * Mb n ω) ≤ |h| ^ 3 * (|Mb n ω - c| + (√(n : ℝ))⁻¹ * |c|) :=
          mul_le_mul_of_nonneg_left hA hh30
      _ ≤ K * (ε / (3 * K) + (√(n : ℝ))⁻¹ * |c|) :=
          mul_le_mul hh3 (by linarith) (by positivity) hK.le
      _ = K * (ε / (3 * K)) + (√(n : ℝ))⁻¹ * (K * |c|) := by ring
  have hKε : K * (ε / (3 * K)) = ε / 3 := by field_simp
  have : |F n ω + h ^ 2 * I / 2| < ε := by linarith
  exact absurd hω (not_le.2 this)

omit [IsProbabilityMeasure P] in
/-- A sum of two sequences tending to `0` in probability tends to `0` in probability. -/
private theorem tendstoInMeasure_add_zero'' {U V : ℕ → Ω → ℝ}
    (hU : TendstoInMeasure P U atTop 0) (hV : TendstoInMeasure P V atTop 0) :
    TendstoInMeasure P (fun i ω => U i ω + V i ω) atTop 0 := by
  rw [tendstoInMeasure_iff_norm] at hU hV ⊢
  intro ε hε
  have h2 := (hU (ε / 2) (by positivity)).add (hV (ε / 2) (by positivity))
  rw [add_zero] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun _ => zero_le)
    fun i => (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  simp only [Set.mem_ofPred_eq, Pi.zero_apply, sub_zero, Real.norm_eq_abs] at hω ⊢
  by_contra h
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at h
  linarith [abs_add_le (U i ω) (V i ω)]

/-- **Wilks' expansion for a triangular array.** Let `X n i` be random variables (row `n` is the
sample of size `n`) and `θ̂ₙ` estimators that solve the likelihood equation
`∑_{i<n} ∂_θ log p θ (X n i) = 0` with probability tending to one and converge to `θ₀` in
probability. Suppose that on the ball of radius `δ > 0` about `θ₀` the log-likelihood is
differentiable in `θ`, the score is twice differentiable, and `|∂³_θ log p θ x| ≤ M x`. Assume
the laws of large numbers `-(n⁻¹ ∑_{i<n} ∂²_θ log p θ₀ (X n i)) → I` with `I > 0` and
`n⁻¹ ∑_{i<n} M (X n i) → c` in probability, and that the normalized score
`n^{-1/2} ∑_{i<n} ∂_θ log p θ₀ (X n i)` converges in distribution to `Y`. Then
`2 (ℓₙ(θ̂ₙ) - ℓₙ(θ₀)) → Y² / I` in distribution, where `ℓₙ θ = ∑_{i<n} log p θ (X n i)`.

No independence or distributional assumption on the rows is made: they enter only through the
three limit hypotheses. The positivity of `p` is not used either: the expansion holds for any
criterion `log p θ x` with these derivatives. For i.i.d. rows with law `p θ₀ ν` this is Wilks'
theorem; under local alternatives it gives the local power
(`tendstoInDistribution_two_mul_logLikelihood_sub_local`).

Source: Wilks (1938); van der Vaart (1998), Theorem 5.41 and ch. 16. -/
theorem tendstoInDistribution_two_mul_logLikelihood_sub_of_triangular
    {p : ℝ → 𝓧 → ℝ} {θ₀ δ I c : ℝ} (hδ : 0 < δ) (hI : 0 < I)
    (hp_meas : Measurable (Function.uncurry p))
    (hℓ_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => Real.log (p t x)) θ)
    (hs_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => score p t x) θ)
    (hs'_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      DifferentiableAt ℝ (fun t => deriv (fun s => score p s x) t) θ)
    {M : 𝓧 → ℝ} (hM : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      |deriv (fun t => deriv (fun s => score p s x) t) θ| ≤ M x)
    {X : ℕ → ℕ → Ω → 𝓧} (hX : ∀ n i, AEMeasurable (X n i) P)
    {θhat : ℕ → Ω → ℝ} (hθ_meas : ∀ n, AEMeasurable (θhat n) P)
    (hroot : Tendsto
      (fun n => P {ω | ∑ i ∈ Finset.range n, score p (θhat n ω) (X n i ω) ≠ 0}) atTop (𝓝 0))
    (hcons : TendstoInMeasure P θhat atTop (fun _ => θ₀))
    {Y : Ω' → ℝ}
    (hA : TendstoInDistribution
      (fun (n : ℕ) ω => (√n)⁻¹ * ∑ i ∈ Finset.range n, score p θ₀ (X n i ω)) atTop Y
      (fun _ => P) P')
    (hB : TendstoInMeasure P
      (fun (n : ℕ) ω => -((∑ i ∈ Finset.range n, deriv (fun t => score p t (X n i ω)) θ₀) / n))
      atTop (fun _ => I))
    (hB_meas : ∀ n : ℕ, AEMeasurable
      (fun ω => -((∑ i ∈ Finset.range n, deriv (fun t => score p t (X n i ω)) θ₀) / n)) P)
    (hMb : TendstoInMeasure P (fun (n : ℕ) ω => (∑ i ∈ Finset.range n, M (X n i ω)) / n)
      atTop (fun _ => c))
    (hMb_meas : ∀ n : ℕ, AEMeasurable (fun ω => (∑ i ∈ Finset.range n, M (X n i ω)) / n) P) :
    TendstoInDistribution
      (fun (n : ℕ) ω => 2 * ∑ i ∈ Finset.range n,
        (Real.log (p (θhat n ω) (X n i ω)) - Real.log (p θ₀ (X n i ω))))
      atTop (fun ω => Y ω ^ 2 / I) (fun _ => P) P' := by
  have hθ₀ : θ₀ ∈ Metric.ball θ₀ δ := Metric.mem_ball_self hδ
  have hM0 : ∀ x, 0 ≤ M x := fun x => (abs_nonneg _).trans (hM x θ₀ hθ₀)
  have hI0 : I ≠ 0 := hI.ne'
  set ψ' : 𝓧 → ℝ := fun x => deriv (fun t => score p t x) θ₀ with hψ'_def
  set A : ℕ → Ω → ℝ := fun n ω => (√n)⁻¹ * ∑ i ∈ Finset.range n, score p θ₀ (X n i ω)
    with hA_def
  set B : ℕ → Ω → ℝ := fun n ω => -((∑ i ∈ Finset.range n, ψ' (X n i ω)) / n) with hB_def
  set Mb : ℕ → Ω → ℝ := fun n ω => (∑ i ∈ Finset.range n, M (X n i ω)) / n with hMb_def
  set T : ℕ → Ω → ℝ := fun n ω => √n * (θhat n ω - θ₀) with hT_def
  set η : ℕ → Ω → ℝ := fun n ω => |B n ω - I| + |θhat n ω - θ₀| * Mb n ω with hη_def
  have hT_meas : ∀ n, AEMeasurable (T n) P := fun n => ((hθ_meas n).sub_const _).const_mul _
  have hη_meas : ∀ n, AEMeasurable (η n) P := fun n =>
    (continuous_abs.measurable.comp_aemeasurable ((hB_meas n).sub_const _)).add
      ((continuous_abs.measurable.comp_aemeasurable ((hθ_meas n).sub_const _)).mul (hMb_meas n))
  have hBI : TendstoInMeasure P (fun n ω => |B n ω - I|) atTop 0 := by
    rw [tendstoInMeasure_iff_norm] at hB ⊢
    simpa using hB
  have hdθ : TendstoInMeasure P (fun n ω => |θhat n ω - θ₀|) atTop 0 := by
    rw [tendstoInMeasure_iff_norm] at hcons ⊢
    simpa using hcons
  have hrem : TendstoInMeasure P (fun n ω => |θhat n ω - θ₀| * Mb n ω) atTop 0 := by
    have h := (hMb.tendstoInDistribution_of_aemeasurable hMb_meas aemeasurable_const
      ).mul_tendstoInMeasure_zero hdθ
      (fun n => continuous_abs.measurable.comp_aemeasurable ((hθ_meas n).sub_const _))
    simpa only [mul_comm] using h
  have hη : TendstoInMeasure P η atTop 0 := tendstoInMeasure_add_zero'' hBI hrem
  -- the good events
  set G : ℕ → Set Ω := fun n =>
    {ω | ∑ i ∈ Finset.range n, score p (θhat n ω) (X n i ω) = 0} ∩
      {ω | |θhat n ω - θ₀| < δ} ∩ {ω | η n ω ≤ I / 2} with hG_def
  have hG : Tendsto (fun n => P (G n)ᶜ) atTop (𝓝 0) := by
    have h1 := (tendstoInMeasure_iff_dist.1 hcons) δ hδ
    have h2 := (tendstoInMeasure_iff_norm.1 hη) (I / 2) (by positivity)
    have h3 := (hroot.add h1).add h2
    simp only [add_zero] at h3
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun _ => zero_le)
      fun n => ?_
    refine (measure_mono fun ω hω => ?_).trans
      ((measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _))
    simp only [hG_def, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_ofPred_eq, not_and_or,
      not_lt, not_le] at hω
    simp only [Set.mem_union, Set.mem_ofPred_eq, Real.dist_eq, Pi.zero_apply, sub_zero,
      Real.norm_eq_abs]
    rcases hω with (h | h) | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (h.le.trans (le_abs_self _))
  -- step 1: `T - A / I → 0` in probability
  have hbound : ∀ n, ∀ ω ∈ G n, |T n ω - A n ω / I| ≤ (2 / I ^ 2 * |A n ω|) * η n ω := by
    intro n ω hω
    obtain ⟨⟨hroot', hclose⟩, hsmall⟩ := hω
    simp only [Set.mem_ofPred_eq] at hroot' hclose hsmall
    set d := θhat n ω - θ₀
    have hball : θhat n ω ∈ Metric.ball θ₀ δ := by
      rw [Metric.mem_ball, Real.dist_eq]; exact hclose
    have htay : |∑ i ∈ Finset.range n, score p θ₀ (X n i ω) +
        d * ∑ i ∈ Finset.range n, ψ' (X n i ω)| ≤ (∑ i ∈ Finset.range n, M (X n i ω)) * d ^ 2 := by
      have e : ∑ i ∈ Finset.range n, score p θ₀ (X n i ω) +
          d * ∑ i ∈ Finset.range n, ψ' (X n i ω) =
          -∑ i ∈ Finset.range n, (score p (θhat n ω) (X n i ω) - score p θ₀ (X n i ω) -
            d * ψ' (X n i ω)) := by
        simp only [Finset.sum_sub_distrib, hroot', Finset.mul_sum]; ring
      rw [e, abs_neg, Finset.sum_mul]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      exact abs_sub_sub_mul_deriv_le' (f := fun t => score p t (X n i ω)) (hs_diff (X n i ω))
        (hs'_diff (X n i ω)) (hM (X n i ω)) hball
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hT_def, hA_def]
    have hr : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hMb0 : 0 ≤ Mb n ω := div_nonneg (Finset.sum_nonneg fun i _ => hM0 _) (Nat.cast_nonneg n)
    have hATB : |A n ω - T n ω * B n ω| ≤ |T n ω| * (|d| * Mb n ω) := by
      have e1 : A n ω - T n ω * B n ω = (∑ i ∈ Finset.range n, score p θ₀ (X n i ω) +
          d * ∑ i ∈ Finset.range n, ψ' (X n i ω)) / √(n : ℝ) := by
        simp only [hA_def, hT_def, hB_def]
        obtain ⟨r, hr_def⟩ : ∃ r, r = √(n : ℝ) := ⟨_, rfl⟩
        have hn' : (n : ℝ) = r ^ 2 := by rw [hr_def, Real.sq_sqrt (Nat.cast_nonneg n)]
        rw [← hr_def] at hr ⊢
        rw [hn']
        field_simp
        ring
      have e2 : |T n ω| * (|d| * Mb n ω) =
          (∑ i ∈ Finset.range n, M (X n i ω)) * d ^ 2 / √(n : ℝ) := by
        simp only [hT_def, hMb_def, abs_mul, abs_of_pos hr]
        obtain ⟨r, hr_def⟩ : ∃ r, r = √(n : ℝ) := ⟨_, rfl⟩
        have hn' : (n : ℝ) = r ^ 2 := by rw [hr_def, Real.sq_sqrt (Nat.cast_nonneg n)]
        rw [← hr_def] at hr ⊢
        rw [hn', ← sq_abs d]
        field_simp
        ring
      rw [e1, e2, abs_div, abs_of_pos hr]
      exact div_le_div_of_nonneg_right htay hr.le
    have hATJ : |A n ω - T n ω * I| ≤ |T n ω| * η n ω := by
      have : A n ω - T n ω * I = (A n ω - T n ω * B n ω) + T n ω * (B n ω - I) := by ring
      rw [this]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, hη_def]
      simp only
      nlinarith [abs_nonneg (T n ω), abs_nonneg (B n ω - I)]
    have hη0 : 0 ≤ η n ω := add_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) hMb0)
    have hJpos : 0 < |I| := abs_pos.2 hI0
    have hsmall' : η n ω ≤ |I| / 2 := by rwa [abs_of_pos hI]
    have hTle : |T n ω| * |I| ≤ 2 * |A n ω| := by
      have h1 : |T n ω * I| ≤ |A n ω| + |A n ω - T n ω * I| := by
        have := abs_sub_abs_le_abs_sub (T n ω * I) (A n ω)
        rw [abs_sub_comm (T n ω * I)] at this
        linarith
      rw [abs_mul] at h1
      nlinarith [abs_nonneg (T n ω)]
    have e : T n ω - A n ω / I = -(A n ω - T n ω * I) / I := by field_simp; ring
    rw [e, abs_div, abs_neg, div_le_iff₀ hJpos]
    have hJ2 : I ^ 2 = |I| * |I| := by rw [← sq_abs, sq]
    calc |A n ω - T n ω * I| ≤ |T n ω| * η n ω := hATJ
      _ ≤ 2 / I ^ 2 * |A n ω| * η n ω * |I| := by
        rw [hJ2]
        have : |T n ω| ≤ 2 * |A n ω| / |I| := by rw [le_div_iff₀ hJpos]; exact hTle
        calc |T n ω| * η n ω ≤ 2 * |A n ω| / |I| * η n ω :=
              mul_le_mul_of_nonneg_right this hη0
          _ = 2 / (|I| * |I|) * |A n ω| * η n ω * |I| := by field_simp
  have hV : TendstoInMeasure P (fun n ω => (2 / I ^ 2 * |A n ω|) * η n ω) atTop 0 := by
    have hA' := hA.continuous_comp (g := fun x => 2 / I ^ 2 * |x|) (by fun_prop)
    exact hA'.mul_tendstoInMeasure_zero hη hη_meas
  have hdiff : TendstoInMeasure P (fun n ω => T n ω - A n ω / I) atTop 0 :=
    tendstoInMeasure_zero_of_abs_le hV hG fun n ω hω => hbound n ω hω
  -- step 2: `T → Y / I` in distribution
  have hAJ : TendstoInDistribution (fun n ω => A n ω / I) atTop (fun ω => Y ω / I)
      (fun _ => P) P' := hA.continuous_comp (g := fun x => x / I) (by fun_prop)
  have hT : TendstoInDistribution T atTop (fun ω => Y ω / I) (fun _ => P) P' :=
    tendstoInDistribution_of_tendstoInMeasure_sub T _ hAJ hdiff hT_meas
  -- step 3: quadratic expansion `2 (ℓₙ(θ̂ₙ) - ℓₙ(θ₀)) - T² I → 0`
  set G' : ℕ → Set Ω := fun n =>
    {ω | ∑ i ∈ Finset.range n, score p (θhat n ω) (X n i ω) = 0} ∩
      {ω | |θhat n ω - θ₀| < δ} with hG'_def
  have hG' : Tendsto (fun n => P (G' n)ᶜ) atTop (𝓝 0) := by
    have h1 := (tendstoInMeasure_iff_dist.1 hcons) δ hδ
    have h3 := hroot.add h1
    rw [add_zero] at h3
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun _ => zero_le)
      fun n => (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
    simp only [hG'_def, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_ofPred_eq, not_and_or,
      not_lt] at hω
    simp only [Set.mem_union, Set.mem_ofPred_eq, Real.dist_eq]
    exact hω
  have hbound' : ∀ n, ∀ ω ∈ G' n,
      |2 * ∑ i ∈ Finset.range n,
          (Real.log (p (θhat n ω) (X n i ω)) - Real.log (p θ₀ (X n i ω))) -
        T n ω ^ 2 * I| ≤ (2 * T n ω ^ 2) * η n ω := by
    intro n ω hω
    obtain ⟨hroot', hclose⟩ := hω
    simp only [Set.mem_ofPred_eq] at hroot' hclose
    have hball : θhat n ω ∈ Metric.ball θ₀ δ := by
      rw [Metric.mem_ball, Real.dist_eq]; exact hclose
    have hT2 : T n ω ^ 2 = n * (θhat n ω - θ₀) ^ 2 := by
      simp only [hT_def]; rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    rw [hT2]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hη_def]
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hSM : 0 ≤ ∑ i ∈ Finset.range n, M (X n i ω) := Finset.sum_nonneg fun i _ => hM0 _
    have htay : |-(∑ i ∈ Finset.range n,
          (Real.log (p (θhat n ω) (X n i ω)) - Real.log (p θ₀ (X n i ω)))) -
        (θhat n ω - θ₀) ^ 2 / 2 * ∑ i ∈ Finset.range n, ψ' (X n i ω)| ≤
          (∑ i ∈ Finset.range n, M (X n i ω)) * |θhat n ω - θ₀| ^ 3 := by
      have e : -(∑ i ∈ Finset.range n,
          (Real.log (p (θhat n ω) (X n i ω)) - Real.log (p θ₀ (X n i ω)))) -
            (θhat n ω - θ₀) ^ 2 / 2 * ∑ i ∈ Finset.range n, ψ' (X n i ω) =
          ∑ i ∈ Finset.range n, (Real.log (p θ₀ (X n i ω)) -
            Real.log (p (θhat n ω) (X n i ω)) -
            (θ₀ - θhat n ω) * score p (θhat n ω) (X n i ω) -
              (θ₀ - θhat n ω) ^ 2 / 2 * ψ' (X n i ω)) := by
        simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hroot', mul_zero]
        ring
      rw [e, Finset.sum_mul]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      exact abs_taylor_two_le' (f := fun t => Real.log (p t (X n i ω)))
        (f₁ := fun t => score p t (X n i ω))
        (f₂ := fun t => deriv (fun s => score p s (X n i ω)) t)
        (f₃ := fun t => deriv (fun t => deriv (fun s => score p s (X n i ω)) t) t)
        (fun t ht => (hℓ_diff _ t ht).hasDerivAt) (fun t ht => (hs_diff _ t ht).hasDerivAt)
        (fun t ht => (hs'_diff _ t ht).hasDerivAt) (fun t ht => hM _ t ht) hball
    generalize hL : ∑ i ∈ Finset.range n,
      (Real.log (p (θhat n ω) (X n i ω)) - Real.log (p θ₀ (X n i ω))) = L at htay
    generalize hS : ∑ i ∈ Finset.range n, ψ' (X n i ω) = S at htay
    generalize hSM' : ∑ i ∈ Finset.range n, M (X n i ω) = SM at htay hSM
    have hB' : B n ω = -S / n := by simp only [hB_def, hS]; ring
    have hMb' : Mb n ω = SM / n := by simp only [hMb_def, hSM']
    have hη' : η n ω = |B n ω - I| + |θhat n ω - θ₀| * Mb n ω := rfl
    rw [hη', hB', hMb']
    generalize θhat n ω - θ₀ = d at htay ⊢
    have h1 : |-S / n - I| = |S + n * I| / n := by
      rw [show -S / n - I = -(S + n * I) / n by field_simp; ring, abs_div, abs_neg,
        abs_of_pos hn']
    rw [h1]
    have e2 : 2 * L - n * d ^ 2 * I = -2 * (-L - d ^ 2 / 2 * S) - d ^ 2 * (S + n * I) := by ring
    have e3 : 2 * (n * d ^ 2) * (|S + n * I| / n + |d| * (SM / n)) =
        2 * d ^ 2 * |S + n * I| + 2 * SM * (d ^ 2 * |d|) := by field_simp
    have e4 : |d| ^ 3 = d ^ 2 * |d| := by rw [pow_succ, sq_abs]
    rw [e2, e3]
    calc |-2 * (-L - d ^ 2 / 2 * S) - d ^ 2 * (S + n * I)|
        ≤ 2 * |-L - d ^ 2 / 2 * S| + d ^ 2 * |S + n * I| := by
          refine (abs_sub _ _).trans ?_
          rw [abs_mul, abs_mul, abs_neg, abs_two, abs_of_nonneg (sq_nonneg d)]
      _ ≤ 2 * (SM * |d| ^ 3) + d ^ 2 * |S + n * I| := by linarith
      _ ≤ 2 * d ^ 2 * |S + n * I| + 2 * SM * (d ^ 2 * |d|) := by
          rw [e4]; nlinarith [mul_nonneg (sq_nonneg d) (abs_nonneg (S + n * I))]
  have hV' : TendstoInMeasure P (fun n ω => (2 * T n ω ^ 2) * η n ω) atTop 0 :=
    (hT.continuous_comp (g := fun x => 2 * x ^ 2) (by fun_prop)).mul_tendstoInMeasure_zero hη
      hη_meas
  have hQ := tendstoInMeasure_zero_of_abs_le hV' hG' hbound'
  -- step 4: conclusion
  have hTI : TendstoInDistribution (fun n ω => T n ω ^ 2 * I) atTop (fun ω => Y ω ^ 2 / I)
      (fun _ => P) P' := by
    refine (hT.continuous_comp (g := fun x => x ^ 2 * I) (by fun_prop)).congr
      (fun n => ae_of_all _ fun ω => rfl) (ae_of_all _ fun ω => ?_)
    simp only [Function.comp_apply]
    field_simp
  have hp0 : Measurable (p θ₀) := hp_meas.comp (measurable_const.prodMk measurable_id)
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hTI hQ fun n => ?_
  refine (Finset.aemeasurable_fun_sum _ fun i _ => ?_).const_mul 2
  exact ((Real.measurable_log.comp hp_meas).comp_aemeasurable ((hθ_meas n).prodMk (hX n i))).sub
    ((Real.measurable_log.comp hp0).comp_aemeasurable (hX n i))


/-- **Local power of the likelihood-ratio test.** Let row `n` of the triangular array
`X n 0, X n 1, …` be i.i.d. with law `p θₙ ν`, `θₙ = θ₀ + h / √n`, under the Cramér conditions
at `θ₀` of `LikelihoodRatioTests.tendstoInDistribution_two_mul_logLikelihood_sub` (all moment
and envelope conditions are under the null law `p θ₀ ν`). If `θ̂ₙ` solves the likelihood
equation for row `n` with probability tending to one and `θ̂ₙ → θ₀` in probability, then
`2 (ℓₙ(θ̂ₙ) - ℓₙ(θ₀))` converges in distribution to the law of `(Z + h √I(θ₀))²`,
`Z ~ N(0, 1)` (noncentral `χ²₁` with noncentrality `h² I(θ₀)`). For `h = 0` this is Wilks'
theorem for a triangular array.

The row `n = 0` is irrelevant for the limit; with Lean's `h / √0 = 0` its law is `p θ₀ ν`, which
makes `p θ₀ ν` a probability measure. No normalization `∫ p θ dν = 1` is assumed otherwise:
the laws `p θₙ ν` are probability measures because they are laws of random variables.

Source: van der Vaart (1998), ch. 16 (local power), via local asymptotic normality (ch. 7) and
Le Cam's first and third lemmas (ch. 6). -/
theorem tendstoInDistribution_two_mul_logLikelihood_sub_local
    {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {θ₀ δ h : ℝ} (hδ : 0 < δ)
    (hp_pos : ∀ θ x, 0 < p θ x) (hp_meas : Measurable (Function.uncurry p))
    {X : ℕ → ℕ → Ω → 𝓧}
    (hX_law : ∀ n i, HasLaw (X n i) (lawOf ν p (θ₀ + h / √n)) P)
    (hX_indep : ∀ n, iIndepFun (X n) P)
    (hℓ_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => Real.log (p t x)) θ)
    (hs_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => score p t x) θ)
    (hs'_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      DifferentiableAt ℝ (fun t => deriv (fun s => score p s x) t) θ)
    {M : 𝓧 → ℝ} (hM_meas : Measurable M) (hM_int : Integrable M (lawOf ν p θ₀))
    (hM : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      |deriv (fun t => deriv (fun s => score p s x) t) θ| ≤ M x)
    (hs_meas : Measurable (score p θ₀))
    (hs_sq : Integrable (fun x => score p θ₀ x ^ 2) (lawOf ν p θ₀))
    (hs_mean : ∫ x, score p θ₀ x ∂lawOf ν p θ₀ = 0)
    (hs'_meas : Measurable fun x => deriv (fun t => score p t x) θ₀)
    (hs'_int : Integrable (fun x => deriv (fun t => score p t x) θ₀) (lawOf ν p θ₀))
    (h_info : ∫ x, deriv (fun t => score p t x) θ₀ ∂lawOf ν p θ₀ = -fisherInformation ν p θ₀)
    (hI_pos : 0 < fisherInformation ν p θ₀)
    {θhat : ℕ → Ω → ℝ} (hθ_meas : ∀ n, AEMeasurable (θhat n) P)
    (hroot : Tendsto
      (fun n => P {ω | ∑ i ∈ Finset.range n, score p (θhat n ω) (X n i ω) ≠ 0}) atTop (𝓝 0))
    (hcons : TendstoInMeasure P θhat atTop (fun _ => θ₀))
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z ((gaussianReal (h * √(fisherInformation ν p θ₀)) 1).map
      (fun x : ℝ => x ^ 2)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => 2 * ∑ i ∈ Finset.range n,
        (Real.log (p (θhat n ω) (X n i ω)) - Real.log (p θ₀ (X n i ω))))
      atTop Z (fun _ => P) P' := by
  classical
  set I := fisherInformation ν p θ₀ with hI_def
  set ψ' : 𝓧 → ℝ := fun x => deriv (fun t => score p t x) θ₀ with hψ'_def
  have hpθ : ∀ θ, Measurable (p θ) := fun θ =>
    hp_meas.comp (measurable_const.prodMk measurable_id)
  have hp_diff : ∀ x, DifferentiableAt ℝ (fun t => p t x) θ₀ := fun x => by
    have e : (fun t => p t x) = fun t => Real.exp (Real.log (p t x)) := by
      funext t; rw [Real.exp_log (hp_pos t x)]
    rw [e]; exact (hℓ_diff x θ₀ (Metric.mem_ball_self hδ)).exp
  -- the laws
  have hX0 : ∀ i, HasLaw (X 0 i) (lawOf ν p θ₀) P := fun i => by
    simpa using hX_law 0 i
  have : IsProbabilityMeasure (lawOf ν p θ₀) :=
    (hX0 0).isProbabilityMeasure_iff.1 inferInstance
  have hμn : ∀ n : ℕ, IsProbabilityMeasure (lawOf ν p (θ₀ + h / √n)) := fun n =>
    (hX_law n 0).isProbabilityMeasure_iff.1 inferInstance
  set r : ℕ → 𝓧 → ℝ≥0∞ := fun n x => ENNReal.ofReal (p (θ₀ + h / √n) x / p θ₀ x) with hr_def
  have hr_meas : ∀ n, Measurable (r n) := fun n =>
    ((hpθ _).div (hpθ θ₀)).ennreal_ofReal
  have hdens : ∀ n, (lawOf ν p θ₀).withDensity (r n) = lawOf ν p (θ₀ + h / √n) := fun n => by
    rw [lawOf, lawOf, ← withDensity_mul ν (hpθ θ₀).ennreal_ofReal (hr_meas n)]
    congr 1
    funext x
    simp only [Pi.mul_apply, hr_def]
    rw [← ENNReal.ofReal_mul (hp_pos θ₀ x).le, mul_div_cancel₀ _ (hp_pos θ₀ x).ne']
  have hdens_prob : ∀ n, IsProbabilityMeasure ((lawOf ν p θ₀).withDensity (r n)) := fun n => by
    rw [hdens n]; infer_instance
  -- the null product space and the reweighted measures
  set P₀ : Measure (ℕ → 𝓧) := Measure.infinitePi fun _ : ℕ => lawOf ν p θ₀ with hP₀_def
  set Λ : ℕ → (ℕ → 𝓧) → ℝ := fun n x => ∑ i ∈ Finset.range n,
    (Real.log (p (θ₀ + h / √n) (x i)) - Real.log (p θ₀ (x i))) with hΛ_def
  have hΛ_meas : ∀ n, Measurable (Λ n) := fun n =>
    Finset.measurable_fun_sum _ fun i _ =>
      ((Real.measurable_log.comp (hpθ _)).comp (measurable_pi_apply i)).sub
        ((Real.measurable_log.comp (hpθ θ₀)).comp (measurable_pi_apply i))
  have hexpΛ : ∀ n, (fun x => ENNReal.ofReal (Real.exp (Λ n x))) =
      fun x => ∏ i ∈ Finset.range n, r n (x i) := fun n => by
    funext x
    simp only [hΛ_def, hr_def]
    rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.exp_pos _).le]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Real.exp_sub, Real.exp_log (hp_pos _ _), Real.exp_log (hp_pos _ _)]
  set Q : ℕ → Measure (ℕ → 𝓧) := fun n =>
    P₀.withDensity fun x => ENNReal.ofReal (Real.exp (Λ n x)) with hQ_def
  have hrestr : ∀ n : ℕ, Measurable fun (x : ℕ → 𝓧) (i : Fin n) => x i := fun n =>
    measurable_pi_iff.2 fun i => measurable_pi_apply _
  have hQmap : ∀ n : ℕ, (Q n).map (fun x (i : Fin n) => x i) =
      Measure.pi fun _ : Fin n => lawOf ν p (θ₀ + h / √n) := fun n => by
    simp only [hQ_def]
    rw [hexpΛ n, map_withDensity_infinitePi_prod (hr_meas n) n, hdens n]
  have hQ_prob : ∀ n, IsProbabilityMeasure (Q n) := fun n => by
    constructor
    have h1 := congrArg (fun m : Measure (Fin n → 𝓧) => m Set.univ) (hQmap n)
    simp only [Measure.map_apply (hrestr n) MeasurableSet.univ, Set.preimage_univ,
      measure_univ] at h1
    exact h1
  -- the law of a row under the alternative
  have hrow : ∀ n : ℕ, P.map (fun ω (i : Fin n) => X n i ω) = (Q n).map fun x (i : Fin n) => x i :=
    fun n => by
    rw [hQmap n]
    have hind : iIndepFun (fun (i : Fin n) => X n i) P :=
      (hX_indep n).precomp Fin.val_injective
    rw [(iIndepFun_iff_map_fun_eq_pi_map (f := fun (i : Fin n) => X n i) (μ := P)
      fun i => (hX_law n i).aemeasurable).1 hind]
    congr 1
    funext i
    exact (hX_law n i).map_eq
  have hrow_meas : ∀ n : ℕ, AEMeasurable (fun ω (i : Fin n) => X n i ω) P := fun n =>
    AEMeasurable.of_eval fun i => (hX_law n i).aemeasurable
  have htransfer : ∀ (n : ℕ) (F : (Fin n → 𝓧) → ℝ), Measurable F →
      P.map (fun ω => F fun i => X n i ω) = (Q n).map fun x => F fun i => x i := fun n F hF => by
    have e1 : (fun ω => F fun i : Fin n => X n i ω) = F ∘ fun ω (i : Fin n) => X n i ω := rfl
    have e2 : (fun x : ℕ → 𝓧 => F fun i : Fin n => x i) = F ∘ fun x (i : Fin n) => x i := rfl
    rw [e1, e2, ← AEMeasurable.map_map_of_aemeasurable hF.aemeasurable (hrow_meas n),
      ← Measure.map_map hF (hrestr n), hrow n]
  -- the null asymptotics
  have hY_law : ∀ i, HasLaw (fun x : ℕ → 𝓧 => x i) (lawOf ν p θ₀) P₀ := fun i =>
    ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval _ i⟩
  have hY_indep : iIndepFun (fun i (x : ℕ → 𝓧) => x i) P₀ :=
    iIndepFun_infinitePi (P := fun _ : ℕ => lawOf ν p θ₀) (X := fun _ => id)
      fun _ => measurable_id
  have hS : TendstoInDistribution
      (fun (n : ℕ) (x : ℕ → 𝓧) => (√n)⁻¹ * ∑ i ∈ Finset.range n, score p θ₀ (x i)) atTop id
      (fun _ => P₀) (gaussianReal 0 I.toNNReal) :=
    tendstoInDistribution_score (fun x => hp_pos θ₀ x) (hpθ θ₀) hp_diff hY_law hY_indep hs_meas
      hs_sq hs_mean HasLaw.id
  have hB0 : TendstoInMeasure P₀
      (fun (n : ℕ) (x : ℕ → 𝓧) => -((∑ i ∈ Finset.range n, ψ' (x i)) / n)) atTop
      (fun _ => I) :=
    LikelihoodRatioTests.tendstoInMeasure_observedInformation hY_law hY_indep hs'_meas
      hs'_int h_info
  have hMb0 : TendstoInMeasure P₀ (fun (n : ℕ) (x : ℕ → 𝓧) => (∑ i ∈ Finset.range n, M (x i)) / n)
      atTop (fun _ => ∫ x, M x ∂lawOf ν p θ₀) := by
    have hident : ∀ i, IdentDistrib (M ∘ fun x : ℕ → 𝓧 => x i) (M ∘ fun x => x 0) P₀ P₀ :=
      fun i => (⟨(hY_law i).aemeasurable, (hY_law 0).aemeasurable,
        (hY_law i).map_eq.trans (hY_law 0).map_eq.symm⟩ :
          IdentDistrib (fun x : ℕ → 𝓧 => x i) (fun x => x 0) P₀ P₀).comp hM_meas
    have h := strong_law_ae_real (fun i => M ∘ fun x : ℕ → 𝓧 => x i)
      ((hY_law 0).integrable_comp hM_int)
      (fun i j hij => (hY_indep.comp (fun _ => M) (fun _ => hM_meas)).indepFun hij) hident
    rw [(hY_law 0).integral_comp hM_meas.aestronglyMeasurable] at h
    exact tendstoInMeasure_of_tendsto_ae (fun n => ((Finset.measurable_fun_sum _ fun i _ =>
      hM_meas.comp (measurable_pi_apply i)).div_const _).aestronglyMeasurable) h
  have hLAN := tendstoInMeasure_logLikelihoodRatio_sub (h := h) hδ hℓ_diff hs_diff hs'_diff hM
    hB0 hMb0
  have hIv : ((I.toNNReal : ℝ≥0) : ℝ) = I := Real.coe_toNNReal _ hI_pos.le
  have hLAN' : TendstoInMeasure P₀
      (fun n x => Λ n x - h * ((√n)⁻¹ * ∑ i ∈ Finset.range n, score p θ₀ (x i))) atTop
      (fun _ => -(h ^ 2 * (I.toNNReal : ℝ) / 2)) := by
    rw [hIv]; exact hLAN
  have hcont := isContiguous_withDensity_exp hΛ_meas hS hLAN'
  have hthird := tendstoInDistribution_withDensity_exp hΛ_meas hS hLAN'
  -- transfer to the alternative
  have hmeas_tr : ∀ (g : 𝓧 → ℝ), Measurable g → ∀ n : ℕ,
      Measurable fun y : Fin n → 𝓧 => ∑ i : Fin n, g (y i) := fun g hg n =>
    Finset.measurable_fun_sum _ fun i _ => hg.comp (measurable_pi_apply i)
  have htr_meas : ∀ (g : 𝓧 → ℝ) (a : ℕ → ℝ) (b : ℝ), Measurable g →
      TendstoInMeasure P₀ (fun (n : ℕ) (x : ℕ → 𝓧) => a n * ∑ i ∈ Finset.range n, g (x i))
        atTop (fun _ => b) →
      TendstoInMeasure P (fun (n : ℕ) ω => a n * ∑ i ∈ Finset.range n, g (X n i ω))
        atTop (fun _ => b) := fun g a b hg h0 => by
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    have hT : ∀ n, Measurable fun (x : ℕ → 𝓧) => a n * ∑ i ∈ Finset.range n, g (x i) :=
      fun n => (Finset.measurable_fun_sum _ fun i _ =>
        hg.comp (measurable_pi_apply i)).const_mul _
    have hQ0 := hcont.tendsto_measure_abs_sub_ge hT h0 hε
    refine hQ0.congr fun n => ?_
    set F : (Fin n → 𝓧) → ℝ := fun y => a n * ∑ i : Fin n, g (y i) with hF_def
    have hF : Measurable F := (hmeas_tr g hg n).const_mul _
    have hS_meas : MeasurableSet {y : ℝ | ε ≤ |y - b|} :=
      measurableSet_le measurable_const (by fun_prop)
    have h1 := congrArg (fun m : Measure ℝ => m {y : ℝ | ε ≤ |y - b|}) (htransfer n F hF)
    rw [Measure.map_apply_of_aemeasurable (f := fun ω => F fun i => X n i ω)
        (hF.comp_aemeasurable (hrow_meas n)) hS_meas,
      Measure.map_apply (f := fun (x : ℕ → 𝓧) => F fun i : Fin n => x i) (hF.comp (hrestr n))
        hS_meas] at h1
    simp only [Real.norm_eq_abs]
    convert h1.symm using 2 <;> ext <;>
      simp [hF_def, Finset.sum_range]
  have hB : TendstoInMeasure P
      (fun (n : ℕ) ω => -((∑ i ∈ Finset.range n, ψ' (X n i ω)) / n)) atTop (fun _ => I) := by
    have h0 : TendstoInMeasure P₀ (fun (n : ℕ) (x : ℕ → 𝓧) =>
        (-(n : ℝ)⁻¹) * ∑ i ∈ Finset.range n, ψ' (x i)) atTop (fun _ => I) := by
      refine hB0.congr_left fun n => ae_of_all _ fun x => ?_
      ring
    refine (htr_meas ψ' (fun n => -(n : ℝ)⁻¹) I hs'_meas h0).congr_left fun n =>
      ae_of_all _ fun ω => ?_
    ring
  have hMb : TendstoInMeasure P (fun (n : ℕ) ω => (∑ i ∈ Finset.range n, M (X n i ω)) / n)
      atTop (fun _ => ∫ x, M x ∂lawOf ν p θ₀) := by
    have h0 : TendstoInMeasure P₀ (fun (n : ℕ) (x : ℕ → 𝓧) =>
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, M (x i)) atTop (fun _ => ∫ x, M x ∂lawOf ν p θ₀) := by
      refine hMb0.congr_left fun n => ae_of_all _ fun x => ?_
      ring
    refine (htr_meas M (fun n => (n : ℝ)⁻¹) _ hM_meas h0).congr_left fun n =>
      ae_of_all _ fun ω => ?_
    ring
  have hXm : ∀ n i, AEMeasurable (X n i) P := fun n i => (hX_law n i).aemeasurable
  have hA : TendstoInDistribution
      (fun (n : ℕ) ω => (√n)⁻¹ * ∑ i ∈ Finset.range n, score p θ₀ (X n i ω)) atTop id
      (fun _ => P) (gaussianReal (h * I.toNNReal) I.toNNReal) := by
    refine ⟨fun n => (Finset.aemeasurable_fun_sum _ fun i _ =>
      hs_meas.comp_aemeasurable (hXm n i)).const_mul _, aemeasurable_id, ?_⟩
    · refine hthird.tendsto.congr fun n => ?_
      apply Subtype.ext
      have h1 := htransfer n (fun y => (√n)⁻¹ * ∑ i : Fin n, score p θ₀ (y i))
        ((hmeas_tr _ hs_meas n).const_mul _)
      simp only [Finset.sum_range]
      exact h1.symm
  have hLRT := tendstoInDistribution_two_mul_logLikelihood_sub_of_triangular hδ hI_pos hp_meas
    hℓ_diff hs_diff hs'_diff hM hXm hθ_meas hroot hcons hA hB
    (fun n => ((Finset.aemeasurable_fun_sum _ fun i _ =>
      hs'_meas.comp_aemeasurable (hXm n i)).div_const _).neg) hMb
    (fun n => (Finset.aemeasurable_fun_sum _ fun i _ =>
      hM_meas.comp_aemeasurable (hXm n i)).div_const _)
  -- identify the limit law
  have hlaw : (gaussianReal (h * I.toNNReal) I.toNNReal).map (fun y => id y ^ 2 / I) =
      (gaussianReal (h * √I) 1).map (fun x : ℝ => x ^ 2) := by
    have hsI : 0 < √I := Real.sqrt_pos.2 hI_pos
    have e : (fun y : ℝ => id y ^ 2 / I) = (fun x : ℝ => x ^ 2) ∘ ((√I)⁻¹ * ·) := by
      funext y
      simp only [id, Function.comp_apply, mul_pow, inv_pow, Real.sq_sqrt hI_pos.le]
      ring
    rw [e, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul]
    congr 2
    · rw [hIv]
      field_simp
      rw [Real.sq_sqrt hI_pos.le]
      ring
    · ext
      simp only [NNReal.coe_mul, NNReal.coe_mk, inv_pow, hIv, NNReal.coe_one,
        Real.sq_sqrt hI_pos.le]
      field_simp
  exact
    { forall_aemeasurable := hLRT.forall_aemeasurable
      aemeasurable_limit := hZ.aemeasurable
      tendsto := by
        convert hLRT.tendsto using 2
        exact congrArg 𝓝 (Subtype.ext (by simp only; rw [hZ.map_eq, ← hlaw])) }


end MathlibExt.Probability.Statistics.LikelihoodRatioLocalPower
