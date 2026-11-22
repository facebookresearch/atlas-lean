/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CramerLDPUpperBound
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The Cramér lower bound and Cramér's theorem in `ℝᵈ`

Let `X₀, X₁, …` be measurable i.i.d. random vectors in `ℝᵈ` on a probability space with
`E[exp ⟪t, X₀⟫] < ∞` for every `t`, and let `μₙ` be the law of the empirical mean
`(1/n) ∑_{i<n} Xᵢ`. This file proves the large deviation lower bound
`-inf_U Λ* ≤ liminf (1/n) log μₙ(U)` for open `U` and, combined with the upper bound and
goodness of `CramerLDPUpperBound`, Cramér's theorem `satisfiesLDP_empiricalMeanMeasureVec`.

## Proof idea

* At a gradient point `x = ∇Λ(θ)`, write `Sₙ = ∑_{i<n} Xᵢ` and tilt inside the expectation by
  `Wₙ = exp (⟪θ, Sₙ⟫ - n Λ(θ))`, which has mean `1`. On the ball `B(x, δ)`,
  `Wₙ ≤ exp (n (⟪θ, x⟫ + ‖θ‖ δ - Λ(θ)))`. Off the ball some coordinate of the mean leaves
  `(xⱼ - η, xⱼ + η)`, and the tilted mass of each such half-space is at most
  `exp (n (Λ(θ + s e) - Λ(θ) - s (⟪e, x⟫ + η)))`, exponentially small for a small `s > 0` by
  differentiability of `Λ` at `θ`. Hence `μₙ(B(x, δ)) ≥ exp (-n (⟪θ, x⟫ - Λ(θ) + ‖θ‖ δ)) / 2`
  eventually, and `⟪θ, x⟫ - Λ(θ) ≤ Λ*(x)`.
* For a general `x` with `Λ*(x) < ∞`, a maximiser `θ` of `t ↦ ⟪x, t⟫ - Λ(t) - ε ‖t‖² / 2`
  (which exists by coercivity) satisfies `∇Λ(θ) = x - ε θ` with `ε ‖θ‖ → 0`, so the gradient
  case applies at points converging to `x` without increasing the rate.
* `Λ` is differentiable by differentiation under the integral sign, dominated by finitely many
  exponential moments.

## Sources

S. R. S. Varadhan, *Large Deviations*, lecture notes, New York University, Spring 2010,
Section 1 (tilting proof in `ℝ`, https://math.nyu.edu/~varadhan/LDP/1-2.pdf); A. Dembo and
O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed., Section 2.2.

## Main results

* `le_liminf_log_empiricalMeanMeasureVec_ball`: the lower bound on small balls at gradient
  points.
* `le_liminf_log_empiricalMeanMeasureVec_of_differentiable`: the open-set lower bound for a
  differentiable `Λ`.
* `differentiable_logMGFVec`: `Λ` is differentiable.
* `le_liminf_log_empiricalMeanMeasureVec`: the open-set lower bound.
* `satisfiesLDP_empiricalMeanMeasureVec`: Cramér's theorem in `ℝᵈ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped InnerProductSpace ENNReal
open MathlibExt.Probability.LargeDeviationPrinciple
open MathlibExt.Probability.CramerUpperBound
open MathlibExt.Probability.CramerRateFunction
open MathlibExt.Probability.CramerLDPUpperBound

namespace MathlibExt.Probability.CramerLDPLowerBound

open MathlibExt.Probability.VaradhanIntegralLemma (coe_le_inv_mul_log_iff)

/-- **A one-sided slope bound from a derivative.** If `g` has derivative `g'` at `0` and
`η > 0`, then `g s - g 0 < s (g' + η)` for some `s > 0`. -/
theorem exists_pos_sub_lt_of_hasDerivAt {g : ℝ → ℝ} {g' : ℝ} (hg : HasDerivAt g g' 0) {η : ℝ}
    (hη : 0 < η) : ∃ s > 0, g s - g 0 < s * (g' + η) := by
  have h := hasDerivAt_iff_tendsto_slope_zero.1 hg
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ • (g (0 + t) - g 0) < g' + η :=
    (h.mono_left (nhdsWithin_mono _ fun t (ht : 0 < t) =>
      mem_compl_singleton_iff.2 ht.ne')).eventually (gt_mem_nhds (by linarith))
  obtain ⟨s, hs1, hs2⟩ := (h2.and self_mem_nhdsWithin).exists
  refine ⟨s, hs2, ?_⟩
  rw [zero_add, smul_eq_mul, inv_mul_lt_iff₀ hs2] at hs1
  exact hs1

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {d : ℕ} {X : ℕ → Ω → EuclideanSpace ℝ (Fin d)}

/-- **Exponential moments of the partial sums.** For i.i.d. random vectors with finite
exponential moments and `n > 0`, `exp ⟪t, Sₙ⟫` is integrable and
`E[exp ⟪t, Sₙ⟫] = exp (n Λ(t))`, where `Sₙ = ∑_{i<n} Xᵢ`. -/
theorem integrable_and_integral_exp_inner_sum (hXmeas : ∀ i, Measurable (X i))
    (hXindep : iIndepFun X μ) (hXident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hInt : ∀ t : EuclideanSpace ℝ (Fin d), Integrable (fun ω => Real.exp ⟪t, X 0 ω⟫_ℝ) μ)
    (t : EuclideanSpace ℝ (Fin d)) {n : ℕ} (hn : 0 < n) :
    Integrable (fun ω => Real.exp ⟪t, ∑ i ∈ Finset.range n, X i ω⟫_ℝ) μ ∧
      ∫ ω, Real.exp ⟪t, ∑ i ∈ Finset.range n, X i ω⟫_ℝ ∂μ =
        Real.exp (n * logMGFVec (X 0) μ t) := by
  set Y : ℕ → Ω → ℝ := fun i ω => ⟪t, X i ω⟫_ℝ with hY
  have hinnerMeas : Measurable (fun x : EuclideanSpace ℝ (Fin d) => ⟪t, x⟫_ℝ) := by
    simpa [innerSL_apply_apply] using (innerSL ℝ t).continuous.measurable
  have hYmeas : ∀ i, Measurable (Y i) := fun i => hinnerMeas.comp (hXmeas i)
  have hYindep : iIndepFun Y μ :=
    hXindep.comp (fun _ => fun x => ⟪t, x⟫_ℝ) (fun _ => hinnerMeas)
  have hYident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ := fun i => (hXident i).comp hinnerMeas
  have hYint : ∀ i, Integrable (fun ω => Real.exp (1 * Y i ω)) μ := fun i => by
    have hcomp := (hYident i).comp
      (show Measurable (fun x : ℝ => Real.exp (1 * x)) by fun_prop)
    refine hcomp.integrable_iff.mpr ?_
    change Integrable ((fun x : ℝ => Real.exp (1 * x)) ∘ Y 0) μ
    simpa [Function.comp_def, hY] using hInt t
  have heq : (fun ω => Real.exp ⟪t, ∑ i ∈ Finset.range n, X i ω⟫_ℝ) =
      fun ω => Real.exp (1 * (∑ i ∈ Finset.range n, Y i) ω) := by
    funext ω
    simp [hY, inner_sum, Finset.sum_apply]
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hYindep.integrable_exp_mul_sum hYmeas fun i _ => hYint i
  · have h := mgf_sum_of_identDistrib (μ := μ) (s := Finset.range n) (j := 0) hYmeas hYindep
      (fun i _ j _ => (hYident i).trans (hYident j).symm) (Finset.mem_range.2 hn) 1
    rw [Finset.card_range] at h
    have hpos : 0 < ∫ ω, Real.exp ⟪t, X 0 ω⟫_ℝ ∂μ := integral_exp_pos (hInt t)
    have hm0 : mgf (Y 0) μ 1 = Real.exp (logMGFVec (X 0) μ t) := by
      rw [logMGFVec, Real.exp_log hpos]
      simp [mgf, hY]
    rw [heq, Real.exp_nat_mul, ← hm0, ← h]
    rfl

/-- **Tilted Chernoff bound for a half-space event.** With the weight
`Wₙ = exp (⟪θ, Sₙ⟫ - n Λ(θ))`, for `s ≥ 0` the weighted mass of `{n c ≤ ⟪e, Sₙ⟫}` is at most
`exp (n (Λ(θ + s e) - Λ(θ) - s c))`. -/
theorem setLIntegral_tilt_le (hXmeas : ∀ i, Measurable (X i))
    (hXindep : iIndepFun X μ) (hXident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hInt : ∀ t : EuclideanSpace ℝ (Fin d), Integrable (fun ω => Real.exp ⟪t, X 0 ω⟫_ℝ) μ)
    (θ e : EuclideanSpace ℝ (Fin d)) (c : ℝ) {s : ℝ} (hs : 0 ≤ s) {n : ℕ} (hn : 0 < n) :
    ∫⁻ ω in {ω | n * c ≤ ⟪e, ∑ i ∈ Finset.range n, X i ω⟫_ℝ},
        ENNReal.ofReal (Real.exp ⟪θ, ∑ i ∈ Finset.range n, X i ω⟫_ℝ *
          Real.exp (-(n * logMGFVec (X 0) μ θ))) ∂μ ≤
      ENNReal.ofReal (Real.exp (n * (logMGFVec (X 0) μ (θ + s • e) -
        logMGFVec (X 0) μ θ - s * c))) := by
  obtain ⟨hI, hEq⟩ := integrable_and_integral_exp_inner_sum hXmeas hXindep hXident hInt
    (θ + s • e) hn
  have hSm : Measurable fun ω => ∑ i ∈ Finset.range n, X i ω :=
    Finset.measurable_sum _ fun i _ => hXmeas i
  have hset : MeasurableSet {ω | n * c ≤ ⟪e, ∑ i ∈ Finset.range n, X i ω⟫_ℝ} :=
    measurableSet_le measurable_const (by fun_prop)
  set L := logMGFVec (X 0) μ
  calc ∫⁻ ω in {ω | n * c ≤ ⟪e, ∑ i ∈ Finset.range n, X i ω⟫_ℝ},
        ENNReal.ofReal (Real.exp ⟪θ, ∑ i ∈ Finset.range n, X i ω⟫_ℝ *
          Real.exp (-(n * L θ))) ∂μ
      ≤ ∫⁻ ω in {ω | n * c ≤ ⟪e, ∑ i ∈ Finset.range n, X i ω⟫_ℝ},
          ENNReal.ofReal (Real.exp ⟪θ + s • e, ∑ i ∈ Finset.range n, X i ω⟫_ℝ *
            Real.exp (-(n * L θ + n * s * c))) ∂μ := by
        refine setLIntegral_mono' hset fun ω hω => ENNReal.ofReal_le_ofReal ?_
        rw [← Real.exp_add, ← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        rw [inner_add_left, real_inner_smul_left]
        have hω' : n * c ≤ ⟪e, ∑ i ∈ Finset.range n, X i ω⟫_ℝ := hω
        nlinarith
    _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp ⟪θ + s • e, ∑ i ∈ Finset.range n, X i ω⟫_ℝ *
            Real.exp (-(n * L θ + n * s * c))) ∂μ := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (∫ ω, Real.exp ⟪θ + s • e, ∑ i ∈ Finset.range n, X i ω⟫_ℝ *
            Real.exp (-(n * L θ + n * s * c)) ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal (hI.mul_const _)
          (ae_of_all _ fun ω => by positivity)).symm
    _ = ENNReal.ofReal (Real.exp (n * (L (θ + s • e) - L θ - s * c))) := by
        rw [integral_mul_const, hEq, ← Real.exp_add]
        congr 2
        ring

/-- **Cramér lower bound on small balls at gradient points.** Let `X₀, X₁, …` be measurable
i.i.d. random vectors in `ℝᵈ` on a probability space with `E[exp ⟪t, X₀⟫] < ∞` for every `t`,
and let the log moment generating function `Λ` have gradient `x` at `θ`. Then for every
`δ > 0`, `liminf (1/n) log μₙ(B(x, δ)) ≥ -(⟪θ, x⟫ - Λ(θ)) - ‖θ‖ δ`.

The proof tilts by `exp (⟪θ, Sₙ⟫ - n Λ(θ))` inside the expectation under the original law: the
tilted mass of the complement of the ball is exponentially small by the Chernoff bound in the
`2 d` coordinate directions, using the derivative of `Λ` at `θ`. Sources: S. R. S. Varadhan,
*Large Deviations*, lecture notes, New York University, Spring 2010, Section 1 (tilting proof
in `ℝ`, https://math.nyu.edu/~varadhan/LDP/1-2.pdf); A. Dembo and O. Zeitouni, *Large
Deviations Techniques and Applications*, 2nd ed., Section 2.2. -/
theorem le_liminf_log_empiricalMeanMeasureVec_ball (hXmeas : ∀ i, Measurable (X i))
    (hXindep : iIndepFun X μ) (hXident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hInt : ∀ t : EuclideanSpace ℝ (Fin d), Integrable (fun ω => Real.exp ⟪t, X 0 ω⟫_ℝ) μ)
    {θ x : EuclideanSpace ℝ (Fin d)}
    (hΛ : HasFDerivAt (logMGFVec (X 0) μ) (innerSL ℝ x) θ) {δ : ℝ} (hδ : 0 < δ) :
    (((-(⟪θ, x⟫_ℝ - logMGFVec (X 0) μ θ) - ‖θ‖ * δ : ℝ)) : EReal) ≤
      liminf (fun n => ((n : ℕ) : EReal)⁻¹ *
        ENNReal.log (empiricalMeanMeasureVec X μ n (ball x δ))) atTop := by
  set L := logMGFVec (X 0) μ with hL_def
  set η : ℝ := δ / (d + 1) with hη_def
  have hη : 0 < η := by positivity
  set dir : Fin d × Bool → EuclideanSpace ℝ (Fin d) := fun p =>
    if p.2 then EuclideanSpace.single p.1 (1 : ℝ) else -EuclideanSpace.single p.1 (1 : ℝ)
    with hdir_def
  have hderiv : ∀ p, ∃ s > 0, L (θ + s • dir p) - L θ - s * (⟪dir p, x⟫_ℝ + η) < 0 := by
    intro p
    have hline : HasDerivAt (fun s : ℝ => θ + s • dir p) (dir p) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (dir p)).const_add θ
    have hΛ' : HasFDerivAt L (innerSL ℝ x) (θ + (0 : ℝ) • dir p) := by simpa using hΛ
    have hg := hΛ'.comp_hasDerivAt (0 : ℝ) hline
    obtain ⟨s, hs, hlt⟩ := exists_pos_sub_lt_of_hasDerivAt hg (η := η / 2) (by positivity)
    refine ⟨s, hs, ?_⟩
    simp only [Function.comp_apply, zero_smul, add_zero, innerSL_apply_apply] at hlt
    rw [real_inner_comm] at hlt
    nlinarith
  choose s hs hneg using hderiv
  set r : Fin d × Bool → ℝ := fun p => L (θ + s p • dir p) - L θ - s p * (⟪dir p, x⟫_ℝ + η)
    with hr_def
  have hsum_tend : Tendsto (fun n : ℕ => ∑ p, Real.exp (n * r p)) atTop (𝓝 0) := by
    have : ∀ p, Tendsto (fun n : ℕ => Real.exp (n * r p)) atTop (𝓝 0) := fun p =>
      Real.tendsto_exp_atBot.comp
        (tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg (hneg p))
    simpa using tendsto_finsetSum (Finset.univ : Finset (Fin d × Bool)) fun p _ => this p
  have hhalf : ∀ᶠ n : ℕ in atTop, ∑ p, Real.exp (n * r p) ≤ 1 / 2 := by
    filter_upwards [hsum_tend (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with n hn
    exact hn
  set K : ℝ := ⟪θ, x⟫_ℝ + ‖θ‖ * δ - L θ with hK_def
  have hmain : ∀ n : ℕ, 0 < n → ∑ p, Real.exp (n * r p) ≤ 1 / 2 →
      Real.exp (-(n * K)) / 2 ≤ (empiricalMeanMeasureVec X μ n (ball x δ)).toReal := by
    intro n hn hσ
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    set S : Ω → EuclideanSpace ℝ (Fin d) := fun ω => ∑ i ∈ Finset.range n, X i ω with hS_def
    set A : Ω → EuclideanSpace ℝ (Fin d) := fun ω => (n : ℝ)⁻¹ • S ω with hA_def
    have hSm : Measurable S := Finset.measurable_sum _ fun i _ => hXmeas i
    have hAm : Measurable A := hSm.const_smul ((n : ℝ)⁻¹)
    set w : Ω → ℝ≥0∞ := fun ω =>
      ENNReal.ofReal (Real.exp ⟪θ, S ω⟫_ℝ * Real.exp (-(n * L θ))) with hw_def
    set G := A ⁻¹' ball x δ with hG_def
    have hG : MeasurableSet G := hAm measurableSet_ball
    have hμn : empiricalMeanMeasureVec X μ n (ball x δ) = μ G := by
      rw [empiricalMeanMeasureVec, Measure.map_apply hAm measurableSet_ball]
    have htot : ∫⁻ ω, w ω ∂μ = 1 := by
      obtain ⟨hI, hEq⟩ := integrable_and_integral_exp_inner_sum hXmeas hXindep hXident hInt θ hn
      rw [hw_def, ← ofReal_integral_eq_lintegral_ofReal (hI.mul_const _)
        (ae_of_all _ fun ω => by positivity), integral_mul_const, hEq, ← Real.exp_add, hL_def]
      simp
    have hgood : ∫⁻ ω in G, w ω ∂μ ≤ ENNReal.ofReal (Real.exp (n * K)) * μ G := by
      calc ∫⁻ ω in G, w ω ∂μ ≤ ∫⁻ _ω in G, ENNReal.ofReal (Real.exp (n * K)) ∂μ := by
            refine setLIntegral_mono' hG fun ω hω => ENNReal.ofReal_le_ofReal ?_
            rw [← Real.exp_add]
            refine Real.exp_le_exp.2 ?_
            have hdist : ‖A ω - x‖ < δ := by
              rw [← dist_eq_norm]
              exact hω
            have h1 : ⟪θ, A ω - x⟫_ℝ ≤ ‖θ‖ * ‖A ω - x‖ := real_inner_le_norm _ _
            have h2 : ⟪θ, S ω⟫_ℝ = n * ⟪θ, A ω⟫_ℝ := by
              rw [hA_def]
              simp only [inner_smul_right]
              field_simp
            have h3 : ‖θ‖ * ‖A ω - x‖ ≤ ‖θ‖ * δ :=
              mul_le_mul_of_nonneg_left hdist.le (norm_nonneg _)
            rw [inner_sub_right] at h1
            have h4 : n * ⟪θ, A ω⟫_ℝ ≤ n * (⟪θ, x⟫_ℝ + ‖θ‖ * δ) :=
              mul_le_mul_of_nonneg_left (by linarith) hnR.le
            rw [h2, hK_def]
            nlinarith
        _ = ENNReal.ofReal (Real.exp (n * K)) * μ G := setLIntegral_const _ _
    have hbad_sub : Gᶜ ⊆ ⋃ p, {ω | n * (⟪dir p, x⟫_ℝ + η) ≤ ⟪dir p, S ω⟫_ℝ} := by
      intro ω hω
      by_contra hcon
      simp only [mem_iUnion, not_exists, mem_ofPred_eq, not_le] at hcon
      apply hω
      change A ω ∈ ball x δ
      have hj : ∀ j, |(A ω - x) j| < η := by
        intro j
        have h1 := hcon (j, true)
        have h2 := hcon (j, false)
        simp only [hdir_def, ↓reduceIte, Bool.false_eq_true, inner_neg_left,
          inner_single_one] at h1 h2
        have hAj : (A ω - x) j = (n : ℝ)⁻¹ * S ω j - x j := by
          simp [hA_def]
        rw [hAj, abs_lt]
        have hinv : (n : ℝ)⁻¹ * S ω j * n = S ω j := by field_simp
        constructor
        · have : (n : ℝ) * (x j - η) < S ω j := by linarith
          have h5 : x j - η < (n : ℝ)⁻¹ * S ω j := by
            rw [lt_inv_mul_iff₀ hnR]
            linarith
          linarith
        · have h5 : (n : ℝ)⁻¹ * S ω j < x j + η := by
            rw [inv_mul_lt_iff₀ hnR]
            linarith
          linarith
      rw [mem_ball, dist_eq_norm, EuclideanSpace.norm_eq, Real.sqrt_lt' hδ]
      calc ∑ j, ‖(A ω - x) j‖ ^ 2 ≤ ∑ _j : Fin d, η ^ 2 := Finset.sum_le_sum fun j _ => by
            rw [Real.norm_eq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hj j).le 2
        _ = d * η ^ 2 := by simp
        _ < δ ^ 2 := by
            rw [hη_def, div_pow, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
            have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
            nlinarith [mul_pos (sq_pos_of_pos hδ)
              (show (0 : ℝ) < (d : ℝ) ^ 2 + d + 1 by positivity)]
    have hbad : ∫⁻ ω in Gᶜ, w ω ∂μ ≤ ENNReal.ofReal (∑ p, Real.exp (n * r p)) := by
      calc ∫⁻ ω in Gᶜ, w ω ∂μ
          ≤ ∫⁻ ω in ⋃ p, {ω | n * (⟪dir p, x⟫_ℝ + η) ≤ ⟪dir p, S ω⟫_ℝ}, w ω ∂μ :=
            lintegral_mono_set hbad_sub
        _ ≤ ∑' p, ∫⁻ ω in {ω | n * (⟪dir p, x⟫_ℝ + η) ≤ ⟪dir p, S ω⟫_ℝ}, w ω ∂μ :=
            lintegral_iUnion_le _ _
        _ = ∑ p, ∫⁻ ω in {ω | n * (⟪dir p, x⟫_ℝ + η) ≤ ⟪dir p, S ω⟫_ℝ}, w ω ∂μ :=
            tsum_fintype _
        _ ≤ ∑ p, ENNReal.ofReal (Real.exp (n * r p)) := Finset.sum_le_sum fun p _ =>
            setLIntegral_tilt_le hXmeas hXindep hXident hInt θ (dir p) _ (hs p).le hn
        _ = ENNReal.ofReal (∑ p, Real.exp (n * r p)) :=
            (ENNReal.ofReal_sum_of_nonneg fun p _ => (Real.exp_pos _).le).symm
    have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (n * K)) * μ G +
        ENNReal.ofReal (∑ p, Real.exp (n * r p)) := by
      rw [← htot, ← lintegral_add_compl w hG]
      exact add_le_add hgood hbad
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ G), ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun p _ => (Real.exp_pos _).le),
      ← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
    rw [hμn]
    have h2 : 1 / 2 ≤ Real.exp (n * K) * (μ G).toReal := by linarith
    calc Real.exp (-(n * K)) / 2 = Real.exp (-(n * K)) * (1 / 2) := by ring
      _ ≤ Real.exp (-(n * K)) * (Real.exp (n * K) * (μ G).toReal) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = (μ G).toReal := by
          rw [← mul_assoc, ← Real.exp_add]
          simp
  refine le_of_forall_lt_imp_le_of_dense fun b hb => ?_
  obtain ⟨b', hbb', hb'T⟩ := EReal.lt_iff_exists_real_btwn.1 hb
  rw [EReal.coe_lt_coe_iff] at hb'T
  refine hbb'.le.trans ?_
  have h2ev : ∀ᶠ n : ℕ in atTop, 2 ≤ Real.exp (n * (-K - b')) := by
    have : Tendsto (fun n : ℕ => (n : ℝ) * (-K - b')) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const (by rw [hK_def]; linarith)
    filter_upwards [this.eventually_ge_atTop 1] with n hn
    linarith [Real.add_one_le_exp (n * (-K - b'))]
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [hhalf, h2ev, eventually_gt_atTop 0] with n hσ h2 hn0
  rw [coe_le_inv_mul_log_iff hn0]
  have hm := hmain n hn0 hσ
  have hprob := isProbabilityMeasure_empiricalMeanMeasureVec (μ := μ) X n
  rw [← ENNReal.ofReal_toReal (measure_ne_top (empiricalMeanMeasureVec X μ n) (ball x δ))]
  refine ENNReal.ofReal_le_ofReal (le_trans ?_ hm)
  calc Real.exp (n * b') = Real.exp (-(n * K)) * Real.exp (-(n * (-K - b'))) := by
        rw [← Real.exp_add]
        ring_nf
    _ ≤ Real.exp (-(n * K)) * (1 / 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        rw [Real.exp_neg, one_div]
        exact inv_anti₀ (by norm_num) h2
    _ = Real.exp (-(n * K)) / 2 := by ring

/-- **Cramér lower bound for open sets, assuming a differentiable log moment generating
function.** Let `X₀, X₁, …` be measurable i.i.d. random vectors in `ℝᵈ` on a probability space
with `E[exp ⟪t, X₀⟫] < ∞` for every `t`, and suppose `Λ = log E[exp ⟪·, X₀⟫]` is differentiable.
Then for every open `U`, `-inf_U Λ* ≤ liminf (1/n) log μₙ(U)`.

For `x ∈ U` with `Λ*(x) < ∞` and `ε > 0`, a maximiser `θ` of
`t ↦ ⟪x, t⟫ - Λ(t) - ε ‖t‖² / 2` satisfies `∇Λ(θ) = x - ε θ`, with `ε ‖θ‖ → 0` and
`⟪θ, x - ε θ⟫ - Λ(θ) ≤ Λ*(x)`; the ball bound `le_liminf_log_empiricalMeanMeasureVec_ball` at
the gradient point `x - ε θ` concludes. Sources: S. R. S. Varadhan, *Large Deviations*, lecture
notes, New York University, Spring 2010, Section 1 (https://math.nyu.edu/~varadhan/LDP/1-2.pdf);
A. Dembo and O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed.,
Section 2.2. -/
theorem le_liminf_log_empiricalMeanMeasureVec_of_differentiable
    (hXmeas : ∀ i, Measurable (X i)) (hXindep : iIndepFun X μ)
    (hXident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hInt : ∀ t : EuclideanSpace ℝ (Fin d), Integrable (fun ω => Real.exp ⟪t, X 0 ω⟫_ℝ) μ)
    (hdiff : Differentiable ℝ (logMGFVec (X 0) μ)) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) :
    -(⨅ x ∈ U, (cramerRateFunction (X 0) μ x : EReal)) ≤
      liminf (fun n => ((n : ℕ) : EReal)⁻¹ *
        ENNReal.log (empiricalMeanMeasureVec X μ n U)) atTop := by
  set L := logMGFVec (X 0) μ with hL_def
  refine le_of_forall_lt_imp_le_of_dense fun b hb => ?_
  rw [EReal.lt_neg_comm] at hb
  obtain ⟨x, hxU, hx⟩ : ∃ x ∈ U, ((cramerRateFunction (X 0) μ x : ℝ≥0∞) : EReal) < -b := by
    rw [iInf_lt_iff] at hb
    obtain ⟨x, hx⟩ := hb
    rw [iInf_lt_iff] at hx
    obtain ⟨hxU, h⟩ := hx
    exact ⟨x, hxU, h⟩
  have hfin : cramerRateFunction (X 0) μ x ≠ ⊤ := by
    intro h
    rw [h, EReal.coe_ennreal_top] at hx
    exact not_top_lt hx
  set c := (cramerRateFunction (X 0) μ x).toReal with hc_def
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have hcx : ((cramerRateFunction (X 0) μ x : ℝ≥0∞) : EReal) = (c : EReal) :=
    (EReal.coe_ennreal_toReal hfin).symm
  rw [hcx, EReal.lt_neg_comm, ← EReal.coe_neg] at hx
  obtain ⟨b', hbb', hb'c⟩ := EReal.lt_iff_exists_real_btwn.1 hx
  rw [EReal.coe_lt_coe_iff] at hb'c
  refine hbb'.le.trans ?_
  -- Fenchel–Young bound
  have hFY : ∀ t, ⟪t, x⟫_ℝ - L t ≤ c := by
    intro t
    have h := le_cramerRateFunction_of_integrable (X 0) x t (hInt t)
    rw [← ENNReal.ofReal_toReal hfin, ENNReal.ofReal_le_ofReal_iff hc0] at h
    exact h
  -- an open ball inside `U`
  obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.1 hU x hxU
  set η := (-c - b') / 2 with hη_def
  have hη : 0 < η := by rw [hη_def]; linarith
  set ε : ℝ := min 1 (ρ ^ 2 / (8 * (c + 1))) with hε_def
  have hε : 0 < ε := lt_min one_pos (by positivity)
  -- the regularised maximisation problem
  set h : EuclideanSpace ℝ (Fin d) → ℝ := fun t => ⟪x, t⟫_ℝ - L t - ε / 2 * ‖t‖ ^ 2
    with hh_def
  have hcont : Continuous h := by
    have := hdiff.continuous
    rw [hh_def]
    fun_prop
  have hh0 : h 0 = 0 := by
    simp [hh_def, hL_def, logMGFVec_zero]
  obtain ⟨θ, hθ⟩ : ∃ θ, ∀ t, h t ≤ h θ := by
    refine hcont.exists_forall_ge' 0 ?_
    set R : ℝ := 2 * (c + 1) / ε + 1 with hR_def
    filter_upwards [(isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) R).compl_mem_cocompact]
      with t ht
    have htR : R < ‖t‖ := by
      simpa [mem_closedBall, dist_zero_right, not_le] using ht
    have hR0 : 0 ≤ 2 * (c + 1) / ε := by positivity
    have hR1 : 1 ≤ R := by rw [hR_def]; linarith
    have hsq : ‖t‖ ≤ ‖t‖ ^ 2 := by nlinarith
    have hRε : ε * R ≥ 2 * (c + 1) := by
      rw [hR_def, mul_add, mul_div_cancel₀ _ hε.ne']
      linarith
    have := hFY t
    rw [hh0, hh_def]
    simp only
    rw [real_inner_comm]
    nlinarith
  have hθ0 : ε / 2 * ‖θ‖ ^ 2 ≤ c := by
    have h1 := hθ 0
    rw [hh0, hh_def] at h1
    simp only at h1
    have := hFY θ
    rw [real_inner_comm] at h1
    linarith
  -- first-order condition
  set xε := x - ε • θ with hxε_def
  have hgrad : HasFDerivAt L (innerSL ℝ xε) θ := by
    have hL' := (hdiff θ).hasFDerivAt
    have hderiv : HasFDerivAt h (innerSL ℝ x - fderiv ℝ L θ - (ε / 2) • (2 • innerSL ℝ θ)) θ :=
      (((innerSL ℝ x).hasFDerivAt).sub hL').sub
        ((hasStrictFDerivAt_norm_sq θ).hasFDerivAt.const_smul (ε / 2))
    have h0 := (IsLocalMax.hasFDerivAt_eq_zero
      (Filter.Eventually.of_forall fun t => hθ t) hderiv)
    have heq : innerSL ℝ xε = fderiv ℝ L θ := by
      ext v
      have := congrArg (fun T : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ => T v) h0
      simp [innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul] at this
      simp only [innerSL_apply_apply, hxε_def, inner_sub_left, real_inner_smul_left]
      linarith
    rw [heq]
    exact hL'
  -- choice of the radius
  have hεθ : ε * ‖θ‖ < ρ / 2 := by
    have h1 : (ε * ‖θ‖) ^ 2 ≤ 2 * c * ε := by nlinarith
    have h2 : 2 * c * ε < (ρ / 2) ^ 2 := by
      have hεle : ε ≤ ρ ^ 2 / (8 * (c + 1)) := min_le_right _ _
      calc 2 * c * ε ≤ 2 * c * (ρ ^ 2 / (8 * (c + 1))) := by gcongr
        _ < (ρ / 2) ^ 2 := by
            rw [div_pow]
            rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
            nlinarith [sq_pos_of_pos hρ]
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) (h1.trans_lt h2)
  set δ := min (ρ / 2) (η / (‖θ‖ + 1)) with hδ_def
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hball : ball xε δ ⊆ U := by
    intro y hy
    refine hρU ?_
    rw [mem_ball] at hy ⊢
    have h1 : dist xε x = ε * ‖θ‖ := by
      rw [hxε_def, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
        abs_of_pos hε]
    have h2 : δ ≤ ρ / 2 := min_le_left _ _
    linarith [dist_triangle y xε x]
  have hθδ : ‖θ‖ * δ ≤ η := by
    have h1 : δ ≤ η / (‖θ‖ + 1) := min_le_right _ _
    calc ‖θ‖ * δ ≤ ‖θ‖ * (η / (‖θ‖ + 1)) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ ≤ η := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith [norm_nonneg θ]
  have hrate : ⟪θ, xε⟫_ℝ - L θ ≤ c := by
    have := hFY θ
    rw [hxε_def, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    nlinarith [sq_nonneg ‖θ‖]
  have hball_bound := le_liminf_log_empiricalMeanMeasureVec_ball hXmeas hXindep hXident hInt
    hgrad hδ
  refine le_trans ?_ (hball_bound.trans ?_)
  · exact_mod_cast (show b' ≤ -(⟪θ, xε⟫_ℝ - L θ) - ‖θ‖ * δ by linarith)
  · refine liminf_le_liminf ?_ (by isBoundedDefault) (by isBoundedDefault)
    filter_upwards [eventually_ge_atTop 1] with n hn
    apply mul_le_mul_of_nonneg_left _ _
    · exact ENNReal.log_monotone (measure_mono hball)
    · exact EReal.inv_nonneg_of_nonneg (by exact_mod_cast Nat.zero_le n)

/-- Cramér's theorem with the differentiability of `Λ` as an explicit hypothesis; a proof step of
`satisfiesLDP_empiricalMeanMeasureVec`, where the hypothesis is discharged by
`differentiable_logMGFVec` (it always holds under finite exponential moments). -/
private theorem satisfiesLDP_empiricalMeanMeasureVec_of_differentiable
    (hXmeas : ∀ i, Measurable (X i)) (hXindep : iIndepFun X μ)
    (hXident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hInt : ∀ t : EuclideanSpace ℝ (Fin d), Integrable (fun ω => Real.exp ⟪t, X 0 ω⟫_ℝ) μ)
    (hdiff : Differentiable ℝ (logMGFVec (X 0) μ)) :
    SatisfiesLDP (empiricalMeanMeasureVec X μ) (cramerRateFunction (X 0) μ) ∧
      IsGoodRateFunction (cramerRateFunction (X 0) μ) :=
  ⟨⟨⟨lowerSemicontinuous_cramerRateFunction (X 0) μ⟩,
    fun _ hU => le_liminf_log_empiricalMeanMeasureVec_of_differentiable hXmeas hXindep hXident
      hInt hdiff hU,
    fun _ hF => limsup_log_empiricalMeanMeasureVec_le hXmeas hXindep hXident hInt hF⟩,
    isGoodRateFunction_cramerRateFunction (X 0) hInt⟩

/-- **Differentiability of the log moment generating function.** If `X₀` is a measurable random
vector in `ℝᵈ` with `E[exp ⟪t, X₀⟫] < ∞` for every `t` under a probability measure, then
`Λ(t) = log E[exp ⟪t, X₀⟫]` is differentiable on `ℝᵈ` (differentiation under the integral,
dominated by finitely many exponential moments). -/
theorem differentiable_logMGFVec (X₀ : Ω → EuclideanSpace ℝ (Fin d)) (hX : Measurable X₀)
    (hInt : ∀ t : EuclideanSpace ℝ (Fin d), Integrable (fun ω => Real.exp ⟪t, X₀ ω⟫_ℝ) μ) :
    Differentiable ℝ (logMGFVec X₀ μ) := by
  intro t
  set v : (Fin d → Bool) → EuclideanSpace ℝ (Fin d) := fun σ =>
    ∑ j, (if σ j then EuclideanSpace.single j (1 : ℝ) else -EuclideanSpace.single j (1 : ℝ))
    with hv_def
  have hv : ∀ y : EuclideanSpace ℝ (Fin d),
      ⟪v (fun j => decide (0 ≤ y j)), y⟫_ℝ = ∑ j, |y j| := by
    intro y
    simp only [hv_def, sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : 0 ≤ y j
    · simp [hj, inner_single_one, abs_of_nonneg hj]
    · simp [hj, inner_neg_left, inner_single_one, abs_of_neg (lt_of_not_ge hj)]
  have hnorm : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ ∑ j, |y j| := by
    intro y
    rw [EuclideanSpace.norm_eq]
    calc Real.sqrt (∑ j, ‖y j‖ ^ 2) ≤ Real.sqrt ((∑ j, |y j|) ^ 2) := by
          refine Real.sqrt_le_sqrt ?_
          simpa only [Real.norm_eq_abs] using
            Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun j => |y j|)
              (fun j _ => abs_nonneg _)
      _ = ∑ j, |y j| := Real.sqrt_sq (Finset.sum_nonneg fun j _ => abs_nonneg _)
  set bound : Ω → ℝ := fun ω => ∑ σ, Real.exp ⟪t + (2 : ℝ) • v σ, X₀ ω⟫_ℝ with hbound_def
  have hbound_int : Integrable bound μ := integrable_finsetSum _ fun σ _ => hInt _
  have hderiv1 : ∀ y t' : EuclideanSpace ℝ (Fin d), HasFDerivAt (fun t => Real.exp ⟪t, y⟫_ℝ)
      (Real.exp ⟪t', y⟫_ℝ • innerSL ℝ y) t' := by
    intro y t'
    have h := ((innerSL ℝ y).hasFDerivAt (x := t')).exp
    have e : (fun t => Real.exp ⟪t, y⟫_ℝ) = fun t => Real.exp ((innerSL ℝ y) t) := by
      funext t
      rw [innerSL_apply_apply, real_inner_comm]
    rw [e]
    convert h using 2
    rw [innerSL_apply_apply, real_inner_comm]
  have hM : HasFDerivAt (fun t => ∫ ω, Real.exp ⟪t, X₀ ω⟫_ℝ ∂μ)
      (∫ ω, Real.exp ⟪t, X₀ ω⟫_ℝ • innerSL ℝ (X₀ ω) ∂μ) t := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := bound)
      (F' := fun t' ω => Real.exp ⟪t', X₀ ω⟫_ℝ • innerSL ℝ (X₀ ω))
      (ball_mem_nhds t one_pos) ?_ (hInt t) ?_ ?_ hbound_int ?_
    · exact Eventually.of_forall fun t' => (hInt t').aestronglyMeasurable
    · exact (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin d) =>
        Real.exp ⟪t, y⟫_ℝ • innerSL ℝ y).comp_aestronglyMeasurable hX.aestronglyMeasurable
    · refine ae_of_all _ fun ω t' ht' => ?_
      set y := X₀ ω
      rw [norm_smul, innerSL_apply_norm, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have h1 : ⟪t', y⟫_ℝ ≤ ⟪t, y⟫_ℝ + ‖y‖ := by
        have h := real_inner_le_norm (t' - t) y
        rw [inner_sub_left] at h
        have hd : ‖t' - t‖ < 1 := by
          rw [← dist_eq_norm]
          exact ht'
        nlinarith [norm_nonneg y]
      have h2 : ‖y‖ ≤ Real.exp ‖y‖ := by linarith [Real.add_one_le_exp ‖y‖]
      calc Real.exp ⟪t', y⟫_ℝ * ‖y‖ ≤ Real.exp (⟪t, y⟫_ℝ + ‖y‖) * Real.exp ‖y‖ :=
            mul_le_mul (Real.exp_le_exp.2 h1) h2 (norm_nonneg _) (Real.exp_pos _).le
        _ = Real.exp (⟪t, y⟫_ℝ + 2 * ‖y‖) := by
            rw [← Real.exp_add]
            ring_nf
        _ ≤ Real.exp ⟪t + (2 : ℝ) • v (fun j => decide (0 ≤ y j)), y⟫_ℝ := by
            refine Real.exp_le_exp.2 ?_
            rw [inner_add_left, real_inner_smul_left, hv]
            linarith [hnorm y]
        _ ≤ bound ω := Finset.single_le_sum
            (f := fun σ => Real.exp ⟪t + (2 : ℝ) • v σ, y⟫_ℝ)
            (fun σ _ => (Real.exp_pos _).le) (Finset.mem_univ _)
    · exact ae_of_all _ fun ω t' _ => hderiv1 (X₀ ω) t'
  have hpos : (∫ ω, Real.exp ⟪t, X₀ ω⟫_ℝ ∂μ) ≠ 0 := (integral_exp_pos (hInt t)).ne'
  change DifferentiableAt ℝ (fun t => Real.log (∫ ω, Real.exp ⟪t, X₀ ω⟫_ℝ ∂μ)) t
  exact hM.differentiableAt.log hpos

/-- **Cramér lower bound for open sets.** Let `X₀, X₁, …` be measurable i.i.d. random vectors in
`ℝᵈ` on a probability space with `E[exp ⟪t, X₀⟫] < ∞` for every `t`. Then for every open `U`,
`-inf_U Λ* ≤ liminf (1/n) log μₙ(U)`, in the form of the `SatisfiesLDP.lower_bound` field.
Sources: S. R. S. Varadhan, *Large Deviations*, lecture notes, New York University,
Spring 2010, Section 1 (https://math.nyu.edu/~varadhan/LDP/1-2.pdf); A. Dembo and
O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed., Section 2.2. -/
theorem le_liminf_log_empiricalMeanMeasureVec (hXmeas : ∀ i, Measurable (X i))
    (hXindep : iIndepFun X μ) (hXident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hInt : ∀ t : EuclideanSpace ℝ (Fin d), Integrable (fun ω => Real.exp ⟪t, X 0 ω⟫_ℝ) μ)
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) :
    -(⨅ x ∈ U, (cramerRateFunction (X 0) μ x : EReal)) ≤
      liminf (fun n => ((n : ℕ) : EReal)⁻¹ *
        ENNReal.log (empiricalMeanMeasureVec X μ n U)) atTop :=
  le_liminf_log_empiricalMeanMeasureVec_of_differentiable hXmeas hXindep hXident hInt
    (differentiable_logMGFVec (X 0) (hXmeas 0) hInt) hU

/-- **Cramér's theorem in `ℝᵈ`.** Let `X₀, X₁, …` be measurable, independent, identically
distributed random vectors in `ℝᵈ` on a probability space, with `E[exp ⟪t, X₀⟫] < ∞` for every
`t ∈ ℝᵈ`. Then the laws `μₙ` of the empirical means `(1/n) ∑_{i<n} Xᵢ` satisfy the large
deviation principle with the Cramér rate function `Λ*(x) = sup_t (⟪t, x⟫ - log E[exp ⟪t, X₀⟫])`,
and `Λ*` is a good rate function. Sources: S. R. S. Varadhan, *Large Deviations*, lecture notes,
New York University, Spring 2010, Section 3, Corollary 1.3 in the notes' numbering
(https://math.nyu.edu/~varadhan/LDP/Spring2010.3.pdf; separable Banach spaces with
`E[exp (θ ‖X₀‖)] < ∞` for every `θ > 0`, which in `ℝᵈ` is the finite-moment hypothesis here), and
Section 1 for the Chebyshev upper bound and tilting lower bound followed here
(https://math.nyu.edu/~varadhan/LDP/1-2.pdf); A. Dembo and O. Zeitouni, *Large Deviations
Techniques and Applications*, 2nd ed., Section 2.2. -/
theorem satisfiesLDP_empiricalMeanMeasureVec (hXmeas : ∀ i, Measurable (X i))
    (hXindep : iIndepFun X μ) (hXident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hInt : ∀ t : EuclideanSpace ℝ (Fin d), Integrable (fun ω => Real.exp ⟪t, X 0 ω⟫_ℝ) μ) :
    SatisfiesLDP (empiricalMeanMeasureVec X μ) (cramerRateFunction (X 0) μ) ∧
      IsGoodRateFunction (cramerRateFunction (X 0) μ) :=
  satisfiesLDP_empiricalMeanMeasureVec_of_differentiable hXmeas hXindep hXident hInt
    (differentiable_logMGFVec (X 0) (hXmeas 0) hInt)

end MathlibExt.Probability.CramerLDPLowerBound
