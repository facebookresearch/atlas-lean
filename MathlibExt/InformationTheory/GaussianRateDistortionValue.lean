/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.ConditionalEntropy
public import MathlibExt.InformationTheory.GaussianDistortionFeasibility
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The Gaussian rate-distortion function at every distortion level

## Source contract

For a scalar Gaussian source `N(0, σ2)` with `σ2 > 0` and squared-error distortion, the
rate-distortion function `R(D)`, in bits, is the `ℝ≥0∞` infimum of the mutual information over the
joint laws of `(X, X̂)` whose source marginal is `N(0, σ2)` and whose lower-integral distortion
`∫⁻ ofReal ((x - x̂)²)` is at most `ofReal D`, for `D ≥ 0`. Its value at every `D ≥ 0` is

* `R(D) = 0` for `D ≥ σ2`: the independent constant reconstruction `X̂ = 0` has distortion `σ2`
  and zero mutual information;
* `R(0) = ⊤`: zero distortion forces `X = X̂` almost surely, so the joint law charges the diagonal
  with mass one, while the product of its marginals gives the diagonal mass zero because the
  Gaussian source has no atoms; the joint law is not absolutely continuous with respect to that
  product and its Kullback-Leibler divergence, hence its mutual information, is `⊤`;
* `R(D) = log (σ2 / D) / (2 log 2)` bits for `0 < D < σ2`, combining the positive-distortion lower
  bound (the normalized density test) with the matching upper bound (the additive Gaussian
  backward channel).

The two endpoints are proved here outright. The headline `rateDistortion_eq_ite` takes the two
interior bounds as hypotheses: the lower bound is exactly
`GaussianDistortionConverse.rateDistortion_ge_ofReal_log_div σ2`, and the upper bound is the
achievability bound of the additive Gaussian backward channel. The unconditional value for every
`σ2 > 0` and `D ≥ 0` follows by supplying both bounds; that corollary is left to accompany the
achievability theorem.

The top endpoint stays in `ℝ≥0∞`; it is never turned into a real number. A source with an atom does
not support the diagonal-singularity argument: for the degenerate source `N(0, 0)` the
zero-distortion rate is `0`.

Source: T. M. Cover and J. A. Thomas, *Elements of Information Theory*, 2nd ed. (2006),
Theorem 10.3.2 and the surrounding discussion of `R(D)` for `D ≥ σ2`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MathlibExt.InformationTheory.GaussianRateDistortionValue

open _root_.InformationTheory
open MathlibExt.InformationTheory.GaussianDistortionFeasibility

/-! ### Private helpers -/

private theorem measurable_sq_error_ennreal' :
    Measurable (fun z : ℝ × ℝ => ENNReal.ofReal ((z.1 - z.2) ^ 2)) :=
  ((continuous_fst.sub continuous_snd).pow 2).measurable.ennreal_ofReal

private theorem measurable_diag : Measurable (fun x : ℝ => (x, x)) :=
  measurable_id.prodMk measurable_id

private theorem map_fst_diagonalReconstruction (σ2 : ℝ≥0) :
    (diagonalReconstruction σ2 : Measure (ℝ × ℝ)).map Prod.fst = gaussianReal 0 σ2 := by
  change ((gaussianReal 0 σ2).map (fun x : ℝ => (x, x))).map Prod.fst = _
  rw [Measure.map_map measurable_fst measurable_diag]
  exact Measure.map_id

/-! ### Monotonicity in the distortion level -/

/-- Raising the distortion level enlarges the feasible set. -/
theorem distortionFeasible_mono (σ2 : ℝ≥0) {D D' : ℝ} (h : D ≤ D') :
    distortionFeasible σ2 D ⊆ distortionFeasible σ2 D' := by
  rintro μ ⟨h0, hmap, hle⟩
  exact ⟨h0.trans h, hmap, hle.trans (ENNReal.ofReal_le_ofReal h)⟩

/-- The rate-distortion function is antitone in the distortion level. -/
theorem rateDistortion_antitone (σ2 : ℝ≥0) : Antitone (rateDistortion σ2) := by
  intro D D' h
  unfold rateDistortion
  exact biInf_mono fun μ hμ => distortionFeasible_mono σ2 h hμ

/-! ### Large distortion: zero rate -/

/-- For `D ≥ σ2` the independent constant reconstruction `X̂ = 0` is feasible and carries no
information, so `R(D) = 0`. -/
theorem rateDistortion_eq_zero_of_le (σ2 : ℝ≥0) {D : ℝ} (hD : (σ2 : ℝ) ≤ D) :
    rateDistortion σ2 D = 0 := by
  have hmem : constantReconstruction σ2 ∈ distortionFeasible σ2 D :=
    distortionFeasible_mono σ2 hD (constantReconstruction_mem_distortionFeasible σ2)
  have hle : rateDistortion σ2 D ≤ measureMutualInformation (constantReconstruction σ2) :=
    iInf₂_le _ hmem
  rw [measureMutualInformation_constantReconstruction] at hle
  exact le_antisymm hle bot_le

/-! ### Zero distortion: infinite rate -/

/-- A law that is feasible at distortion `0` reconstructs the source exactly almost surely. -/
theorem ae_fst_eq_snd_of_mem_distortionFeasible_zero {σ2 : ℝ≥0}
    {μ : ProbabilityMeasure (ℝ × ℝ)} (hμ : μ ∈ distortionFeasible σ2 0) :
    ∀ᵐ z ∂(μ : Measure (ℝ × ℝ)), z.1 = z.2 := by
  obtain ⟨-, -, hle⟩ := hμ
  rw [ENNReal.ofReal_zero, nonpos_iff_eq_zero,
    lintegral_eq_zero_iff measurable_sq_error_ennreal'] at hle
  filter_upwards [hle] with z hz
  have h0 : ENNReal.ofReal ((z.1 - z.2) ^ 2) = 0 := hz
  rw [ENNReal.ofReal_eq_zero] at h0
  have hsq : (z.1 - z.2) ^ 2 = 0 := le_antisymm h0 (sq_nonneg _)
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq)

/-- For `σ2 > 0`, a law feasible at distortion `0` charges the diagonal with full mass while the
product of its marginals gives the diagonal mass zero (the source `N(0, σ2)` has no atoms), so the
law is not absolutely continuous with respect to that product. -/
theorem not_absolutelyContinuous_prod_of_mem_distortionFeasible_zero {σ2 : ℝ≥0} (hσ2 : 0 < σ2)
    {μ : ProbabilityMeasure (ℝ × ℝ)} (hμ : μ ∈ distortionFeasible σ2 0) :
    ¬ (μ : Measure (ℝ × ℝ)) ≪
      ((μ : Measure (ℝ × ℝ)).map Prod.fst).prod ((μ : Measure (ℝ × ℝ)).map Prod.snd) := by
  intro hac
  have hmap : (μ : Measure (ℝ × ℝ)).map Prod.fst = gaussianReal 0 σ2 := hμ.2.1
  have hae := ae_fst_eq_snd_of_mem_distortionFeasible_zero hμ
  have hdiag : MeasurableSet (Set.diagonal ℝ) := measurableSet_diagonal
  -- the diagonal has full joint mass
  have hcompl : (μ : Measure (ℝ × ℝ)) (Set.diagonal ℝ)ᶜ = 0 := ae_iff.mp hae
  have hone : (μ : Measure (ℝ × ℝ)) (Set.diagonal ℝ) = 1 :=
    (prob_compl_eq_zero_iff hdiag).mp hcompl
  -- the product of the marginals gives the diagonal mass zero
  have : NullSingletonClass (gaussianReal 0 σ2) :=
    nullSingletonClass_gaussianReal (ne_of_gt hσ2)
  have hprod : (((μ : Measure (ℝ × ℝ)).map Prod.fst).prod
      ((μ : Measure (ℝ × ℝ)).map Prod.snd)) (Set.diagonal ℝ) = 0 := by
    rw [Measure.prod_apply_symm hdiag, hmap]
    have hpre : ∀ y : ℝ, (fun x : ℝ => (x, y)) ⁻¹' Set.diagonal ℝ = {y} := by
      intro y
      ext x
      simp [Set.mem_diagonal_iff]
    simp only [hpre, measure_singleton, lintegral_zero]
  have := hac hprod
  rw [hone] at this
  exact one_ne_zero this

/-- For `σ2 > 0`, every law feasible at distortion `0` has infinite mutual information. -/
theorem measureMutualInformation_eq_top_of_mem_distortionFeasible_zero {σ2 : ℝ≥0}
    (hσ2 : 0 < σ2) {μ : ProbabilityMeasure (ℝ × ℝ)} (hμ : μ ∈ distortionFeasible σ2 0) :
    measureMutualInformation μ = ⊤ := by
  unfold measureMutualInformation
  rw [klDiv_of_not_ac (not_absolutelyContinuous_prod_of_mem_distortionFeasible_zero hσ2 hμ)]
  exact ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top

/-- **Zero distortion.** For `σ2 > 0`, `R(0) = ⊤`. -/
theorem rateDistortion_zero_eq_top {σ2 : ℝ≥0} (hσ2 : 0 < σ2) :
    rateDistortion σ2 0 = ⊤ := by
  refine eq_top_iff.mpr (le_iInf₂ fun μ hμ => ?_)
  rw [measureMutualInformation_eq_top_of_mem_distortionFeasible_zero hσ2 hμ]

/-! ### Validation of the zero-distortion endpoint -/

/-- Exact reconstruction is feasible at distortion `0`, so the infimum defining `R(0)` is not
taken over the empty set. -/
theorem diagonalReconstruction_mem_distortionFeasible_zero (σ2 : ℝ≥0) :
    diagonalReconstruction σ2 ∈ distortionFeasible σ2 0 := by
  refine ⟨le_rfl, map_fst_diagonalReconstruction σ2, ?_⟩
  change ∫⁻ z, ENNReal.ofReal ((z.1 - z.2) ^ 2)
    ∂((gaussianReal 0 σ2).map (fun x : ℝ => (x, x))) ≤ ENNReal.ofReal 0
  rw [lintegral_map measurable_sq_error_ennreal' measurable_diag]
  simp

/-- For `σ2 > 0`, exact reconstruction carries infinite mutual information. -/
theorem measureMutualInformation_diagonalReconstruction {σ2 : ℝ≥0} (hσ2 : 0 < σ2) :
    measureMutualInformation (diagonalReconstruction σ2) = ⊤ := by
  exact measureMutualInformation_eq_top_of_mem_distortionFeasible_zero hσ2
    (diagonalReconstruction_mem_distortionFeasible_zero σ2)

/-- An atomic source breaks the zero-distortion claim: for the degenerate source `N(0, 0)`, a
point mass, exact reconstruction has zero mutual information. -/
theorem measureMutualInformation_diagonalReconstruction_zero :
    measureMutualInformation (diagonalReconstruction 0) = 0 := by
  unfold measureMutualInformation
  have hd : (diagonalReconstruction 0 : Measure (ℝ × ℝ)) = Measure.dirac ((0 : ℝ), (0 : ℝ)) := by
    change (gaussianReal 0 0).map (fun x : ℝ => (x, x)) = _
    rw [gaussianReal_zero_var, Measure.map_dirac' measurable_diag]
  rw [hd, Measure.map_dirac' measurable_fst, Measure.map_dirac' measurable_snd,
    Measure.dirac_prod_dirac, klDiv_self, ENNReal.zero_div]

/-- Hence `R(0) = 0` for the degenerate source, and the hypothesis `0 < σ2` of
`rateDistortion_zero_eq_top` cannot be dropped. -/
theorem rateDistortion_zero_zero : rateDistortion 0 0 = 0 := by
  exact rateDistortion_eq_zero_of_le 0 (by simp)

/-! ### Headline -/

/-- **Gaussian rate-distortion function.** For the source `N(0, σ2)` with `σ2 > 0` and every
distortion level `D ≥ 0`,
`R(D) = ⊤` if `D = 0`, `R(D) = log (σ2 / D) / (2 log 2)` bits if `0 < D < σ2`, and `R(D) = 0` if
`D ≥ σ2`. The interior value combines the positive-distortion lower bound `hlower` with the
matching upper bound `hupper`, both stated for every `0 < d < σ2`; the two endpoints are proved
here without them. -/
theorem rateDistortion_eq_ite {σ2 : ℝ≥0} (hσ2 : 0 < σ2) {D : ℝ} (hD : 0 ≤ D)
    (hlower : ∀ d : ℝ≥0, (0 : ℝ) < (d : ℝ) → (d : ℝ) < (σ2 : ℝ) →
      ENNReal.ofReal (Real.log ((σ2 : ℝ) / (d : ℝ)) / (2 * Real.log 2)) ≤
        rateDistortion σ2 (d : ℝ))
    (hupper : ∀ d : ℝ≥0, (0 : ℝ) < (d : ℝ) → (d : ℝ) < (σ2 : ℝ) →
      rateDistortion σ2 (d : ℝ) ≤
        ENNReal.ofReal (Real.log ((σ2 : ℝ) / (d : ℝ)) / (2 * Real.log 2))) :
    rateDistortion σ2 D =
      if D = 0 then ⊤
      else if D < (σ2 : ℝ) then ENNReal.ofReal (Real.log ((σ2 : ℝ) / D) / (2 * Real.log 2))
      else 0 := by
  split_ifs with h0 hlt
  · subst h0
    exact rateDistortion_zero_eq_top hσ2
  · have hpos : (0 : ℝ) < D := lt_of_le_of_ne hD (Ne.symm h0)
    exact le_antisymm (hupper ⟨D, hD⟩ hpos hlt) (hlower ⟨D, hD⟩ hpos hlt)
  · exact rateDistortion_eq_zero_of_le σ2 (not_lt.mp hlt)

end MathlibExt.InformationTheory.GaussianRateDistortionValue
