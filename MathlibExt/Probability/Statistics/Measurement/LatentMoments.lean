/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FiniteProbability
public import MathlibExt.Probability.Statistics.Measurement.ProductMoments
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# Finite latent-mixture moments

For a finite latent state with law `pi` and conditionally independent
coordinates with success curves `q z i` in `[0, 1]`, the observed law is
the bind of `pi` with the existing product law. Its first moments and its off-diagonal (distinct-coordinate) pair
moments are the `pi`-mixtures of the component moments, and for distinct
coordinates the observed covariance is the finite covariance of the
success curves under `pi`.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.Measurement

open MeasureTheory ProbabilityTheory

/-! ## Helpers -/

private theorem bind_integral_eq {Z α : Type*} [Fintype Z] [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (pi : PMF Z) (K : Z → PMF α) (f : α → ℝ) :
    ∫ x, f x ∂(pi.bind K).toMeasure
      = ∑ z, (pi z).toReal * (∫ x, f x ∂(K z).toMeasure) := by
  have hbind : ∀ x, ((pi.bind K) x).toReal
      = ∑ z, (pi z).toReal * ((K z) x).toReal := by
    intro x
    rw [PMF.bind_apply, tsum_fintype]
    rw [ENNReal.toReal_sum (fun a _ => by
      apply ENNReal.mul_ne_top
      · exact pi.apply_ne_top a
      · exact (K a).apply_ne_top x)]
    apply Finset.sum_congr rfl
    intro z _
    rw [ENNReal.toReal_mul]
  have hK : ∀ z, (∫ x, f x ∂(K z).toMeasure) = ∑ x, ((K z) x).toReal * f x := by
    intro z
    rw [PMF.integral_eq_sum _ f]
    apply Finset.sum_congr rfl
    intro x _
    rw [smul_eq_mul]
  rw [PMF.integral_eq_sum _ f]
  simp_rw [hbind, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [hK]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring


/-- **Latent-mixture coordinate moments.** Let `Z` (latent states) and `ι`
(items) be finite, `pi : PMF Z` a latent law with no support restriction,
and `q z i ∈ [0, 1]` item curves (endpoints `0` and `1` allowed). Under
the observed law `pi.bind (fun z => localIndepPMF (q z) ..)`, the first
moment of coordinate `i` is the `pi`-mixture of the component means
`q z i`, the off-diagonal pair moment of distinct coordinates `i, j` is
the mixture of the component products `q z i * q z j`, and for distinct coordinates
`i ≠ j` the observed covariance is the finite covariance of the curves
`z ↦ q z i`, `z ↦ q z j` under the weights `(pi z).toReal`. -/
theorem latentMixture_coordinate_moments {Z ι : Type*} [Fintype Z] [Fintype ι]
    [DecidableEq ι] (pi : PMF Z) (q : Z → ι → ℝ)
    (hq0 : ∀ z i, 0 ≤ q z i) (hq1 : ∀ z i, q z i ≤ 1) :
    (∀ i, ∫ x, (if x i then (1 : ℝ) else 0)
        ∂(pi.bind fun z => localIndepPMF (q z) (hq0 z) (hq1 z)).toMeasure
      = MathlibExt.Probability.FiniteProbability.expectation
          (fun z => (pi z).toReal) (fun z => q z i))
    ∧ (∀ i j, i ≠ j →
        ∫ x, (if x i then (1 : ℝ) else 0) * (if x j then (1 : ℝ) else 0)
          ∂(pi.bind fun z => localIndepPMF (q z) (hq0 z) (hq1 z)).toMeasure
        = MathlibExt.Probability.FiniteProbability.expectation
            (fun z => (pi z).toReal) (fun z => q z i * q z j))
    ∧ (∀ i j, i ≠ j →
        ProbabilityTheory.covariance (fun x : ι → Bool => if x i then (1 : ℝ) else 0)
            (fun x : ι → Bool => if x j then (1 : ℝ) else 0)
            (pi.bind fun z => localIndepPMF (q z) (hq0 z) (hq1 z)).toMeasure
          = MathlibExt.Probability.FiniteProbability.covariance
              (fun z => (pi z).toReal) (fun z => q z i) (fun z => q z j)) := by
  have h1 : ∀ i, ∫ x, (if x i then (1 : ℝ) else 0)
        ∂(pi.bind fun z => localIndepPMF (q z) (hq0 z) (hq1 z)).toMeasure
      = MathlibExt.Probability.FiniteProbability.expectation
          (fun z => (pi z).toReal) (fun z => q z i) := by
    intro i
    rw [bind_integral_eq]
    simp_rw [(localIndepPMF_coordinate_moments (q _) (hq0 _) (hq1 _)).1 i]
    rfl
  have h2 : ∀ i j, i ≠ j →
        ∫ x, (if x i then (1 : ℝ) else 0) * (if x j then (1 : ℝ) else 0)
          ∂(pi.bind fun z => localIndepPMF (q z) (hq0 z) (hq1 z)).toMeasure
        = MathlibExt.Probability.FiniteProbability.expectation
            (fun z => (pi z).toReal) (fun z => q z i * q z j) := by
    intro i j hij
    rw [bind_integral_eq]
    simp_rw [(localIndepPMF_coordinate_moments (q _) (hq0 _) (hq1 _)).2 i j hij]
    rfl
  have h3 : ∀ i j, i ≠ j →
        ProbabilityTheory.covariance (fun x : ι → Bool => if x i then (1 : ℝ) else 0)
            (fun x : ι → Bool => if x j then (1 : ℝ) else 0)
            (pi.bind fun z => localIndepPMF (q z) (hq0 z) (hq1 z)).toMeasure
          = MathlibExt.Probability.FiniteProbability.covariance
              (fun z => (pi z).toReal) (fun z => q z i) (fun z => q z j) := by
    intro i j hij
    rw [MathlibExt.Probability.FiniteProbability.covariance_toMeasure_eq]
    rw [MathlibExt.Probability.FiniteProbability.covariance_eq_sub
      (MathlibExt.Probability.FiniteProbability.sum_toReal_eq_one _),
      MathlibExt.Probability.FiniteProbability.covariance_eq_sub
      (MathlibExt.Probability.FiniteProbability.sum_toReal_eq_one pi)]
    rw [← MathlibExt.Probability.FiniteProbability.integral_toMeasure_eq_expectation,
      ← MathlibExt.Probability.FiniteProbability.integral_toMeasure_eq_expectation,
      ← MathlibExt.Probability.FiniteProbability.integral_toMeasure_eq_expectation]
    rw [h1 i, h1 j, h2 i j hij]
  exact ⟨h1, h2, h3⟩

/-- Latent relabeling, as an instantiation of the existing `PMF.map` /
`PMF.bind` laws (leaf: "instantiate existing bind/map relabeling rather
than reprove its generic law"). Relabeling latent states by an equivalence
`e : Z ≃ Z'`, with curves transported along `e`, leaves the observed
mixture law unchanged. Kept as an `example`: no new public symbol. At
integration this follows from `PMF.map_bind` and `PMF.bind_map`. -/
example {Z Z' ι : Type*} [Fintype Z] [Fintype Z'] [Fintype ι] [DecidableEq ι]
    (e : Z ≃ Z') (pi : PMF Z) (q : Z → ι → ℝ)
    (hq0 : ∀ z i, 0 ≤ q z i) (hq1 : ∀ z i, q z i ≤ 1) :
    (pi.map e).bind (fun z' => localIndepPMF (q (e.symm z'))
        (hq0 (e.symm z')) (hq1 (e.symm z')))
      = pi.bind (fun z => localIndepPMF (q z) (hq0 z) (hq1 z)) := by
  rw [PMF.bind_map]
  congr 1
  funext z
  simp


end MathlibExt.Probability.Statistics.Measurement
