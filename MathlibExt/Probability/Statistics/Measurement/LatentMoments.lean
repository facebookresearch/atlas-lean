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
the bind of `pi` with the existing product law. Its first and pair
moments are the `pi`-mixtures of the component moments, and for distinct
coordinates the observed covariance is the finite covariance of the
success curves under `pi`.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.Measurement

open MeasureTheory ProbabilityTheory

/-! ## Helpers (proof-only, not PIN-COPY) -/

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

private theorem pmf_sum_toReal_eq_one {Z : Type*} [Fintype Z] (pi : PMF Z) :
    ∑ z, (pi z).toReal = 1 := by
  have h1 : (∑ z, pi z) = 1 := by
    have h := pi.tsum_coe
    rwa [tsum_fintype] at h
  have h2 : (∑ z, pi z).toReal = (1 : ENNReal).toReal := by rw [h1]
  rw [ENNReal.toReal_sum (fun a _ => pi.apply_ne_top a)] at h2
  simpa using h2

private theorem memLp_indicator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : PMF (ι → Bool)) (i : ι) :
    MemLp (fun x : ι → Bool => (if x i then (1 : ℝ) else 0)) 2 p.toMeasure := by
  refine memLp_of_bounded (a := 0) (b := 1) ?_ ?_ 2
  · filter_upwards with x
    cases h : x i <;> simp
  · exact (by measurability : Measurable (fun x : ι → Bool => (if x i then (1 : ℝ) else 0))).aestronglyMeasurable

private theorem finiteCovariance_eq {α : Type*} [Fintype α] (p X Y : α → ℝ)
    (hp : ∑ x, p x = 1) :
    MathlibExt.Probability.FiniteProbability.covariance p X Y
      = (∑ x, p x * (X x * Y x)) - (∑ x, p x * X x) * (∑ x, p x * Y x) := by
  unfold MathlibExt.Probability.FiniteProbability.covariance
    MathlibExt.Probability.FiniteProbability.expectation
  have hterm : ∀ x, p x * ((X x - (∑ y, p y * X y)) * (Y x - (∑ y, p y * Y y)))
      = p x * (X x * Y x) - (p x * X x) * (∑ y, p y * Y y)
        - (p x * Y x) * (∑ y, p y * X y)
        + p x * ((∑ y, p y * X y) * (∑ y, p y * Y y)) := by
    intro x
    ring
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hB : (∑ x, (p x * X x) * (∑ y, p y * Y y))
      = (∑ x, p x * X x) * (∑ y, p y * Y y) :=
    (Finset.sum_mul Finset.univ (fun x => p x * X x) _).symm
  have hC : (∑ x, (p x * Y x) * (∑ y, p y * X y))
      = (∑ x, p x * Y x) * (∑ y, p y * X y) :=
    (Finset.sum_mul Finset.univ (fun x => p x * Y x) _).symm
  have hD : (∑ x, p x * ((∑ y, p y * X y) * (∑ y, p y * Y y)))
      = (∑ x, p x) * ((∑ y, p y * X y) * (∑ y, p y * Y y)) :=
    (Finset.sum_mul Finset.univ (fun x => p x) _).symm
  rw [hB, hC, hD, hp]
  ring

/-- **Latent-mixture coordinate moments.** Let `Z` (latent states) and `ι`
(items) be finite, `pi : PMF Z` a latent law with no support restriction,
and `q z i ∈ [0, 1]` item curves (endpoints `0` and `1` allowed). Write
`K z = localIndepPMF (q z) _ _` and observe `Y : ι → Bool` from the mixture
law `pi.bind K` on the full response space. Then, with
`Y_i x = if x i then 1 else 0`:

(1) mixed first moment `E[Y_i] = E_pi[q_i]`;
(2) mixed pair moment `E[Y_i * Y_j] = E_pi[q_i * q_j]` for `i ≠ j`;
(3) observable covariance `Cov(Y_i, Y_j) = Cov_pi(q_i, q_j)` for `i ≠ j`,
where the left covariance is `ProbabilityTheory.covariance` under the
observed law and the right is the finite-sum
`FiniteProbability.covariance` under the weights `(pi z).toReal`.

No diagonal (`i = j`) covariance claim is made. -/
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
    have hX : MemLp (fun x : ι → Bool => (if x i then (1 : ℝ) else 0)) 2
        (pi.bind fun z => localIndepPMF (q z) (hq0 z) (hq1 z)).toMeasure :=
      memLp_indicator _ i
    have hY : MemLp (fun x : ι → Bool => (if x j then (1 : ℝ) else 0)) 2
        (pi.bind fun z => localIndepPMF (q z) (hq0 z) (hq1 z)).toMeasure :=
      memLp_indicator _ j
    rw [ProbabilityTheory.covariance_eq_sub hX hY]
    simp only [Pi.mul_apply]
    rw [finiteCovariance_eq _ _ _ (pmf_sum_toReal_eq_one pi)]
    rw [h1 i, h1 j, h2 i j hij]
    rfl
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
