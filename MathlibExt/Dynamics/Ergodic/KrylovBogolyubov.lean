/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

section
open MeasureTheory

namespace MathlibExt.Dynamics.Ergodic.KrylovBogolyubovWanted

/-!
# Krylov–Bogolyubov theorem

Invariant Borel probability measures for continuous self-maps of compact
metric spaces.
-/

/-- Cesàro average of Dirac masses along the forward orbit of `x₀` under `T`. -/
private noncomputable def kbAvg
    {X : Type*} [MeasurableSpace X] (T : X → X) (x₀ : X) (n : ℕ) : Measure X :=
  ((n + 1 : ℕ) : ENNReal)⁻¹ • ∑ k ∈ Finset.range (n + 1), Measure.dirac (T^[k] x₀)

/-- Each Cesàro average is a probability measure. -/
private theorem kbAvg_isProb
    {X : Type*} [MeasurableSpace X] (T : X → X) (x₀ : X) (n : ℕ) :
    IsProbabilityMeasure (kbAvg T x₀ n) := by
  have h1 : ∀ k, Measure.dirac (T^[k] x₀) Set.univ = 1 := fun k ↦
    IsProbabilityMeasure.measure_univ
  have hS : (∑ k ∈ Finset.range (n + 1), Measure.dirac (T^[k] x₀)) Set.univ
      = ((n + 1 : ℕ) : ENNReal) := by
    rw [Measure.coe_finsetSum, Finset.sum_apply]
    simp only [h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hne : ((n + 1 : ℕ) : ENNReal) ≠ 0 := by positivity
  have htop : ((n + 1 : ℕ) : ENNReal) ≠ ⊤ := by simp
  rw [isProbabilityMeasure_iff, kbAvg, Measure.smul_apply, hS, smul_eq_mul,
    ENNReal.inv_mul_cancel hne htop]

/-- Integral of a bounded continuous function against a Cesàro average. -/
private theorem kbAvg_integral
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    (T : X → X) (x₀ : X) (n : ℕ) (f : BoundedContinuousFunction X ℝ) :
    ∫ x, f x ∂(kbAvg T x₀ n)
      = (((n + 1 : ℕ) : ℝ)⁻¹) * ∑ k ∈ Finset.range (n + 1), f (T^[k] x₀) := by
  have hcast : (((n + 1 : ℕ) : ENNReal)).toReal = ((n + 1 : ℕ) : ℝ) :=
    ENNReal.toReal_natCast _
  rw [kbAvg, integral_smul_measure,
    integral_finsetSum_measure (fun k _ ↦ f.integrable _),
    ENNReal.toReal_inv, hcast]
  simp only [integral_dirac, smul_eq_mul]

/-- The invariance defect of a Cesàro average telescopes to boundary terms. -/
private theorem kbAvg_diff
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    (T : X → X) (hT : Continuous T) (x₀ : X) (n : ℕ) (f : BoundedContinuousFunction X ℝ) :
    (∫ x, (f.compContinuous ⟨T, hT⟩) x ∂(kbAvg T x₀ n))
      - (∫ x, f x ∂(kbAvg T x₀ n))
      = (((n + 1 : ℕ) : ℝ)⁻¹) * (f (T^[n + 1] x₀) - f x₀) := by
  have hshift : ∀ k, (f.compContinuous ⟨T, hT⟩) (T^[k] x₀) = f (T^[k + 1] x₀) := by
    intro k
    change f (T (T^[k] x₀)) = _
    rw [Function.iterate_succ_apply']
  have hshift_sum : (∑ k ∈ Finset.range (n + 1), (f.compContinuous ⟨T, hT⟩) (T^[k] x₀))
      = ∑ k ∈ Finset.range (n + 1), f (T^[k + 1] x₀) :=
    Finset.sum_congr rfl (fun k _ ↦ hshift k)
  have htele : (∑ k ∈ Finset.range (n + 1), f (T^[k + 1] x₀))
      - (∑ k ∈ Finset.range (n + 1), f (T^[k] x₀))
      = f (T^[n + 1] x₀) - f x₀ := by
    rw [← Finset.sum_sub_distrib]
    have h := Finset.sum_range_sub (fun k ↦ f (T^[k] x₀)) (n + 1)
    simpa [Function.iterate_zero_apply] using h
  rw [kbAvg_integral T x₀ n (f.compContinuous ⟨T, hT⟩), kbAvg_integral T x₀ n f,
    hshift_sum, ← mul_sub, htele]

/--
**Krylov–Bogolyubov theorem.** Every continuous map $T : X \to X$ of a nonempty compact metric
space $X$ to itself has an invariant Borel probability measure: there is a probability measure
$\mu$ on the Borel $\sigma$-algebra of $X$ whose pushforward under $T$ equals $\mu$.

Proves `Wanted` entry `krylov_bogolyubov`.

Source: N. M. Krylov and N. N. Bogolyubov, Ann. Math. 38 (1937), 65-113, DOI 10.2307/1968511.
-/
theorem krylov_bogolyubov
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    {T : X → X} (hT : Continuous T) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧ Measure.map T μ = μ := by
  obtain ⟨x₀⟩ := ‹Nonempty X›
  obtain ⟨μ, φ, hφmono, hφlim⟩ := CompactSpace.tendsto_subseq
    (X := ProbabilityMeasure X)
    (fun n : ℕ ↦ (⟨kbAvg T x₀ n, kbAvg_isProb T x₀ n⟩ : ProbabilityMeasure X))
  refine ⟨(μ : Measure X), inferInstance, ?_⟩
  have hTmeas : Measurable T := hT.measurable
  have key : (⟨Measure.map T (μ : Measure X), inferInstance⟩ : FiniteMeasure X)
      = ⟨(μ : Measure X), inferInstance⟩ := by
    apply FiniteMeasure.ext_of_forall_integral_eq
    intro f
    have hpt : ∀ y, (f.compContinuous ⟨T, hT⟩) y = f (T y) := fun y ↦ rfl
    have hmap : ∫ x, f x ∂(Measure.map T (μ : Measure X))
        = ∫ x, (f.compContinuous ⟨T, hT⟩) x ∂(μ : Measure X) := by
      have e : ∫ x, f x ∂(Measure.map T (μ : Measure X))
          = ∫ x, f (T x) ∂(μ : Measure X) :=
        integral_map hTmeas.aemeasurable f.continuous.aestronglyMeasurable
      exact e.trans (integral_congr_ae (ae_of_all _ fun x ↦ (hpt x).symm))
    have hlim_f : Filter.Tendsto (fun j ↦ ∫ x, f x ∂(kbAvg T x₀ (φ j))) Filter.atTop
        (nhds (∫ x, f x ∂(μ : Measure X))) :=
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hφlim) f
    have hlim_g : Filter.Tendsto
        (fun j ↦ ∫ x, (f.compContinuous ⟨T, hT⟩) x ∂(kbAvg T x₀ (φ j))) Filter.atTop
        (nhds (∫ x, (f.compContinuous ⟨T, hT⟩) x ∂(μ : Measure X))) :=
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hφlim)
        (f.compContinuous ⟨T, hT⟩)
    have hform : ∀ n, (∫ x, (f.compContinuous ⟨T, hT⟩) x ∂(kbAvg T x₀ n))
        - (∫ x, f x ∂(kbAvg T x₀ n))
        = ((((n : ℝ) + 1))⁻¹) * (f (T^[n + 1] x₀) - f x₀) := by
      intro n
      simpa [Nat.cast_add, Nat.cast_one] using kbAvg_diff T hT x₀ n f
    have hbdd : ∀ n, ‖(∫ x, (f.compContinuous ⟨T, hT⟩) x ∂(kbAvg T x₀ n))
        - (∫ x, f x ∂(kbAvg T x₀ n))‖ ≤ ((n : ℝ) + 1)⁻¹ * (2 * ‖f‖) := by
      intro n
      rw [hform n, norm_mul, Real.norm_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc ‖f (T^[n + 1] x₀) - f x₀‖ ≤ ‖f (T^[n + 1] x₀)‖ + ‖f x₀‖ :=
            norm_sub_le _ _
        _ ≤ ‖f‖ + ‖f‖ := add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _)
        _ = 2 * ‖f‖ := by ring
    have hlim0 : Filter.Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹ * (2 * ‖f‖))
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) := by
        have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        simpa [one_div] using h
      have hconst : Filter.Tendsto (fun _ : ℕ ↦ (2 * ‖f‖)) Filter.atTop
          (nhds (2 * ‖f‖)) := tendsto_const_nhds
      have h2 := h1.mul hconst
      simpa using h2
    have hfull : Filter.Tendsto (fun n ↦ (∫ x, (f.compContinuous ⟨T, hT⟩) x ∂(kbAvg T x₀ n))
        - (∫ x, f x ∂(kbAvg T x₀ n))) Filter.atTop (nhds 0) :=
      squeeze_zero_norm hbdd hlim0
    have hzero : Filter.Tendsto (fun j ↦ (∫ x, (f.compContinuous ⟨T, hT⟩) x ∂(kbAvg T x₀ (φ j)))
        - (∫ x, f x ∂(kbAvg T x₀ (φ j)))) Filter.atTop (nhds 0) :=
      hfull.comp hφmono.tendsto_atTop
    have heq := tendsto_nhds_unique (hlim_g.sub hlim_f) hzero
    change (∫ x, f x ∂(Measure.map T (μ : Measure X)))
      = (∫ x, f x ∂(μ : Measure X))
    rw [hmap]
    exact sub_eq_zero.mp heq
  exact congrArg (fun ν : FiniteMeasure X ↦ (ν : Measure X)) key

end MathlibExt.Dynamics.Ergodic.KrylovBogolyubovWanted
