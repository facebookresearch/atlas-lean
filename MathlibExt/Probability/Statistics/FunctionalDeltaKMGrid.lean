/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.FunctionalDelta
public import MathlibExt.Probability.Statistics.Slutsky
public import MathlibExt.Probability.Statistics.Survival.ProcessInference
public import Mathlib.MeasureTheory.Measure.Stieltjes

/-!
# Fixed-grid Kaplan–Meier weak limit and Wald-band coverage

Consumers of `tendstoInDistribution_kmSurvival_grid_of_nelsonAalen` on a fixed grid
`t : Fin k → ℝ` with a cadlag cumulative hazard `A : StieltjesFunction ℝ`.

## Main results

* `tendstoInDistribution_kmSurvival_fixedGrid`: from the Nelson–Aalen CLT
  `√n (Λ̂ₙ - A ∘ t) ⇒ G`, the Kaplan–Meier estimate satisfies
  `√n (Ŝₙ - S) ⇒ -duhamelDeriv (-Δ(A ∘ t)) (ΔG)` with `S = prodIntegral (-Δ(A ∘ t))`.
* `tendstoInDistribution_kmSurvival_fixedGrid_studentized`: with standard-error estimates
  converging in probability to a vector with no zero coordinate, the coordinatewise studentized
  vector converges in distribution (Slutsky).
* `tendsto_kmSurvival_fixedGrid_waldCoverage`: the coverage probability of the simultaneous Wald
  band `ProcessInference.gridBand Ŝₙ (sehat n / √n) z` converges to the limit rectangle
  probability, provided the rectangle faces are null for the limit.

## Scope

Fixed grid only: the grid does not depend on `n`, and continuous-time Kaplan–Meier is out of
scope. No band is defined here; the coverage statement uses the existing
`ProcessInference.gridBand`. Unlike `ProcessInference.tendsto_coverage_gridBand`, which assumes
the finite-grid limit and Gaussian marginals, the limit here is derived from the Nelson–Aalen CLT
and only face-nullity is assumed. In the Gaussian case the test file applies
`ProcessInference.tendsto_coverage_gridBand` directly.
-/

@[expose] public section

open MeasureTheory Filter Topology Finset
open MathlibExt.Probability.Statistics.KaplanMeier
open scoped ENNReal

namespace MathlibExt.Probability.Statistics.FunctionalDelta

/-- **Kaplan–Meier weak limit on a fixed grid, explicit grid and cadlag binders.** The data sets
`Dn n ω` all use the fixed grid `t` (`htime`), and the true cumulative hazard is the grid
restriction `j ↦ A (t j)` of a monotone right-continuous function `A`. If the Nelson–Aalen
estimates at the grid satisfy `√n (Λ̂ₙ - A ∘ t) ⇒ G`, then
`√n (Ŝₙ - S) ⇒ -duhamelDeriv (-Δ(A ∘ t)) (ΔG)` with `S = prodIntegral (-Δ(A ∘ t))`. -/
theorem tendstoInDistribution_kmSurvival_fixedGrid {k : ℕ} {Ω Ω' : Type*}
    {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω} {μ' : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (t : Fin k → ℝ) (A : StieltjesFunction ℝ) {Dn : ℕ → Ω → CensoredData k}
    (htime : ∀ n ω, (Dn n ω).time = t) {G : Ω' → Fin k → ℝ}
    (hCLT : TendstoInDistribution
      (fun (n : ℕ) ω ↦ √(n : ℝ) • ((fun j ↦ (Dn n ω).nelsonAalen (t j)) - fun j ↦ A (t j)))
      atTop G (fun _ ↦ μ) μ') :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ √(n : ℝ) •
        ((fun j ↦ (Dn n ω).kmSurvival (t j)) - prodIntegral (-gridIncrements fun i ↦ A (t i))))
      atTop (fun ω ↦ -duhamelDeriv (-gridIncrements fun i ↦ A (t i)) (gridIncrements (G ω)))
      (fun _ ↦ μ) μ' := by
  have hCLT' : TendstoInDistribution
      (fun (n : ℕ) ω ↦ √(n : ℝ) •
        ((fun j ↦ (Dn n ω).nelsonAalen ((Dn n ω).time j)) - fun j ↦ A (t j)))
      atTop G (fun _ ↦ μ) μ' := by
    simpa only [htime] using hCLT
  have h := tendstoInDistribution_kmSurvival_grid_of_nelsonAalen
    (Λ := fun j ↦ A (t j)) hCLT'
  simpa only [htime] using h

/-- **Studentized fixed-grid Kaplan–Meier limit (Slutsky).** Under the hypotheses of
`tendstoInDistribution_kmSurvival_fixedGrid`, if standard-error estimates `sehat n` converge in
probability to a vector `se` with no zero coordinate, then the coordinatewise studentized vector
`√n (Ŝₙ j - S j) / sehat n j` converges in distribution to `H j / se j`, where `H` is the
Kaplan–Meier limit. -/
theorem tendstoInDistribution_kmSurvival_fixedGrid_studentized {k : ℕ} {Ω Ω' : Type*}
    {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω} {μ' : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (t : Fin k → ℝ) (A : StieltjesFunction ℝ) {Dn : ℕ → Ω → CensoredData k}
    (htime : ∀ n ω, (Dn n ω).time = t) {G : Ω' → Fin k → ℝ}
    (hCLT : TendstoInDistribution
      (fun (n : ℕ) ω ↦ √(n : ℝ) • ((fun j ↦ (Dn n ω).nelsonAalen (t j)) - fun j ↦ A (t j)))
      atTop G (fun _ ↦ μ) μ')
    {se : Fin k → ℝ} (hse : ∀ j, se j ≠ 0) {sehat : ℕ → Ω → Fin k → ℝ}
    (hsehat : TendstoInMeasure μ sehat atTop (fun _ ↦ se))
    (hsehat_meas : ∀ n, AEMeasurable (sehat n) μ) :
    TendstoInDistribution
      (fun (n : ℕ) ω j ↦ √(n : ℝ) *
        ((Dn n ω).kmSurvival (t j) - prodIntegral (-gridIncrements fun i ↦ A (t i)) j) /
          sehat n ω j)
      atTop
      (fun ω j ↦ -duhamelDeriv (-gridIncrements fun i ↦ A (t i)) (gridIncrements (G ω)) j / se j)
      (fun _ ↦ μ) μ' := by
  have hKM := tendstoInDistribution_kmSurvival_fixedGrid t A htime hCLT
  have hinv : TendstoInMeasure μ (fun (n : ℕ) ω j ↦ (sehat n ω j)⁻¹) atTop
      (fun _ j ↦ (se j)⁻¹) := by
    have hcont : ContinuousAt (fun s : Fin k → ℝ ↦ fun j ↦ (s j)⁻¹) se :=
      continuousAt_pi.mpr fun j ↦ (continuous_apply j).continuousAt.inv₀ (hse j)
    exact TendstoInMeasure.comp_const_of_continuousAt hcont hsehat
  have hinv_meas : ∀ n, AEMeasurable (fun ω j ↦ (sehat n ω j)⁻¹) μ :=
    fun n ↦ (hsehat_meas n).inv
  have hmul := hKM.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : (Fin k → ℝ) × (Fin k → ℝ) ↦ fun j ↦ p.1 j * p.2 j) (by fun_prop)
    hinv hinv_meas
  refine hmul.congr (fun n ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun ω ↦ ?_)
  · funext j
    simp [div_eq_mul_inv, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  · funext j
    simp [div_eq_mul_inv]

/-- The closed simultaneous studentized region `{(x, s) | ∀ j, |x j| ≤ z * s j}`.
(Copy of the `private` `ProcessInference` helper, which this slot may not expose.) -/
private def kmGrid_bandRegion (ι : Type*) (z : ℝ) : Set ((ι → ℝ) × (ι → ℝ)) :=
  {p | ∀ j, |p.1 j| ≤ z * p.2 j}

private theorem kmGrid_isClosed_bandRegion (ι : Type*) (z : ℝ) :
    IsClosed (kmGrid_bandRegion ι z) := by
  rw [kmGrid_bandRegion, Set.ofPred_forall]
  exact isClosed_iInter fun j ↦ isClosed_le (by fun_prop) (by fun_prop)

private theorem kmGrid_measurableSet_bandRegion (ι : Type*) [Countable ι] (z : ℝ) :
    MeasurableSet (kmGrid_bandRegion ι z) := by
  rw [kmGrid_bandRegion, Set.ofPred_forall]
  exact MeasurableSet.iInter fun j ↦ measurableSet_le (by fun_prop) (by fun_prop)

private theorem kmGrid_frontier_bandRegion_subset (ι : Type*) [Finite ι] (z : ℝ) :
    frontier (kmGrid_bandRegion ι z) ⊆ ⋃ j, {p : (ι → ℝ) × (ι → ℝ) | |p.1 j| = z * p.2 j} := by
  intro p hp
  have hcl : p ∈ kmGrid_bandRegion ι z := (kmGrid_isClosed_bandRegion ι z).frontier_subset hp
  have hopen : IsOpen {q : (ι → ℝ) × (ι → ℝ) | ∀ j, |q.1 j| < z * q.2 j} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun j ↦ isOpen_lt (by fun_prop) (by fun_prop)
  have hnot : ¬ ∀ j, |p.1 j| < z * p.2 j := fun h ↦
    hp.2 (interior_maximal (show {q : (ι → ℝ) × (ι → ℝ) | ∀ j, |q.1 j| < z * q.2 j} ⊆
      kmGrid_bandRegion ι z from fun q hq j ↦ (hq j).le) hopen h)
  simp only [not_forall, not_lt] at hnot
  obtain ⟨j, hj⟩ := hnot
  exact Set.mem_iUnion.2 ⟨j, le_antisymm (hcl j) hj⟩

/-- **Asymptotic coverage of fixed-grid Kaplan–Meier Wald bands.** Under the hypotheses of
`tendstoInDistribution_kmSurvival_fixedGrid`, with standard-error estimates `sehat n → se` in
probability, the probability that the existing Atlas grid band
`ProcessInference.gridBand Ŝₙ (sehat n / √n) z` contains the whole grid survival vector `S`
converges to the limit rectangle probability `P(∀ j, |H j| ≤ z * se j)`, where `H` is the
Kaplan–Meier limit, provided every rectangle face is null for `H` (`hnull`). Unlike
`ProcessInference.tendsto_coverage_gridBand`, the limit `H` is the Kaplan–Meier Duhamel image
of an arbitrary Nelson–Aalen limit `G` (no Gaussian marginals assumed) and `se` is arbitrary. -/
theorem tendsto_kmSurvival_fixedGrid_waldCoverage {k : ℕ} {Ω Ω' : Type*}
    {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω} {μ' : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (t : Fin k → ℝ) (A : StieltjesFunction ℝ) {Dn : ℕ → Ω → CensoredData k}
    (htime : ∀ n ω, (Dn n ω).time = t) {G : Ω' → Fin k → ℝ}
    (hCLT : TendstoInDistribution
      (fun (n : ℕ) ω ↦ √(n : ℝ) • ((fun j ↦ (Dn n ω).nelsonAalen (t j)) - fun j ↦ A (t j)))
      atTop G (fun _ ↦ μ) μ')
    {se : Fin k → ℝ} {sehat : ℕ → Ω → Fin k → ℝ}
    (hsehat : TendstoInMeasure μ sehat atTop (fun _ ↦ se))
    (hsehat_meas : ∀ n, AEMeasurable (sehat n) μ) (z : ℝ)
    (hnull : ∀ j, μ' {ω | |(-duhamelDeriv (-gridIncrements fun i ↦ A (t i))
      (gridIncrements (G ω))) j| = z * se j} = 0) :
    Tendsto (fun n : ℕ ↦ μ.real {ω | prodIntegral (-gridIncrements fun i ↦ A (t i)) ∈
        ProcessInference.gridBand (fun j ↦ (Dn n ω).kmSurvival (t j))
          (fun j ↦ sehat n ω j / √(n : ℝ)) z})
      atTop (𝓝 (μ'.real {ω | ∀ j, |(-duhamelDeriv (-gridIncrements fun i ↦ A (t i))
        (gridIncrements (G ω))) j| ≤ z * se j})) := by
  have hKM := tendstoInDistribution_kmSurvival_fixedGrid t A htime hCLT
  have hpair := hKM.prodMk_of_tendstoInMeasure_const _ sehat _ hsehat hsehat_meas
  have hnull' : μ'.map (fun ω ↦ (-duhamelDeriv (-gridIncrements fun i ↦ A (t i))
      (gridIncrements (G ω)), se)) (frontier (kmGrid_bandRegion (Fin k) z)) = 0 := by
    refine measure_mono_null (kmGrid_frontier_bandRegion_subset (Fin k) z)
      (measure_iUnion_null fun j ↦ ?_)
    rw [Measure.map_apply_of_aemeasurable (hKM.aemeasurable_limit.prodMk aemeasurable_const)
      (measurableSet_eq_fun (by fun_prop) (by fun_prop))]
    exact hnull j
  have hport := ProcessInference.tendsto_measureReal_preimage_of_tendstoInDistribution hpair
    (kmGrid_measurableSet_bandRegion (Fin k) z) hnull'
  refine hport.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  congr 1
  ext ω
  exact forall_congr' fun j ↦ (ProcessInference.mem_waldInterval_div_sqrt_iff hn).symm

end MathlibExt.Probability.Statistics.FunctionalDelta

end
