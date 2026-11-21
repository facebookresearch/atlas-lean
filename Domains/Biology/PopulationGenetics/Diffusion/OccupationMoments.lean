/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Diffusion.PathFunctionals
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Basic.NNReal.Defs
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Probability.Process.Filtration
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Separation.Hausdorff

/-!
# Squared heterozygosity occupation until absorption

Expected sums of a function of gene frequency along sample paths are obtained from the
ordinary differential equation `L{Y(p)} + K(p) = 0`; under the boundary conditions
`Y(0) = Y(1) = 0` the solution is the Green formula. This functional programme is due to
T. Maruyama and M. Kimura, "Moments for Sum of an Arbitrary Function of Gene Frequency
along a Stochastic Path of Gene Frequency Change", Proc. Nat. Acad. Sci. USA 72(4),
1602-1604 (1975). These are the forward (until absorption) statements in diffusion units,
not their retrospective Eq. 21 and not a count in generations or individuals.

Conventions follow `Domains.Biology.PopulationGenetics.Diffusion.WrightFisher`: diploid
population of `N` individuals (`2N` gene copies), diffusion time in units of `2N`
generations, ideal population `N_e = N`, and the neutral backward generator `generator 0`
with coefficient `x (1 - x) / 2` on the second derivative. For the squared heterozygosity
function `g(y) = (2y(1-y))^2`, the potential `u(y) = (2/3) y(1-y)(1+y-y^2)` satisfies
`u(0) = u(1) = 0` and `generator 0 u = -g`, since `u''(y) = -8y(1-y)`; so the Green/Dynkin
value from initial frequency `x` is `(2/3) x(1-x)(1+x-x^2)` in diffusion time units.

This is the expected occupation of the squared heterozygosity integrand, not the second
moment of the accumulated heterozygosity functional; the latter is not claimed here.

## Main results

* `generator_zero_heterozygositySqPotential`: `generator 0` maps the potential
  `u(z) = (2/3) z(1-z)(1+z-z^2)` to `-(2y(1-y))^2`, pointwise in `y`.
* `integral_sq_two_mul_one_sub_absorptionTime`: for any neutral solution started at `x`,
  the stopped squared-heterozygosity integral is integrable and its mean is
  `(2/3) x(1-x)(1+x-x^2)`.
* `integral_sq_two_mul_one_sub_absorptionTime_modifiedProcess`: the same identity for the
  constructed neutral realization `modifiedProcess x` under `rawMeasure x`.

## References

* T. Maruyama and M. Kimura, *Moments for Sum of an Arbitrary Function of Gene Frequency
  along a Stochastic Path of Gene Frequency Change*, Proc. Nat. Acad. Sci. USA 72(4),
  1602-1604 (1975), doi:10.1073/pnas.72.4.1602.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal unitInterval

open MathlibExt.Biology.PopulationGenetics.Diffusion (generator)
open MathlibExt.Biology.PopulationGenetics.Diffusion.KimuraFixationProcess
  (IsWrightFisherSolution absorptionTime)
open MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralWrightFisherRaw
  (modifiedProcess rawMeasure)

namespace MathlibExt.Biology.PopulationGenetics.Diffusion

private theorem hasDerivAt_sqPotential_first (z : ℝ) :
    HasDerivAt (fun z => (2 / 3) * z * (1 - z) * (1 + z - z ^ 2))
      ((2 / 3) * (1 - 6 * z ^ 2 + 4 * z ^ 3)) z := by
  convert ((((hasDerivAt_id' z).const_mul (2 / 3)).mul
    ((hasDerivAt_id' z).const_sub 1)).mul
    (((hasDerivAt_const (c := (1 : ℝ)) (x := z)).add (hasDerivAt_id' z)).sub
      (hasDerivAt_pow 2 z))) using 1
  simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply,
    show (2 - 1 : ℕ) = 1 from rfl]
  ring

private theorem hasDerivAt_sqPotential_second (y : ℝ) :
    HasDerivAt (fun z : ℝ => (2 / 3) * (1 - 6 * z ^ 2 + 4 * z ^ 3))
      (-8 * y * (1 - y)) y := by
  convert (((((hasDerivAt_pow 2 y).const_mul 6).const_sub 1).add
    ((hasDerivAt_pow 3 y).const_mul 4))).const_mul (2 / 3) using 1
  simp only [show (2 - 1 : ℕ) = 1 from rfl, show (3 - 1 : ℕ) = 2 from rfl]
  ring

private theorem contDiff_sqPotential :
    ContDiff ℝ 2 (fun z : ℝ => (2 / 3) * z * (1 - z) * (1 + z - z ^ 2)) :=
  (((contDiff_const.mul contDiff_id).mul
    (contDiff_const.sub contDiff_id)).mul
    ((contDiff_const.add contDiff_id).sub (contDiff_id.pow 2)))

private theorem continuous_sqPotential :
    Continuous fun z : ℝ => (2 / 3) * z * (1 - z) * (1 + z - z ^ 2) :=
  contDiff_sqPotential.continuous

private theorem heteroSq_mem {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    0 ≤ 2 * y * (1 - y) ∧ 2 * y * (1 - y) ≤ 1 / 2 ∧
      (2 * y * (1 - y)) ^ 2 ≤ 2 * y * (1 - y) ∧
      0 ≤ (2 / 3) * y * (1 - y) * (1 + y - y ^ 2) ∧
      |(2 / 3) * y * (1 - y) * (1 + y - y ^ 2)| ≤ 2 * y * (1 - y) := by
  obtain ⟨hy0, hy1⟩ := hy
  have h1 : (0 : ℝ) ≤ 2 * y * (1 - y) :=
    mul_nonneg (mul_nonneg (by norm_num) hy0) (by linarith)
  have h2 : 2 * y * (1 - y) ≤ 1 / 2 := by nlinarith [sq_nonneg (y - 1 / 2)]
  have h3 : (2 * y * (1 - y)) ^ 2 ≤ 2 * y * (1 - y) := by
    nlinarith [mul_nonneg h1 (show (0 : ℝ) ≤ 1 - 2 * y * (1 - y) by linarith)]
  have hs : (0 : ℝ) ≤ 1 + y - y ^ 2 := by
    nlinarith [mul_nonneg hy0 (show (0 : ℝ) ≤ 1 - y by linarith)]
  have h4 : (0 : ℝ) ≤ (2 / 3) * y * (1 - y) * (1 + y - y ^ 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hy0) (by linarith)) hs
  have h5 : |(2 / 3) * y * (1 - y) * (1 + y - y ^ 2)| ≤ 2 * y * (1 - y) := by
    rw [abs_of_nonneg h4]
    nlinarith [mul_nonneg h1 (show (0 : ℝ) ≤ 2 - y + y ^ 2 by
      nlinarith [sq_nonneg (y - 1 / 2)])]
  exact ⟨h1, h2, h3, h4, h5⟩

/-- Neutral generator applied to the squared-heterozygosity potential: for every real `y`
(no restriction to the unit interval),
`generator 0 (fun z => (2/3) z(1-z)(1+z-z^2)) y = -((2y(1-y))^2)`, pointwise in `y`. The
potential vanishes at both endpoints, `u(0) = u(1) = 0`, with `u''(y) = -8y(1-y)`; time is
in diffusion units (multiples of `2N` generations). This is a pointwise
ordinary-differential-equation identity and makes no claim about any process. -/
theorem generator_zero_heterozygositySqPotential (y : ℝ) :
    generator 0 (fun z => (2 / 3) * z * (1 - z) * (1 + z - z ^ 2)) y =
      -((2 * y * (1 - y)) ^ 2) := by
  have hD1 : deriv (fun z : ℝ => (2 / 3) * z * (1 - z) * (1 + z - z ^ 2)) =
      fun z => (2 / 3) * (1 - 6 * z ^ 2 + 4 * z ^ 3) :=
    funext fun z => (hasDerivAt_sqPotential_first z).deriv
  have h2 : HasDerivAt (fun z : ℝ => (2 / 3) * (1 - 6 * z ^ 2 + 4 * z ^ 3))
      (-8 * y * (1 - y)) y :=
    hasDerivAt_sqPotential_second y
  rw [generator, hD1, h2.deriv]
  ring

private theorem measurable_apply {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {sig : ℝ} {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : IsWrightFisherSolution sig ℱ μ X) (t : ℝ≥0) :
    Measurable (X t) :=
  ((hX.2.2.1 t).mono (ℱ.le t)).measurable

private theorem integrable_sqPotential_apply {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℝ≥0 → Ω → ℝ} (hX : IsWrightFisherSolution 0 ℱ μ X) (t : ℝ≥0) :
    Integrable (fun ω => (2 / 3) * X t ω * (1 - X t ω) *
      (1 + X t ω - (X t ω) ^ 2)) μ := by
  have hfm : AEStronglyMeasurable (fun ω => (2 / 3) * X t ω * (1 - X t ω) *
      (1 + X t ω - (X t ω) ^ 2)) μ :=
    (continuous_sqPotential.measurable.comp (measurable_apply hX t)).aestronglyMeasurable
  refine Integrable.of_bound hfm (1 / 2) (ae_of_all _ fun ω => ?_)
  obtain ⟨-, h2, -, -, h5⟩ := heteroSq_mem (hX.1 t ω)
  rw [Real.norm_eq_abs]
  linarith [h5, h2]

private theorem dynkin_sqPotential {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {x : ℝ} {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℝ≥0 → Ω → ℝ} (hX : IsWrightFisherSolution 0 ℱ μ X)
    (hX0 : ∀ᵐ ω ∂μ, X 0 ω = x) (t : ℝ≥0) :
    Integrable (fun ω => ∫ s in (0 : ℝ)..(t : ℝ),
        (2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) ^ 2) μ ∧
      ∫ ω, (∫ s in (0 : ℝ)..(t : ℝ),
        (2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) ^ 2) ∂μ =
        (2 / 3) * x * (1 - x) * (1 + x - x ^ 2) - ∫ ω,
          (2 / 3) * X t ω * (1 - X t ω) * (1 + X t ω - (X t ω) ^ 2) ∂μ := by
  have hDyn := hX.integral_generator contDiff_sqPotential t
  simp only [generator_zero_heterozygositySqPotential, intervalIntegral.integral_neg,
    integral_neg] at hDyn
  have hE0 : ∫ ω, (2 / 3) * X 0 ω * (1 - X 0 ω) * (1 + X 0 ω - (X 0 ω) ^ 2) ∂μ =
      (2 / 3) * x * (1 - x) * (1 + x - x ^ 2) := by
    rw [integral_congr_ae (g := fun _ => (2 / 3) * x * (1 - x) * (1 + x - x ^ 2))
      (hX0.mono fun ω hω => by simp only [hω])]
    simp
  rw [hE0] at hDyn
  refine ⟨?_, ?_⟩
  · simpa using hDyn.1.neg
  · linarith [hDyn.2]

private theorem integral_split_at_absorption_sq {Y : ℝ≥0 → ℝ} (hY : Continuous Y)
    (_hmem : ∀ s, Y s ∈ Icc (0 : ℝ) 1) {τ : ℝ≥0}
    (hafter : ∀ s, τ ≤ s → Y s = 0 ∨ Y s = 1) {k : ℝ} (hk : (τ : ℝ) ≤ k) :
    (∫ s in (0 : ℝ)..k, (2 * Y (Real.toNNReal s) * (1 - Y (Real.toNNReal s))) ^ 2) =
      ∫ s in (0 : ℝ)..(τ : ℝ),
        (2 * Y (Real.toNNReal s) * (1 - Y (Real.toNNReal s))) ^ 2 := by
  have hcont : Continuous fun s : ℝ =>
      (2 * Y (Real.toNNReal s) * (1 - Y (Real.toNNReal s))) ^ 2 :=
    (((continuous_const.mul (hY.comp continuous_real_toNNReal)).mul
      (continuous_const.sub (hY.comp continuous_real_toNNReal))).pow 2)
  have htail : (∫ s in (τ : ℝ)..k,
      (2 * Y (Real.toNNReal s) * (1 - Y (Real.toNNReal s))) ^ 2) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    intro s hs
    rw [uIcc_of_le hk] at hs
    have hτs : τ ≤ Real.toNNReal s := by
      rw [Real.le_toNNReal_iff_coe_le ((τ.2).trans hs.1)]
      exact hs.1
    rcases hafter _ hτs with h0 | h1
    · simp [h0]
    · simp [h1]
  have hsplit : ((∫ s in (0 : ℝ)..(τ : ℝ),
      (2 * Y (Real.toNNReal s) * (1 - Y (Real.toNNReal s))) ^ 2) +
      ∫ s in (τ : ℝ)..k, (2 * Y (Real.toNNReal s) * (1 - Y (Real.toNNReal s))) ^ 2) =
      ∫ s in (0 : ℝ)..k, (2 * Y (Real.toNNReal s) * (1 - Y (Real.toNNReal s))) ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)
  rw [htail, add_zero] at hsplit
  exact hsplit.symm

/-- **Forward squared-heterozygosity functional.** For a solution of the neutral
Wright-Fisher martingale problem started at frequency `x`, the expected squared
heterozygosity accumulated until absorption, in diffusion units (multiples of `2N`
generations), is `(2/3) x(1-x)(1+x-x^2)`. This is a derived corollary of the
Maruyama-Kimura functional machinery with `K = g`, `g(y) = (2y(1-y))^2` and boundary
values `0` at both endpoints, in the repository scaling. It is the occupation of the
squared integrand, not the second moment of the accumulated heterozygosity functional. -/
theorem integral_sq_two_mul_one_sub_absorptionTime {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {x : ℝ} {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℝ≥0 → Ω → ℝ} (hX : IsWrightFisherSolution 0 ℱ μ X)
    (hX0 : ∀ᵐ ω ∂μ, X 0 ω = x) :
    Integrable (fun ω => ∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
        (2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) ^ 2) μ ∧
      ∫ ω, (∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
        (2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) ^ 2) ∂μ
        = (2 / 3) * x * (1 - x) * (1 + x - x ^ 2) := by
  have habs := KimuraFixationProcess.ae_exists_absorbed hX
  have hstay0 := hX.ae_stay_zero
  have hstay1 := hX.ae_stay_one
  have hafter : ∀ᵐ ω ∂μ, ∀ s : ℝ≥0, absorptionTime X ω ≤ s → X s ω = 0 ∨ X s ω = 1 := by
    filter_upwards [habs, hstay0, hstay1] with ω ⟨t₀, ht₀⟩ h0 h1
    have hcl : IsClosed {t | X t ω = 0 ∨ X t ω = 1} :=
      (isClosed_eq (hX.2.1 ω) continuous_const).union (isClosed_eq (hX.2.1 ω) continuous_const)
    have hne : {t | X t ω = 0 ∨ X t ω = 1}.Nonempty := by
      rcases ht₀ with h | h
      · exact ⟨t₀, Or.inl (h t₀ le_rfl)⟩
      · exact ⟨t₀, Or.inr (h t₀ le_rfl)⟩
    have hmem := hcl.csInf_mem hne (OrderBot.bddBelow _)
    intro s hs
    rcases hmem with h | h
    · exact Or.inl (h0 _ s hs h)
    · exact Or.inr (h1 _ s hs h)
  have hτint : Integrable (fun ω => (absorptionTime X ω : ℝ)) μ :=
    (KimuraFixationProcess.integral_absorptionTime hX hX0).1
  have hD : ∀ k : ℕ, Integrable (fun ω => ∫ s in (0 : ℝ)..(k : ℝ),
        (2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) ^ 2) μ ∧
      ∫ ω, (∫ s in (0 : ℝ)..(k : ℝ),
        (2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) ^ 2) ∂μ =
        (2 / 3) * x * (1 - x) * (1 + x - x ^ 2) - ∫ ω,
          (2 / 3) * X (k : ℝ≥0) ω * (1 - X (k : ℝ≥0) ω) *
            (1 + X (k : ℝ≥0) ω - (X (k : ℝ≥0) ω) ^ 2) ∂μ := by
    intro k
    have h := dynkin_sqPotential hX hX0 (k : ℝ≥0)
    simpa only [NNReal.coe_natCast] using h
  have hlim : ∀ᵐ ω ∂μ, Tendsto
      (fun k : ℕ => ∫ s in (0 : ℝ)..(k : ℝ),
        (2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) ^ 2) atTop
      (nhds (∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
        (2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) ^ 2)) := by
    filter_upwards [hafter] with ω hω
    refine (tendsto_congr' ?_).mpr tendsto_const_nhds
    filter_upwards [eventually_ge_atTop ⌈(absorptionTime X ω : ℝ)⌉₊] with k hk
    exact integral_split_at_absorption_sq (hX.2.1 ω) (fun s => hX.1 s ω) hω
      ((Nat.le_ceil _).trans (by exact_mod_cast hk))
  have hball : ∀ᵐ ω ∂μ, ∀ k : ℕ, ‖∫ s in (0 : ℝ)..(k : ℝ),
        (2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) ^ 2‖ ≤
        (absorptionTime X ω : ℝ) := by
    filter_upwards [hafter] with ω hω k
    have hpt : ∀ s : ℝ, ‖(2 * X (Real.toNNReal s) ω *
        (1 - X (Real.toNNReal s) ω)) ^ 2‖ ≤ 1 / 2 := by
      intro s
      obtain ⟨-, h2, h3, -, -⟩ := heteroSq_mem (hX.1 (Real.toNNReal s) ω)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      linarith [h3, h2]
    by_cases hkτ : (k : ℝ) ≤ (absorptionTime X ω : ℝ)
    · refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := (1 / 2 : ℝ)) fun s _ =>
        hpt s).trans ?_
      rw [sub_zero, abs_of_nonneg k.cast_nonneg]
      have hτ0 : (0 : ℝ) ≤ (absorptionTime X ω : ℝ) := NNReal.coe_nonneg _
      linarith [hkτ, hτ0]
    · have hkτ' := lt_of_not_ge hkτ
      have hsplit := integral_split_at_absorption_sq (hX.2.1 ω) (fun s => hX.1 s ω) hω hkτ'.le
      rw [hsplit]
      refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := (1 / 2 : ℝ)) fun s _ =>
        hpt s).trans ?_
      rw [sub_zero, abs_of_nonneg (NNReal.coe_nonneg _)]
      have hτ0 : (0 : ℝ) ≤ (absorptionTime X ω : ℝ) := NNReal.coe_nonneg _
      linarith [hτ0]
  have hbound : ∀ k : ℕ, ∀ᵐ ω ∂μ, ‖∫ s in (0 : ℝ)..(k : ℝ),
        (2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) ^ 2‖ ≤
        (absorptionTime X ω : ℝ) :=
    fun k => hball.mono fun ω hω => hω k
  have hmean : Tendsto (fun k : ℕ => ∫ ω, (∫ s in (0 : ℝ)..(k : ℝ),
        (2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) ^ 2) ∂μ) atTop
      (nhds (∫ ω, (∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
        (2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) ^ 2) ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun ω => (absorptionTime X ω : ℝ))
      (fun k => (hD k).1.aestronglyMeasurable) hτint hbound hlim
  have hptbound : ∀ k : ℕ, ∀ᵐ ω ∂μ,
      ‖(2 / 3) * X (k : ℝ≥0) ω * (1 - X (k : ℝ≥0) ω) *
        (1 + X (k : ℝ≥0) ω - (X (k : ℝ≥0) ω) ^ 2)‖ ≤ 1 / 2 :=
    fun k => ae_of_all _ fun ω => by
      obtain ⟨-, h2, -, -, h5⟩ := heteroSq_mem (hX.1 (k : ℝ≥0) ω)
      rw [Real.norm_eq_abs]
      linarith [h5, h2]
  have hEf0 : Tendsto (fun k : ℕ => ∫ ω, (2 / 3) * X (k : ℝ≥0) ω * (1 - X (k : ℝ≥0) ω) *
      (1 + X (k : ℝ≥0) ω - (X (k : ℝ≥0) ω) ^ 2) ∂μ) atTop (nhds 0) := by
    have h := tendsto_integral_of_dominated_convergence (fun _ => (1 / 2 : ℝ))
      (fun k => (integrable_sqPotential_apply hX (k : ℝ≥0)).aestronglyMeasurable)
      (integrable_const _) hptbound (f := fun _ => (0 : ℝ)) ?_
    · simpa using h
    filter_upwards [habs] with ω ⟨t₀, ht₀⟩
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈(t₀ : ℝ)⌉₊] with k hk
    have hk' : t₀ ≤ (k : ℝ≥0) := by
      rw [← NNReal.coe_le_coe, NNReal.coe_natCast]
      exact (Nat.le_ceil _).trans (by exact_mod_cast hk)
    rcases ht₀ with h | h
    · simp [h _ hk']
    · simp [h _ hk']
  have key : ∀ k : ℕ, (∫ ω, (∫ s in (0 : ℝ)..(k : ℝ),
        (2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) ^ 2) ∂μ) =
        ((2 / 3) * x * (1 - x) * (1 + x - x ^ 2)) - ∫ ω,
          (2 / 3) * X (k : ℝ≥0) ω * (1 - X (k : ℝ≥0) ω) *
            (1 + X (k : ℝ≥0) ω - (X (k : ℝ≥0) ω) ^ 2) ∂μ :=
    fun k => (hD k).2
  have hEq : Tendsto (fun k : ℕ => ∫ ω, (∫ s in (0 : ℝ)..(k : ℝ),
        (2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) ^ 2) ∂μ) atTop
      (nhds ((2 / 3) * x * (1 - x) * (1 + x - x ^ 2))) := by
    have hconst : Tendsto (fun _ : ℕ => (2 / 3) * x * (1 - x) * (1 + x - x ^ 2)) atTop
        (nhds ((2 / 3) * x * (1 - x) * (1 + x - x ^ 2))) :=
      tendsto_const_nhds
    have h : Tendsto
        (fun k : ℕ => (2 / 3) * x * (1 - x) * (1 + x - x ^ 2) - ∫ ω,
          (2 / 3) * X (k : ℝ≥0) ω * (1 - X (k : ℝ≥0) ω) *
            (1 + X (k : ℝ≥0) ω - (X (k : ℝ≥0) ω) ^ 2) ∂μ)
        atTop (nhds ((2 / 3) * x * (1 - x) * (1 + x - x ^ 2) - 0)) :=
      Filter.Tendsto.sub hconst hEf0
    rw [sub_zero] at h
    exact (tendsto_congr' (Eventually.of_forall fun k => key k)).mpr h
  have hval := tendsto_nhds_unique hmean hEq
  have hFm : AEStronglyMeasurable (fun ω =>
      ∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
        (2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) ^ 2) μ := by
    exact aestronglyMeasurable_of_tendsto_ae atTop
      (fun k => (hD k).1.aestronglyMeasurable) hlim
  have hFbound : ∀ᵐ ω ∂μ, ‖∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
      (2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) ^ 2‖ ≤
      (absorptionTime X ω : ℝ) := by
    refine ae_of_all _ fun ω => ?_
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := (1 / 2 : ℝ))
      fun s _ => ?_).trans
      ?_
    · obtain ⟨-, h2, h3, -, -⟩ := heteroSq_mem (hX.1 (Real.toNNReal s) ω)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      linarith [h3, h2]
    · rw [sub_zero, abs_of_nonneg (NNReal.coe_nonneg _)]
      have hτ0 : (0 : ℝ) ≤ (absorptionTime X ω : ℝ) := NNReal.coe_nonneg _
      linarith [hτ0]
  have hFint : Integrable (fun ω => ∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
      (2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) ^ 2) μ :=
    hτint.mono' hFm hFbound
  exact ⟨hFint, hval⟩

/-- **Realization reading.** For every `x : I`, the stopped squared-heterozygosity integral
of the constructed neutral realization `modifiedProcess x` is integrable with respect to
`rawMeasure x`, and its integral equals `(2/3) x(1-x)(1+x-x^2)`. This is the non-vacuity
reading of `integral_sq_two_mul_one_sub_absorptionTime` for the realization identified by
`isWrightFisherSolution_zero_modifiedProcess`. -/
theorem integral_sq_two_mul_one_sub_absorptionTime_modifiedProcess (x : I) :
    Integrable (fun ω => ∫ s in (0 : ℝ)..(absorptionTime (modifiedProcess x) ω : ℝ),
        (2 * modifiedProcess x (Real.toNNReal s) ω *
          (1 - modifiedProcess x (Real.toNNReal s) ω)) ^ 2) (rawMeasure x) ∧
      ∫ ω, (∫ s in (0 : ℝ)..(absorptionTime (modifiedProcess x) ω : ℝ),
        (2 * modifiedProcess x (Real.toNNReal s) ω *
          (1 - modifiedProcess x (Real.toNNReal s) ω)) ^ 2) ∂(rawMeasure x)
        = (2 / 3) * (x : ℝ) * (1 - (x : ℝ)) * (1 + (x : ℝ) - (x : ℝ) ^ 2) := by
  exact integral_sq_two_mul_one_sub_absorptionTime
    (NeutralMartingaleProblem.isWrightFisherSolution_zero_modifiedProcess x)
    (ae_of_all _ fun ω => NeutralWrightFisherRaw.modifiedProcess_zero x ω)

end MathlibExt.Biology.PopulationGenetics.Diffusion
