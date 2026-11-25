/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.MeasureDifferentialPrivacy
public import Mathlib.Probability.Kernel.WithDensity

/-!
# Differential privacy from density bounds

The general density argument for Markov kernels: when every kernel measure is
a density against one common sigma-finite base measure, and the densities
satisfy an almost-everywhere multiplicative bound on ordered adjacent pairs,
then every measurable event obeys the same multiplicative bound. That event
bound is pure differential privacy for the kernel.

`density_kernel_apply` and `density_kernel_isMarkov` build such a kernel from
a constant base kernel and a normalized jointly-measurable density family.
-/

@[expose] public section

namespace CSLibExt.Privacy.DifferentialPrivacy

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Event bound from an almost-everywhere density bound: the `exp ε`
multiplicative bound on densities integrates to the same bound on events. -/
theorem density_event_bound {D Ω : Type*} [MeasurableSpace D] [MeasurableSpace Ω]
    (μ : Measure Ω) [SigmaFinite μ]
    (κ : Kernel D Ω) [IsMarkovKernel κ]
    (ρ : D → Ω → ℝ≥0∞) (adj : D → D → Prop) (ε : ℝ)
    (hf : Measurable (Function.uncurry ρ))
    (hκ : ∀ d, κ d = μ.withDensity (ρ d))
    (_hε : 0 ≤ ε)
    (hbound : ∀ d d', adj d d' →
      ∀ᵐ x ∂μ, ρ d x ≤ ENNReal.ofReal (Real.exp ε) * ρ d' x)
    (d d' : D) (hadj : adj d d') (s : Set Ω) (hs : MeasurableSet s) :
    κ d s ≤ ENNReal.ofReal (Real.exp ε) * κ d' s := by
  rw [hκ d, hκ d']
  calc μ.withDensity (ρ d) s
      ≤ μ.withDensity (fun x => ENNReal.ofReal (Real.exp ε) * ρ d' x) s :=
        Measure.le_iff.mp (withDensity_mono (hbound d d' hadj)) s hs
    _ = ∫⁻ x in s, ENNReal.ofReal (Real.exp ε) * ρ d' x ∂μ :=
        withDensity_apply _ hs
    _ = ENNReal.ofReal (Real.exp ε) * ∫⁻ x in s, ρ d' x ∂μ :=
        lintegral_const_mul _ (hf.of_uncurry_left (x := d'))
    _ = ENNReal.ofReal (Real.exp ε) * μ.withDensity (ρ d') s := by
        rw [withDensity_apply (ρ d') hs]

/-- A kernel with density-form measures and an almost-everywhere density
bound is purely differentially private. -/
theorem isMeasureDP_of_density {D Ω : Type*} [MeasurableSpace D] [MeasurableSpace Ω]
    (μ : Measure Ω) [SigmaFinite μ]
    (κ : Kernel D Ω) [IsMarkovKernel κ]
    (ρ : D → Ω → ℝ≥0∞) (adj : D → D → Prop) (ε : ℝ)
    (hf : Measurable (Function.uncurry ρ))
    (hκ : ∀ d, κ d = μ.withDensity (ρ d))
    (hε : 0 ≤ ε)
    (hbound : ∀ d d', adj d d' →
      ∀ᵐ x ∂μ, ρ d x ≤ ENNReal.ofReal (Real.exp ε) * ρ d' x) :
    IsMeasureDP κ adj ε 0 := by
  rw [isMeasureDP_delta_zero_iff]
  refine ⟨hε, fun d d' hadj s hs => ?_⟩
  exact density_event_bound μ κ ρ adj ε hf hκ hε hbound d d' hadj s hs

/-- A density kernel over a constant base kernel evaluates to the base
measure with the corresponding density. -/
theorem density_kernel_apply {D Ω : Type*} [MeasurableSpace D] [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (ρ : D → Ω → ℝ≥0∞)
    (hf : Measurable (Function.uncurry ρ)) (d : D) :
    Kernel.withDensity (Kernel.const D μ) ρ d = μ.withDensity (ρ d) := by
  rw [Kernel.withDensity_apply _ hf, Kernel.const_apply]

/-- A density kernel over a constant base kernel is Markov when every
density is normalized. -/
theorem density_kernel_isMarkov {D Ω : Type*} [MeasurableSpace D] [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (ρ : D → Ω → ℝ≥0∞)
    (hf : Measurable (Function.uncurry ρ))
    (hnorm : ∀ d, ∫⁻ x, ρ d x ∂μ = 1) :
    IsMarkovKernel (Kernel.withDensity (Kernel.const D μ) ρ) := by
  refine ⟨fun d => ⟨?_⟩⟩
  rw [Kernel.withDensity_apply _ hf d, Kernel.const_apply,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact hnorm d

end CSLibExt.Privacy.DifferentialPrivacy
