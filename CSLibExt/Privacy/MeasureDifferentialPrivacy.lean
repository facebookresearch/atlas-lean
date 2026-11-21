/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.ApproximateDifferentialPrivacy
public import Mathlib.Probability.Kernel.Defs

/-!
# Measure-valued differential privacy for Markov kernels

`IsMeasureDP` is the kernel analogue of `IsApproxDP`: a Markov kernel
satisfies `(ε, δ)`-DP when every measurable event obeys the
`exp ε`-multiplicative plus `δ`-additive bound on ordered adjacent pairs.

`pmfKernel` turns a discrete `D → PMF Ω` mechanism into a Markov kernel,
and `isApproxDP_iff_isMeasureDP` shows the two predicates coincide on
countable discrete spaces. Kernel postprocessing is not covered here.
-/

@[expose] public section

namespace CSLibExt.Privacy.DifferentialPrivacy

/-- Approximate `(ε, δ)`-DP for a Markov kernel: every measurable event
obeys the multiplicative-plus-additive bound on ordered adjacent pairs. -/
def IsMeasureDP {D Ω : Type*} [MeasurableSpace D] [MeasurableSpace Ω]
    (κ : ProbabilityTheory.Kernel D Ω) [ProbabilityTheory.IsMarkovKernel κ]
    (adj : D → D → Prop) (ε δ : ℝ) : Prop :=
  0 ≤ ε ∧ 0 ≤ δ ∧ ∀ d d₂, adj d d₂ → ∀ s : Set Ω, MeasurableSet s →
    κ d s ≤ ENNReal.ofReal (Real.exp ε) * κ d₂ s + ENNReal.ofReal δ

/-- With `δ = 0`, kernel DP is the pure multiplicative event bound. -/
theorem isMeasureDP_delta_zero_iff {D Ω : Type*} [MeasurableSpace D]
    [MeasurableSpace Ω] {κ : ProbabilityTheory.Kernel D Ω}
    [ProbabilityTheory.IsMarkovKernel κ] {adj : D → D → Prop} {ε : ℝ} :
    IsMeasureDP κ adj ε 0 ↔
      0 ≤ ε ∧ ∀ d d₂, adj d d₂ → ∀ s : Set Ω, MeasurableSet s →
        κ d s ≤ ENNReal.ofReal (Real.exp ε) * κ d₂ s := by
  simp only [IsMeasureDP, ENNReal.ofReal_zero, add_zero, le_refl, true_and]

/-- A discrete mechanism as a Markov kernel via `PMF.toMeasure`.
Every function out of a countable space with measurable singletons is
measurable, which supplies the kernel measurability proof. -/
noncomputable def pmfKernel {D Ω : Type*} [MeasurableSpace D]
    [MeasurableSpace Ω] [Countable D] [MeasurableSingletonClass D]
    (M : D → PMF Ω) : ProbabilityTheory.Kernel D Ω :=
  ProbabilityTheory.Kernel.mk (fun d => (M d).toMeasure)
    (measurable_of_countable _)

instance {D Ω : Type*} [MeasurableSpace D] [MeasurableSpace Ω]
    [Countable D] [MeasurableSingletonClass D] (M : D → PMF Ω) :
    ProbabilityTheory.IsMarkovKernel (pmfKernel M) where
  isProbabilityMeasure _ := PMF.toMeasure.isProbabilityMeasure _

@[simp]
theorem pmfKernel_apply {D Ω : Type*} [MeasurableSpace D]
    [MeasurableSpace Ω] [Countable D] [MeasurableSingletonClass D]
    (M : D → PMF Ω) (d : D) : (pmfKernel M) d = (M d).toMeasure := rfl

/-- On countable discrete spaces, event-level approximate DP and kernel DP
coincide. `DiscreteMeasurableSpace Ω` is derived, not assumed: it comes
from `Countable Ω` plus `MeasurableSingletonClass Ω` via
`MeasurableSingletonClass.toDiscreteMeasurableSpace`. -/
theorem isApproxDP_iff_isMeasureDP {D Ω : Type*} [MeasurableSpace D]
    [MeasurableSpace Ω] [Countable D] [MeasurableSingletonClass D]
    [Countable Ω] [MeasurableSingletonClass Ω]
    {M : D → PMF Ω} {adj : D → D → Prop} {ε δ : ℝ} :
    IsApproxDP M adj ε δ ↔ IsMeasureDP (pmfKernel M) adj ε δ := by
  constructor
  · rintro ⟨hε, hδ, h⟩
    refine ⟨hε, hδ, fun d d₂ hadj s _ => ?_⟩
    simp only [pmfKernel_apply, PMF.toMeasure_apply_eq_toOuterMeasure]
    exact h d d₂ hadj s
  · rintro ⟨hε, hδ, h⟩
    refine ⟨hε, hδ, fun d d₂ hadj s => ?_⟩
    have h' := h d d₂ hadj s MeasurableSet.of_discrete
    simp only [pmfKernel_apply, PMF.toMeasure_apply_eq_toOuterMeasure] at h'
    exact h'

/-- A database-independent PMF mechanism is private with zero budgets. -/
theorem isApproxDP_const {D A : Type*} (p : PMF A)
    (adj : D → D → Prop) : IsApproxDP (fun _ => p) adj 0 0 :=
  isApproxDP_zero_iff.mpr (isDP_const p adj)

/-- A database-independent PMF mechanism is kernel-private with zero budgets. -/
theorem isMeasureDP_const {D Ω : Type*} [MeasurableSpace D]
    [MeasurableSpace Ω] [Countable D] [MeasurableSingletonClass D]
    [Countable Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) (adj : D → D → Prop) :
    IsMeasureDP (pmfKernel fun _ => p) adj 0 0 :=
  isApproxDP_iff_isMeasureDP.mp (isApproxDP_const p adj)

end CSLibExt.Privacy.DifferentialPrivacy
